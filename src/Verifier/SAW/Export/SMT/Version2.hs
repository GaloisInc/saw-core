{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Verifier.SAW.Export.SMT.Version2 
  ( WriterState
  , emptyWriterState
  , render
  , warnings
  , Warning(..)
  , SMT.Name
    -- * Writer
  , Writer
  , assert
  , checkSat
    -- * Matching rules for trnslation
  , Rule
  , RuleSet
  , typeRule
  , exprRule
    -- * Predefined rules
  , coreRules
  , bitvectorRules
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Bits
import Data.Monoid
import qualified Data.Map as Map

import qualified SMTLib2 as SMT
import qualified SMTLib2.Array as SMT
import qualified SMTLib2.BitVector as SMT
import qualified SMTLib2.Core as SMT

import Verifier.SAW.Export.SMT.Common
import Verifier.SAW.Conversion
import Verifier.SAW.Rewriter ()
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.TermNet as Net

data Warning t
  = UnmatchedType SMT.Name t
  | UnmatchedTerm SMT.Name t

data WriterState s =
     WriterState { smtContext :: SharedContext s
                 , smtTheory :: !SMT.Name
                 -- Maps terms representing types already seen to expression.
                 , smtTypeNet :: Net.Net (Rule s SMT.Type)
                 , _smtTypeCache :: !(Map.Map TermIndex SMT.Type)
                 , _smtTypeNonce :: !Int
                 -- Maps terms already seen to expression.
                 , smtExprNet :: Net.Net (Rule s SMT.Expr)
                 , _smtExprCache :: !(Map.Map TermIndex SMT.Expr)
                 , _smtExprNonce :: !Int
                 , _smtDefs  :: [SMT.Command]
                 , _smtCommands :: [SMT.Command]
                 , _smtWarnings :: [Warning (SharedTerm s)]
                 }

emptyWriterState :: SharedContext s
                 -> SMT.Name -- ^ Name of theory
                 -> RuleSet s
                 -> WriterState s
emptyWriterState ctx theory (RuleSet typeRules exprRules) =
     WriterState { smtContext = ctx
                 , smtTheory = theory
                 , smtTypeNet = foldr addRule Net.empty typeRules
                 , _smtTypeCache = Map.empty
                 , _smtTypeNonce = 0
                 , smtExprNet = foldr addRule Net.empty exprRules
                 , _smtExprCache = Map.empty
                  , _smtExprNonce = 0
                 , _smtDefs = []
                 , _smtCommands = []
                 , _smtWarnings = []
                 }
  where addRule rule = Net.insert_term (rule, rule)

smtTypeCache :: Simple Lens (WriterState s) (Map.Map TermIndex SMT.Type)
smtTypeCache = lens _smtTypeCache (\s v -> s { _smtTypeCache = v })

smtTypeNonce :: Simple Lens (WriterState s) Int
smtTypeNonce = lens _smtTypeNonce (\s v -> s { _smtTypeNonce = v })

smtExprCache :: Simple Lens (WriterState s) (Map.Map TermIndex SMT.Expr)
smtExprCache = lens _smtExprCache (\s v -> s { _smtExprCache = v })

smtExprNonce :: Simple Lens (WriterState s) Int
smtExprNonce = lens _smtExprNonce (\s v -> s { _smtExprNonce = v })

smtDefs :: Simple Lens (WriterState s) [SMT.Command]
smtDefs = lens _smtDefs (\s v -> s { _smtDefs = v })

smtCommands :: Simple Lens (WriterState s) [SMT.Command]
smtCommands = lens _smtCommands (\s v -> s { _smtCommands = v })

smtWarnings :: Simple Lens (WriterState s) [Warning (SharedTerm s)]
smtWarnings = lens _smtWarnings (\s v -> s { _smtWarnings = v })

warnings :: WriterState s -> [Warning (SharedTerm s)]
warnings = view smtWarnings 

render :: WriterState s -> String
render s = show $ SMT.pp $ SMT.Script $ 
  [ SMT.CmdSetLogic (smtTheory s) ]
  ++ reverse (s^.smtDefs)
  ++ reverse (s^.smtCommands) 

type Writer s = StateT (WriterState s) IO

toSMTType :: SharedTerm s -> Writer s SMT.Type
toSMTType t@(STApp i _tf) = do
  cache smtTypeCache i $ do
    mres <- matchTerm smtTypeNet t
    case mres of
      Just r -> return r
      Nothing -> do
        -- Create name for fresh type.
        nm <- freshName smtTypeNonce "tp"
        -- Add warning for unmatched type.
        smtWarnings %= (UnmatchedType nm t:)
        return (SMT.TVar nm)

toSMTExpr :: SharedTerm s -> Writer s SMT.Expr
toSMTExpr t@(STApp i _tf) = do
  cache smtExprCache i $ do
    -- Get type of term
    tp <- do sc <- gets smtContext
             toSMTType =<< liftIO (scTypeOf sc t)
    -- Create name for fresh variable
    nm <- freshName smtExprNonce "x"
    -- Try matching term to get SMT definition.
    mdefExpr <- matchTerm smtExprNet t 
    case mdefExpr of
      Just defExpr -> do -- Define function if we can.
        smtDefs %= (SMT.CmdDefineFun nm [] tp defExpr:)
      -- Introduce fresh variable.
      Nothing -> do
        smtDefs %= (SMT.CmdDeclareFun nm [] tp:)
        smtWarnings %= (UnmatchedTerm nm t:)
    return $ SMT.App (SMT.I nm []) (Just tp) []

asSMTType :: Rule s SMT.Type
asSMTType = asVar (lift . toSMTType)

asSMTExpr :: Rule s SMT.Expr
asSMTExpr = asVar (lift . toSMTExpr)

assert :: SharedTerm s -> Writer s ()
assert t = do
  e <- toSMTExpr t
  smtCommands %= (SMT.CmdAssert e:)

checkSat :: Writer s ()
checkSat = smtCommands %= (SMT.CmdCheckSat:)

type Rule s = Matcher (MaybeT (Writer s)) (SharedTerm s)

-- HACK!
instance Eq (Rule s r) where
  x == y = Net.toPat x == Net.toPat y

data RuleSet s = RuleSet [Rule s SMT.Type] [Rule s SMT.Expr]

typeRule :: Rule s SMT.Type -> RuleSet s
typeRule r = RuleSet [r] []

exprRule :: Rule s SMT.Expr -> RuleSet s
exprRule r = RuleSet [] [r]

instance Monoid (RuleSet s) where
  mempty = RuleSet [] []
  mappend (RuleSet tx ex) (RuleSet ty ey) = RuleSet (tx ++ ty) (ex ++ ey)

instance Matchable (MaybeT (Writer s)) (SharedTerm s) SMT.Type where
  defaultMatcher = asSMTType

instance Matchable (MaybeT (Writer s)) (SharedTerm s) SMT.Expr where
  defaultMatcher = asSMTExpr

-- Types supported:

-- Bool.
-- Tuples, Records?

-- Either? Maybe?
-- Nat? Fin?
-- Vec?
-- bitvector
-- Float? Double?

-- | SMT Rules for core theory.
coreRules :: RuleSet s
coreRules
  =  typeRule boolTypeRule
  <> exprRule trueExprRule
  <> exprRule falseExprRule
  <> exprRule notExprRule
  <> exprRule andExprRule
  <> exprRule orExprRule
  <> exprRule xorExprRule
  <> exprRule boolEqExprRule
  <> exprRule iteBoolExprRule

boolTypeRule :: Rule s SMT.Type
boolTypeRule = asBoolType `matchArgs` SMT.tBool

trueExprRule :: Rule s SMT.Expr
trueExprRule  = asCtor "Prelude.True" asEmpty `matchArgs` SMT.true

falseExprRule :: Rule s SMT.Expr
falseExprRule = asCtor "Prelude.False" asEmpty `matchArgs` SMT.false

notExprRule :: Rule s SMT.Expr
notExprRule = asGlobalDef "Prelude.not" `matchArgs` SMT.not

-- TODO: Add implies to SAWCore prelude, and corresponding rule.

andExprRule :: Rule s SMT.Expr
andExprRule = asGlobalDef "Prelude.and" `matchArgs` SMT.and

orExprRule :: Rule s SMT.Expr
orExprRule = asGlobalDef "Prelude.or" `matchArgs` SMT.or

xorExprRule :: Rule s SMT.Expr
xorExprRule = asGlobalDef "Prelude.xor" `matchArgs` SMT.xor

boolEqExprRule :: Rule s SMT.Expr
boolEqExprRule = asGlobalDef "Prelude.boolEq" `matchArgs` (SMT.===)

iteBoolExprRule :: Rule s SMT.Expr
iteBoolExprRule = (asGlobalDef "Prelude.ite" <:> asAny) `matchArgs` iteExpr
  where iteExpr c t f = SMT.app "ite" [c,t,f]

-- * Array SMT rules

arrayRules :: RuleSet s
arrayRules = mempty -- TODO: Add rules for get and set and VecLit.

-- * Bitvector SMT rules.

bitvectorRules :: RuleSet s
bitvectorRules
  = coreRules
  <> arrayRules
  <> typeRule bitvectorVecTypeRule

-- How many bits do we need to represent the given number.
needBits :: Integer -> Integer
needBits n0 | n0 <= 0    = 0
            | otherwise = go n0 0
  where go :: Integer -> Integer -> Integer
        go 0 i = i
        go n i = (go $! (shiftR n 1)) $! (i+1)

bitvectorVecTypeRule :: Rule s SMT.Type
bitvectorVecTypeRule =
    asDataType "Prelude.Vec" (asAnyNatLit >: asAny) `thenMatcher` match
  where match ((fromIntegral -> n) :*: tp) = do
          mr <- runMaybeT (runMatcher asBoolType tp)
          case mr of
            Just _ -> return $ SMT.tBitVec n
            Nothing ->
              -- SMTLib arrays don't have lengths, but they do need
              -- an index type.
              lift $ SMT.tArray (SMT.tBitVec (needBits n)) <$> toSMTType tp

{-
bvNatExprRule :: Rule s SMT.Type
bvNatExprRule = asGlobalDef "Prelude.bvNat" `matchArgs` error "bvNatExprRule"

bvEqExprRule :: Rule s SMT.Type
bvEqExprRule = asGlobalDef "Prelude.bvEq" `matchArgs` error "bvEqExprRule"

bvAndExprRule :: Rule s SMT.Type
bvAndExprRule = asGlobalDef "Prelude.bvAnd" `matchArgs` error "bvAndExprRule"

bvOrExprRule :: Rule s SMT.Type
bvOrExprRule = asGlobalDef "Prelude.bvOr" `matchArgs` error "bvOrExprRule"

bvXorExprRule :: Rule s SMT.Type
bvXorExprRule = asGlobalDef "Prelude.bvXor" `matchArgs` error "bvXorExprRule"

bvShlExprRule :: Rule s SMT.Type
bvShlExprRule = asGlobalDef "Prelude.bvShl" `matchArgs` error "bvShlExprRule"

bvSShrExprRule :: Rule s SMT.Type
bvSShrExprRule = asGlobalDef "Prelude.bvSShr" `matchArgs` error "bvSShrExprRule"

bvShrExprRule :: Rule s SMT.Type
bvShrExprRule = asGlobalDef "Prelude.bvShr" `matchArgs` error "bvShrExprRule"

bvAddExprRule :: Rule s SMT.Type
bvAddExprRule = asGlobalDef "Prelude.bvAdd" `matchArgs` error "bvAddExprRule"

bvMulExprRule :: Rule s SMT.Type
bvMulExprRule = asGlobalDef "Prelude.bvMul" `matchArgs` error "bvMulExprRule"

bvSubExprRule :: Rule s SMT.Type
bvSubExprRule = asGlobalDef "Prelude.bvSub" `matchArgs` error "bvSubExprRule"

bvSdivExprRule :: Rule s SMT.Type
bvSdivExprRule = asGlobalDef "Prelude.bvSdiv" `matchArgs` error "bvSdivExprRule"

bvSremExprRule :: Rule s SMT.Type
bvSremExprRule = asGlobalDef "Prelude.bvSrem" `matchArgs` error "bvSremExprRule"

bvUdivExprRule :: Rule s SMT.Type
bvUdivExprRule = asGlobalDef "Prelude.bvUdiv" `matchArgs` error "bvUdivExprRule"

bvUremExprRule :: Rule s SMT.Type
bvUremExprRule = asGlobalDef "Prelude.bvUrem" `matchArgs` error "bvUremExprRule"

bvsleExprRule :: Rule s SMT.Type
bvsleExprRule = asGlobalDef "Prelude.bvsle" `matchArgs` error "bvsleExprRule"

bvsltExprRule :: Rule s SMT.Type
bvsltExprRule = asGlobalDef "Prelude.bvslt" `matchArgs` error "bvsltExprRule"

bvuleExprRule :: Rule s SMT.Type
bvuleExprRule = asGlobalDef "Prelude.bvule" `matchArgs` error "bvuleExprRule"

bvultExprRule :: Rule s SMT.Type
bvultExprRule = asGlobalDef "Prelude.bvult" `matchArgs` error "bvultExprRule"
-}