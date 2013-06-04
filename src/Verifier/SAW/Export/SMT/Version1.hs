{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Verifier.SAW.Export.SMT.Version1
  ( WriterState
  , emptyWriterState
  , render
  , warnings
  , Warning(..)
  , SMT.Name
    -- * Writer
  , Writer
  , formula
    -- * Matching rules for trnslation
  , Rule
  , RuleSet
  , sortRule
  , formulaRule
  , termRule
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

import qualified SMTLib1 as SMT
import qualified SMTLib1.QF_AUFBV as SMT

import Verifier.SAW.Export.SMT.Common
import Verifier.SAW.Conversion
import Verifier.SAW.Prim
import Verifier.SAW.Rewriter ()
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.TermNet as Net

data Warning t
  = UnmatchedSort    SMT.Ident t
  | UnmatchedFormula SMT.Ident t
  | UnmatchedTerm    SMT.Ident t

data WriterState s =
     WriterState { smtContext :: SharedContext s
                 , smtName :: !SMT.Ident
                 , smtLogic :: !SMT.Ident
                 -- Maps term representing types already seen to expression.
                 , smtSortNet :: Net.Net (Rule s SMT.Sort)
                 , _smtSortCache :: !(Map.Map TermIndex SMT.Sort)
                 , _smtSortNonce :: !Int
                 -- Maps terms representing formulas already seen to expression.
                 , smtFormulaNet :: Net.Net (Rule s SMT.Formula)
                 , _smtFormulaCache :: !(Map.Map TermIndex SMT.Formula)
                 , _smtFormulaNonce :: !Int
                 -- Maps terms representing SMT term already seen to expression.
                 , smtTermNet :: Net.Net (Rule s SMT.Term)
                 , _smtTermCache :: !(Map.Map TermIndex SMT.Term)
                 , _smtTermNonce :: !Int

                 , _smtExtraSorts :: [SMT.Sort]
                 , _smtExtraFuns  :: [SMT.FunDecl]
                 , _smtExtraPreds :: [SMT.PredDecl]
                 , _smtCommands :: [SMT.Command]

                 , _smtWarnings :: [Warning (SharedTerm s)]
                 }

emptyWriterState :: SharedContext s
                 -> SMT.Ident -- ^ Name of file
                 -> SMT.Ident -- ^ Name of theory
                 -> RuleSet s
                 -> WriterState s
emptyWriterState ctx nm logic (RuleSet sr fr tr) =
    WriterState { smtContext = ctx
                , smtName = nm
                , smtLogic = logic
                , smtSortNet = foldr addRule Net.empty sr
                , _smtSortCache = Map.empty
                , _smtSortNonce = 0
                , smtFormulaNet = foldr addRule Net.empty fr
                , _smtFormulaCache = Map.empty
                , _smtFormulaNonce = 0
                , smtTermNet = foldr addRule Net.empty tr
                , _smtTermCache = Map.empty
                , _smtTermNonce = 0
                , _smtExtraSorts = []
                , _smtExtraFuns  = []
                , _smtExtraPreds = []
                , _smtCommands = []
                , _smtWarnings = []
                }
  where addRule rule = Net.insert_term (rule, rule)

smtSortCache :: Simple Lens (WriterState s) (Map.Map TermIndex SMT.Sort)
smtSortCache = lens _smtSortCache (\s v -> s { _smtSortCache = v })

smtSortNonce :: Simple Lens (WriterState s) Int
smtSortNonce = lens _smtSortNonce (\s v -> s { _smtSortNonce = v })

smtFormulaCache :: Simple Lens (WriterState s) (Map.Map TermIndex SMT.Formula)
smtFormulaCache = lens _smtFormulaCache (\s v -> s { _smtFormulaCache = v })

smtFormulaNonce :: Simple Lens (WriterState s) Int
smtFormulaNonce = lens _smtFormulaNonce (\s v -> s { _smtFormulaNonce = v })

smtTermCache :: Simple Lens (WriterState s) (Map.Map TermIndex SMT.Term)
smtTermCache = lens _smtTermCache (\s v -> s { _smtTermCache = v })

smtTermNonce :: Simple Lens (WriterState s) Int
smtTermNonce = lens _smtTermNonce (\s v -> s { _smtTermNonce = v })

smtExtraSorts :: Simple Lens (WriterState s) [SMT.Sort]
smtExtraSorts = lens _smtExtraSorts (\s v -> s { _smtExtraSorts = v })

smtExtraFuns :: Simple Lens (WriterState s) [SMT.FunDecl]
smtExtraFuns = lens _smtExtraFuns (\s v -> s { _smtExtraFuns = v })

smtExtraPreds :: Simple Lens (WriterState s) [SMT.PredDecl]
smtExtraPreds = lens _smtExtraPreds (\s v -> s { _smtExtraPreds = v })

smtCommands :: Simple Lens (WriterState s) [SMT.Command]
smtCommands = lens _smtCommands (\s v -> s { _smtCommands = v })

smtWarnings :: Simple Lens (WriterState s) [Warning (SharedTerm s)]
smtWarnings = lens _smtWarnings (\s v -> s { _smtWarnings = v })

warnings :: WriterState s -> [Warning (SharedTerm s)]
warnings = view smtWarnings 

render :: WriterState s -> String
render s = show $ SMT.pp $ SMT.Script
    { SMT.scrName = smtName s
    , SMT.scrCommands = 
       [ SMT.CmdLogic (smtLogic s)
       , SMT.CmdExtraSorts (reverse (s^.smtExtraSorts))
       , SMT.CmdExtraFuns  (reverse (s^.smtExtraFuns))
       , SMT.CmdExtraPreds (reverse (s^.smtExtraPreds))
       ]
       ++ reverse (s^.smtCommands) 
    }

------------------------------------------------------------------------
-- Writer

type Writer s = StateT (WriterState s) IO

toSort :: SharedTerm s -> Writer s SMT.Sort
toSort t@(STApp i _tf) = do
  cache smtSortCache i $ do
    mres <- matchTerm smtSortNet t
    case mres of
      Just r -> return r
      Nothing -> do
        -- Create name for fresh type.
        nm <- freshName smtSortNonce "tp"
        -- Add warning for unmatched type.
        smtWarnings %= (UnmatchedSort nm t:)
        return nm

toSMTFormula :: SharedTerm s -> Writer s SMT.Formula
toSMTFormula t@(STApp i _tf) = do
  cache smtFormulaCache i $ do
    -- Create name for fresh variable
    nm <- freshName smtFormulaNonce "c"
    smtExtraPreds %= (SMT.PredDecl nm [] []:)
    let p = SMT.FPred nm []
    -- Try matching term to get SMT definition.
    mdefFormula <- matchTerm smtFormulaNet t 
    case mdefFormula of
      Just defFormula -> do -- Define function if we can.
        let assumpt = SMT.CmdAssumption (SMT.Conn SMT.Iff [p, defFormula])
        smtCommands %= (assumpt:)
      -- Introduce fresh variable.
      Nothing -> do
        smtWarnings %= (UnmatchedFormula nm t:)
    return p

toSMTTerm :: SharedTerm s -> Writer s SMT.Term
toSMTTerm t@(STApp i _tf) = do
  cache smtTermCache i $ do
    -- Get sort of term
    s <- do sc <- gets smtContext
            toSort =<< liftIO (scTypeOf sc t)
    -- Create name for fresh variable
    nm <- freshName smtTermNonce "t"
    smtExtraFuns %= (SMT.FunDecl nm [] s []:)
    -- Try matching term to get SMT definition.
    mdefTerm <- matchTerm smtTermNet t 
    case mdefTerm of
      Just defTerm -> do -- Define function if we can.
        let assumpt = SMT.CmdAssumption $ SMT.App nm [] SMT.=== defTerm 
        smtCommands %= (assumpt:)
      -- Introduce fresh variable.
      Nothing -> do
        smtWarnings %= (UnmatchedFormula nm t:)
    return $ SMT.App nm []

-- | Write a formula SMT command to script.
formula :: SharedTerm s -> Writer s ()
formula t = do
  e <- toSMTFormula t
  smtCommands %= (SMT.CmdFormula e:)

type Rule s = Matcher (MaybeT (Writer s)) (SharedTerm s)

-- HACK!
instance Eq (Rule s r) where
  x == y = Net.toPat x == Net.toPat y

asSMTSort :: Rule s SMT.Sort
asSMTSort = asVar (lift . toSort)

asFormula :: Rule s SMT.Formula
asFormula = asVar (lift . toSMTFormula)

asTerm :: Rule s SMT.Term
asTerm = asVar (lift . toSMTTerm)

data RuleSet s = RuleSet [Rule s SMT.Sort]
                         [Rule s SMT.Formula]
                         [Rule s SMT.Term]

sortRule :: Rule s SMT.Sort -> RuleSet s
sortRule r = RuleSet [r] [] []

formulaRule :: Rule s SMT.Formula -> RuleSet s
formulaRule r = RuleSet [] [r] []

termRule :: Rule s SMT.Term -> RuleSet s
termRule r = RuleSet [] [] [r]

instance Monoid (RuleSet s) where
  mempty = RuleSet [] [] []
  mappend (RuleSet sx fx ex) (RuleSet sy fy ey) = 
    RuleSet (sx ++ sy) (fx ++ fy) (ex ++ ey)

instance Matchable (MaybeT (Writer s)) (SharedTerm s) SMT.Sort where
  defaultMatcher = asSMTSort

instance Matchable (MaybeT (Writer s)) (SharedTerm s) SMT.Formula where
  defaultMatcher = asFormula

instance Matchable (MaybeT (Writer s)) (SharedTerm s) SMT.Term where
  defaultMatcher = asTerm

------------------------------------------------------------------------
-- Core Rules

-- | SMT Rules for core theory.
coreRules :: RuleSet s
coreRules
  =  formulaRule trueFormulaRule
  <> formulaRule falseFormulaRule
  <> formulaRule notFormulaRule
  <> formulaRule andFormulaRule
  <> formulaRule orFormulaRule
  <> formulaRule xorFormulaRule
  <> formulaRule boolEqFormulaRule
  <> formulaRule iteBoolFormulaRule
  <> termRule iteTermRule

trueFormulaRule :: Rule s SMT.Formula
trueFormulaRule  = asCtor "Prelude.True" asEmpty `matchArgs` SMT.FTrue

falseFormulaRule :: Rule s SMT.Formula
falseFormulaRule = asCtor "Prelude.False" asEmpty `matchArgs` SMT.FFalse

notFormulaRule :: Rule s SMT.Formula
notFormulaRule = asGlobalDef "Prelude.not" `matchArgs` smtNot
  where smtNot x = SMT.Conn SMT.Not [x]

-- TODO: Add implies to SAWCore prelude, and corresponding rule.

binFormulaRule :: Ident -> SMT.Conn -> Rule s SMT.Formula
binFormulaRule d c = asGlobalDef d `matchArgs` fn
  where fn x y = SMT.Conn c [x, y]

andFormulaRule :: Rule s SMT.Formula
andFormulaRule = binFormulaRule "Prelude.and" SMT.And

orFormulaRule :: Rule s SMT.Formula
orFormulaRule = binFormulaRule "Prelude.or" SMT.Or

xorFormulaRule :: Rule s SMT.Formula
xorFormulaRule = binFormulaRule "Prelude.xor" SMT.Xor

boolEqFormulaRule :: Rule s SMT.Formula
boolEqFormulaRule = binFormulaRule "Prelude.boolEq" SMT.Iff

iteBoolFormulaRule :: Rule s SMT.Formula
iteBoolFormulaRule = (asGlobalDef "Prelude.ite" <:> asBoolType) `matchArgs` iteExpr
  where iteExpr c t f = SMT.Conn SMT.IfThenElse [c,t,f]

iteTermRule :: Rule s SMT.Term
iteTermRule = (asGlobalDef "Prelude.ite" <:> asAny) `matchArgs` SMT.ITE

------------------------------------------------------------------------
-- Bitvector Rules

bitvectorRules :: RuleSet s
bitvectorRules
  = coreRules
  <> sortRule bitvectorVecSortRule
  <> sortRule bvBVSortRule
  <> termRule (asGlobalDef "Prelude.bvNat" `matchArgs` smt_bv)

  <> formulaRule (bvBinOpRule "Prelude.bvEq" (SMT.===))

  <> termRule (bvBinOpRule "Prelude.bvAdd" SMT.bvadd)
  <> termRule (bvBinOpRule "Prelude.bvSub" SMT.bvsub)
  <> termRule (bvBinOpRule "Prelude.bvMul" SMT.bvmul)

  <> termRule (bvBinOpRule "Prelude.bvAnd" SMT.bvand)
  <> termRule (bvBinOpRule "Prelude.bvOr"  SMT.bvor)
  <> termRule (bvBinOpRule "Prelude.bvXor" SMT.bvxor)

  <> termRule (bvBinOpRule "Prelude.bvShl"  SMT.bvshl)
  <> termRule (bvBinOpRule "Prelude.bvSShr" SMT.bvashr)
  <> termRule (bvBinOpRule "Prelude.bvShr"  SMT.bvlshr)

  <> termRule (bvBinOpRule "Prelude.bvSdiv" SMT.bvsdiv)
  <> termRule (bvBinOpRule "Prelude.bvSrem" SMT.bvsrem)
  <> termRule (bvBinOpRule "Prelude.bvUdiv" SMT.bvudiv)
  <> termRule (bvBinOpRule "Prelude.bvUrem" SMT.bvurem)

  <> formulaRule (bvBinOpRule "Prelude.bvugt" SMT.bvugt)
  <> formulaRule (bvBinOpRule "Prelude.bvuge" SMT.bvuge)
  <> formulaRule (bvBinOpRule "Prelude.bvult" smt_bvult)
  <> formulaRule (bvBinOpRule "Prelude.bvule" SMT.bvule)

  <> formulaRule (bvBinOpRule "Prelude.bvsgt" SMT.bvsgt)
  <> formulaRule (bvBinOpRule "Prelude.bvsge" SMT.bvsge)
  <> formulaRule (bvBinOpRule "Prelude.bvslt" SMT.bvslt)
  <> formulaRule (bvBinOpRule "Prelude.bvsle" SMT.bvsle)

-- | Matches expressions with an extra int size argument.
bvBinOpRule :: (Applicative m, Monad m, Termlike t, Renderable m t a b)
            => Ident -> a -> Matcher m t b
bvBinOpRule d = matchArgs (asGlobalDef d <:> asAnyNatLit)

-- | How many bits do we need to represent the given number.
needBits :: Nat -> Integer
needBits n0 | n0 <= 0    = 0
            | otherwise = go n0 0
  where go :: Nat -> Integer -> Integer
        go 0 i = i
        go n i = (go $! (shiftR n 1)) $! (i+1)

asBitvectorType :: (Termlike t, Monad m) => Matcher m t Nat
asBitvectorType = 
  thenMatcher (asDataType "Prelude.Vec" (asAnyNatLit >: asBoolType))
              (\(n :*: _) -> return n)

-- | Matches bitvectors.
bitvectorVecSortRule :: Rule s SMT.Sort
bitvectorVecSortRule =
  thenMatcher asBitvectorType
              (return . SMT.tBitVec . fromIntegral)

-- | Matches vectors of bitvectors.
bvBVSortRule :: Rule s SMT.Sort
bvBVSortRule =
  thenMatcher (asDataType "Prelude.Vec" (asAnyNatLit >: asBitvectorType))
              (\(n :*: w) -> return (SMT.tArray (needBits n) (fromIntegral w)))

-- | Create a bitvector from Nat literals.
smt_bv :: Nat -> Nat -> SMT.Term
smt_bv w v = SMT.bv (toInteger w) (toInteger v)

-- | Perform unsigned less then.
-- For some reason, this is missing from smtLib library as of version 1.0.4.
smt_bvult :: SMT.Term -> SMT.Term -> SMT.Formula
smt_bvult s t = SMT.FPred "bvult" [s,t]
