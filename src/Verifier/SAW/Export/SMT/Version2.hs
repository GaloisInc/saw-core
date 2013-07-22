{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Verifier.SAW.Export.SMT.Version2 
  ( WriterState
  , emptyWriterState
  , qf_aufbv_WriterState
  , render
  , warnings
  , Warning(..)
  , ppWarning
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
import Data.Monoid
import qualified Data.Map as Map
import Text.PrettyPrint.Leijen hiding ((<>), (<$>))

import qualified SMTLib2 as SMT
import qualified SMTLib2.Array as SMT
import qualified SMTLib2.BitVector as SMT
import qualified SMTLib2.Core as SMT

import Verifier.SAW.Export.SMT.Common
import Verifier.SAW.Prim
import Verifier.SAW.Rewriter ()
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.TermNet as Net

data Warning t
  = UnmatchedType SMT.Name t
  | UnmatchedExpr SMT.Name t
  deriving (Functor)

ppWarning :: Warning Doc -> Doc
ppWarning (UnmatchedType n d) =
  d <+> text "could not be interpreted as a type." <$$>
  text (show n ++ " introduced as an uninterpreted type to represent it.")
ppWarning (UnmatchedExpr n d) =
  d <+> text "could not be interpreted as an expression." <$$>
  text (show n ++ " introduced as a fresh constant to represent it.")

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
                 , _localExprs :: [SMT.Expr]
                 , _warnings :: [Warning (SharedTerm s)]
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
                 , _localExprs = []
                 , _warnings = []
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

localExprs :: Simple Lens (WriterState s) [SMT.Expr]
localExprs = lens _localExprs (\s v -> s { _localExprs = v})

warnings :: Simple Lens (WriterState s) [Warning (SharedTerm s)]
warnings = lens _warnings (\s v -> s { _warnings = v })

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
        warnings %= (UnmatchedType nm t:)
        return (SMT.TVar nm)

-- | Make a fresh free term using the given term as a type.
mkFreshExpr :: SMT.Type -> Writer s SMT.Name
mkFreshExpr tp = do
  -- Create name for fresh variable
  nm <- freshName smtExprNonce "x"
  -- Declare fresh variable.
  smtDefs %= (SMT.CmdDeclareFun nm [] tp:)
  return nm

smt_constexpr :: SMT.Name -> SMT.Type -> SMT.Expr
smt_constexpr nm tp = SMT.App (SMT.I nm []) (Just tp) []


toSMTExpr :: SharedTerm s -> Writer s SMT.Expr
toSMTExpr (STApp _ (Lambda _ ty tm)) = do
  ty' <- toSMTType ty
  nm <- mkFreshExpr ty'
  let x = smt_constexpr nm ty'
  localExprs %= (x:)
  r <- toSMTExpr tm
  localExprs %= tail
  return r
toSMTExpr t@(STApp i _tf) = do
  cache smtExprCache i $ do
    -- Get type of term
    tp <- do sc <- gets smtContext
             toSMTType =<< liftIO (scTypeOf sc t)
    -- Try matching term to get SMT definition.
    mdefExpr <- matchTerm smtExprNet t 
    case mdefExpr of
      Just defExpr -> do -- Define function if we can.
        -- Create name for fresh variable
        nm <- freshName smtExprNonce "x"
        -- Define fresh variable.
        smtDefs %= (SMT.CmdDefineFun nm [] tp defExpr:)
        return (smt_constexpr nm tp)
      -- Introduce fresh variable.
      Nothing -> do
        nm <- mkFreshExpr tp
        warnings %= (UnmatchedExpr nm t:)
        return (smt_constexpr nm tp)

assert :: SharedTerm s -> Writer s ()
assert t = do
  e <- toSMTExpr t
  smtCommands %= (SMT.CmdAssert e:)

checkSat :: Writer s ()
checkSat = smtCommands %= (SMT.CmdCheckSat:)

type RuleWriter s = MaybeT (Writer s)
type Rule s = Matcher (RuleWriter s) (SharedTerm s)

-- HACK!
instance Eq (Rule s r) where
  _ == _ = False

asSMTType :: Rule s SMT.Type
asSMTType = asVar (lift . toSMTType)

asSMTExpr :: Rule s SMT.Expr
asSMTExpr = asVar (lift . toSMTExpr)

data RuleSet s = RuleSet [Rule s SMT.Type] [Rule s SMT.Expr]

instance Monoid (RuleSet s) where
  mempty = RuleSet [] []
  mappend (RuleSet tx ex) (RuleSet ty ey) = RuleSet (tx ++ ty) (ex ++ ey)

typeRule :: Rule s SMT.Type -> RuleSet s
typeRule r = RuleSet [r] []

exprRule :: Rule s SMT.Expr -> RuleSet s
exprRule r = RuleSet [] [r]

instance Matchable (MaybeT (Writer s)) (SharedTerm s) SMT.Type where
  defaultMatcher = asSMTType

instance Matchable (MaybeT (Writer s)) (SharedTerm s) SMT.Expr where
  defaultMatcher = asSMTExpr

-- | SMT Rules for core theory.
coreRules :: RuleSet s
coreRules
  =  exprRule extCnsExprRule
  <> exprRule localExprRule
  <> typeRule (matchDataType "Prelude.Bool" SMT.tBool)
  <> exprRule (matchCtor "Prelude.True" SMT.true)
  <> exprRule (matchCtor "Prelude.False" SMT.false)
  <> exprRule (matchDef "Prelude.not" SMT.not)
  <> exprRule (matchDef "Prelude.and" SMT.and)
  <> exprRule (matchDef "Prelude.or" SMT.or)
  <> exprRule (matchDef "Prelude.xor" SMT.xor)
  <> exprRule (matchDef "Prelude.boolEq" (SMT.===))
  <> exprRule (matchArgs (asGlobalDef "Prelude.ite" <:> asAny) smt_ite)
  <> exprRule (matchArgs (asGlobalDef "Prelude.eq" <:> asAny) (SMT.===))

extCnsExprRule :: Rule s SMT.Expr
extCnsExprRule =
  thenMatcher asExtCns $ \ec -> lift $ do
    tp <- toSMTType (ecType ec)
    nm <- mkFreshExpr tp
    return (smt_constexpr nm tp)

localExprRule :: Rule s SMT.Expr
localExprRule =
  thenMatcher asLocalVar $ \i -> lift $ do
    ls <- use localExprs
    guard (i < length ls)
    return (ls !! i)

smt_ite :: SMT.Expr -> SMT.Expr -> SMT.Expr -> SMT.Expr
smt_ite c t f = SMT.app "ite" [c,t,f]

-- * Array SMT rules

arrayRules :: RuleSet s
arrayRules = mempty -- TODO: Add rules for get and set and VecLit.

-- * Bitvector SMT rules.

qf_aufbv_WriterState :: SharedContext s
                     -> WriterState s
qf_aufbv_WriterState sc = emptyWriterState sc "QF_AUFBV" bitvectorRules

bitvectorRules :: forall s . RuleSet s
bitvectorRules
  = coreRules
  <> arrayRules
  <> typeRule (matchDef "Prelude.bitvector" smt_bitvecType)
  <> typeRule (matchDataType "Prelude.Vec" 
                 (smt_vectype :: Nat -> SharedTerm s -> RuleWriter s SMT.Type))

  <> exprRule (matchDef "Prelude.bvNat" smt_bvNat)

  <> exprRule (bv_bin_rule "Prelude.bvEq" (SMT.===))

  <> exprRule (bv_bin_rule "Prelude.bvAdd" SMT.bvadd)
  <> exprRule (bv_bin_rule "Prelude.bvSub" SMT.bvsub)
  <> exprRule (bv_bin_rule "Prelude.bvMul" SMT.bvmul)

  <> exprRule (bv_bin_rule "Prelude.bvUdiv" SMT.bvudiv)
  <> exprRule (bv_bin_rule "Prelude.bvUrem" SMT.bvurem)
  <> exprRule (bv_bin_rule "Prelude.bvSdiv" SMT.bvsdiv)
  <> exprRule (bv_bin_rule "Prelude.bvSrem" SMT.bvsrem)

  <> exprRule (bv_bin_rule "Prelude.bvShl"  SMT.bvshl)
  <> exprRule (bv_bin_rule "Prelude.bvShr"  SMT.bvlshr)
  <> exprRule (bv_bin_rule "Prelude.bvSShr" SMT.bvashr)

  <> exprRule (bv_bin_rule "Prelude.bvAnd" SMT.bvand)
  <> exprRule (bv_bin_rule "Prelude.bvOr"  SMT.bvor)
  <> exprRule (bv_bin_rule "Prelude.bvXor" SMT.bvxor)

     -- Unsigned comparisons.
  <> exprRule (bv_bin_rule "Prelude.bvugt" SMT.bvugt)
  <> exprRule (bv_bin_rule "Prelude.bvuge" SMT.bvuge)
  <> exprRule (bv_bin_rule "Prelude.bvult" SMT.bvult)
  <> exprRule (bv_bin_rule "Prelude.bvule" SMT.bvule)

     -- Signed comparisons.
  <> exprRule (bv_bin_rule "Prelude.bvsgt" SMT.bvsgt)
  <> exprRule (bv_bin_rule "Prelude.bvsge" SMT.bvsge)
  <> exprRule (bv_bin_rule "Prelude.bvslt" SMT.bvslt)
  <> exprRule (bv_bin_rule "Prelude.bvsle" SMT.bvsle)

     -- Trunc and extension.
  <> exprRule (matchArgs (asGlobalDef "Prelude.bvTrunc" <:> asAny) 
                         (smt_trunc :: Nat -> SMT.Expr -> RuleWriter s SMT.Expr))
  <> exprRule (matchDef "Prelude.bvUExt" smt_uext)
  <> exprRule (matchDef "Prelude.bvSExt" smt_sext)


smt_bitvecType :: Nat -> SMT.Type
smt_bitvecType = SMT.tBitVec . fromIntegral

smt_vectype :: Nat -> SharedTerm s -> RuleWriter s SMT.Type
smt_vectype n tp = do
  mr <- runMaybeT (runMatcher asBoolType tp)
  case mr of
    Just _ -> return $ SMT.tBitVec (toInteger n)
    Nothing -> lift $ SMT.tArray (SMT.tBitVec (needBits n)) <$> toSMTType tp              

-- | Matches expressions with an extra int size argument.
bv_bin_rule :: Ident -> (SMT.Expr -> SMT.Expr -> SMT.Expr) -> Rule s SMT.Expr
bv_bin_rule d = matchArgs (asGlobalDef d <:> asAnyNatLit)

smt_bvNat :: Nat -> Nat -> SMT.Expr
smt_bvNat w v = SMT.bv (toInteger v) (toInteger w)

smt_trunc :: Monad m => Nat -> SMT.Expr -> m SMT.Expr
smt_trunc 0 _ = fail "SMTLIB does not support size 0 bitvectors."
smt_trunc y v = return $ SMT.extract (toInteger y-1) 0 v

-- | @smt_uext i n x@ zero extends a @n@-bit bitvector @x@ to a
-- @n+i@-bit bitvector.
smt_uext :: Nat -> Nat -> SMT.Expr -> SMT.Expr
smt_uext i _ x = SMT.zero_extend (toInteger i) x

-- | @smt_sext i n x@ sign extends a @n@-bit bitvector @x@ to a
-- @n+i@-bit bitvector.
smt_sext :: Nat -> Nat -> SMT.Expr -> SMT.Expr
smt_sext i _ x = SMT.sign_extend (toInteger i) x
