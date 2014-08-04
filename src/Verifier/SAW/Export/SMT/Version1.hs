{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.Export.SMT.Version1
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Export.SMT.Version1
  ( WriterState
  , emptyWriterState
  , render
  , smtScript
  , warnings
  , Warning(..)
  , ppWarning
  , SMT.Name
    -- * Writer
  , Writer
  , toSort
  , toFormula
  , toTerm
  , writeCommand
  , writeAssumption
  , writeFormula
    -- * Matching rules for trnslation
  , Rule
  , RuleSet
  , sortRule
  , formulaRule
  , termRule
    -- * Predefined rules
  , coreRules
  , qf_aufbv_WriterState
  , bitvectorRules
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Monoid
import qualified Data.Map as Map

import Text.PrettyPrint.Leijen hiding ((<>), (<$>))

import qualified SMTLib1 as SMT
import qualified SMTLib1.QF_AUFBV as SMT

import Verifier.SAW.Export.SMT.Common
import Verifier.SAW.Prim
import Verifier.SAW.Recognizer (asLambda)
import Verifier.SAW.Rewriter ()
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.TermNet as Net

data Warning t
  = UnmatchedSort    SMT.Ident t
  | UnmatchedFormula SMT.Ident t
  | UnmatchedTerm    SMT.Ident t
  deriving (Functor)

ppWarning :: Warning Doc -> Doc
ppWarning (UnmatchedSort n d) =
  d <+> text "could not be interpreted as a sort." <$$>
  text (show n ++ " introduced as an uninterpreted sort to represent it.")
ppWarning (UnmatchedFormula n d) =
  d <+> text "could not be interpreted as a formula." <$$>
  text (show n ++ " introduced as a fresh predicate.")
ppWarning (UnmatchedTerm n d) =
  d <+> text "could not be interpreted as a term." <$$>
  text (show n ++ " introduced as a fresh constant.")

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
                 , _localTerms :: [SMT.Term]
                 , _localTys :: [SharedTerm s]

                 , _warnings :: [Warning (SharedTerm s)]
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
                , _localTerms = []
                , _localTys = []
                , _warnings = []
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

warnings :: Simple Lens (WriterState s) [Warning (SharedTerm s)]
warnings = lens _warnings (\s v -> s { _warnings = v })

localTerms :: Simple Lens (WriterState s) [SMT.Term]
localTerms = lens _localTerms (\s v -> s { _localTerms = v})

localTys :: Simple Lens (WriterState s) [SharedTerm s]
localTys = lens _localTys (\s v -> s { _localTys = v})

render :: WriterState s -> String
render = show . SMT.pp . smtScript

smtScript :: WriterState s -> SMT.Script
smtScript s = SMT.Script
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
        warnings %= (UnmatchedSort nm t:)
        return nm

mkFreshFormula :: Writer s SMT.Ident
mkFreshFormula = do
  nm <- freshName smtFormulaNonce "c"
  smtExtraPreds %= (SMT.PredDecl nm [] []:)
  return nm

-- | Make a fresh free term using the given term as a type.
mkFreshTerm :: SharedTerm s -> Writer s SMT.Ident
mkFreshTerm tp = do
  nm <- freshName smtTermNonce "t"
  s <- toSort tp
  smtExtraFuns %= (SMT.FunDecl nm [] s []:)
  return nm

smt_pred0 :: SMT.Ident -> SMT.Formula
smt_pred0 nm = SMT.FPred nm []

smt_term0 :: SMT.Ident -> SMT.Term
smt_term0 nm = SMT.App nm []

toFormula :: SharedTerm s -> Writer s SMT.Formula
-- toFormula t@(STApp i (Lambda (Pat x _ _) tm) = do
toFormula t@(STApp i _tf) = do
  cache smtFormulaCache i $ do
    -- Create name for fresh variable
    nm <- mkFreshFormula
    let p = smt_pred0 nm
    -- Try matching term to get SMT definition.
    mdefFormula <- matchTerm smtFormulaNet t 
    case mdefFormula of
      Just defFormula -> do -- Define function if we can.
        let assumpt = SMT.CmdAssumption (SMT.Conn SMT.Iff [p, defFormula])
        smtCommands %= (assumpt:)
      Nothing -> do
        warnings %= (UnmatchedFormula nm t:)
    return p

toTerm :: SharedTerm s -> Writer s SMT.Term
toTerm t@(STApp i _tf) = do
  cache smtTermCache i $ do
    -- Create name for fresh variable
    nm <- do sc <- gets smtContext
             tys <- use localTys
             mkFreshTerm =<< liftIO (scTypeOf' sc tys t)
    let app = smt_term0 nm
    -- Try matching term to get SMT definition.
    mdefTerm <- matchTerm smtTermNet t 
    case mdefTerm of
      Just defTerm -> do -- Define function if we can.
        let assumpt = SMT.CmdAssumption $ app SMT.=== defTerm 
        smtCommands %= (assumpt:)
      Nothing -> do
        warnings %= (UnmatchedTerm nm t:)
    return app

writeCommand :: SMT.Command -> Writer s ()
writeCommand c = smtCommands %= (c:)

-- | Write an assumption SMT command to script.
writeAssumption :: SharedTerm s -> Writer s ()
writeAssumption t = writeCommand . SMT.CmdAssumption =<< toFormula t

-- | Write a formula SMT command to script.
writeFormula :: SharedTerm s -> Writer s ()
writeFormula t = writeCommand . SMT.CmdFormula =<< toFormula t

type RuleWriter s = MaybeT (Writer s)

type Rule s = Matcher (RuleWriter s) (SharedTerm s)

-- HACK!
instance Eq (Rule s r) where
  _ == _ = False

asSMTSort :: Rule s SMT.Sort
asSMTSort = asVar (lift . toSort)

asFormula :: Rule s SMT.Formula
asFormula = asVar (lift . toFormula)

asTerm :: Rule s SMT.Term
asTerm = asVar (lift . toTerm)

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
  =  formulaRule extCnsFormulaRule
  <> termRule    extCnsTermRule
  <> formulaRule lambdaFormulaRule
  <> termRule    localTermRule
  <> formulaRule trueFormulaRule
  <> formulaRule falseFormulaRule
  <> formulaRule notFormulaRule
  <> formulaRule andFormulaRule
  <> formulaRule orFormulaRule
  <> formulaRule xorFormulaRule
  <> formulaRule boolEqFormulaRule
  <> formulaRule iteBoolFormulaRule
  <> termRule iteTermRule
  <> formulaRule (matchArgs (asGlobalDef "Prelude.eq" <:> asAny) (SMT.===))


extCnsFormulaRule :: Rule s SMT.Formula
extCnsFormulaRule =
  thenMatcher asExtCns $ \ec -> do
    BoolType <- runMatcher defaultMatcher (ecType ec)
    lift $ smt_pred0 <$> mkFreshFormula

extCnsTermRule :: Rule s SMT.Term
extCnsTermRule =
  thenMatcher asExtCns $ \ec ->
    lift $ smt_term0 <$> mkFreshTerm (ecType ec)

lambdaFormulaRule :: Rule s SMT.Formula
lambdaFormulaRule =
  thenMatcher (asVar asLambda) $ \(_, ty, tm) -> lift $ do
    x <- smt_term0 <$> mkFreshTerm ty
    localTerms %= (x:)
    localTys %= (ty:)
    r <- toFormula tm
    localTerms %= tail
    localTys %= tail
    return r

localTermRule :: Rule s SMT.Term
localTermRule =
  thenMatcher asLocalVar $ \i -> do
    ls <- use localTerms
    guard (i < length ls)
    return (ls !! i)

trueFormulaRule :: Rule s SMT.Formula
trueFormulaRule  = matchCtor "Prelude.True" SMT.FTrue

falseFormulaRule :: Rule s SMT.Formula
falseFormulaRule = matchCtor "Prelude.False" SMT.FFalse

notFormulaRule :: Rule s SMT.Formula
notFormulaRule = matchDef "Prelude.not" smt_not
  where smt_not x = SMT.Conn SMT.Not [x]

-- TODO: Add implies to SAWCore prelude, and corresponding rule.

binFormulaRule :: Ident -> SMT.Conn -> Rule s SMT.Formula
binFormulaRule d c = matchDef d smt_conn
  where smt_conn x y = SMT.Conn c [x, y]

andFormulaRule :: Rule s SMT.Formula
andFormulaRule = binFormulaRule "Prelude.and" SMT.And

orFormulaRule :: Rule s SMT.Formula
orFormulaRule = binFormulaRule "Prelude.or" SMT.Or

xorFormulaRule :: Rule s SMT.Formula
xorFormulaRule = binFormulaRule "Prelude.xor" SMT.Xor

boolEqFormulaRule :: Rule s SMT.Formula
boolEqFormulaRule = binFormulaRule "Prelude.boolEq" SMT.Iff

iteBoolFormulaRule :: Rule s SMT.Formula
iteBoolFormulaRule = matchDef "Prelude.ite" smt_ite
  where smt_ite BoolType c t f = SMT.Conn SMT.IfThenElse [c,t,f]

iteTermRule :: Rule s SMT.Term
iteTermRule = (asGlobalDef "Prelude.ite" <:> asAny) `matchArgs` SMT.ITE

------------------------------------------------------------------------
-- Bitvector Rules

qf_aufbv_WriterState :: SharedContext s
                     -> SMT.Ident -- ^ Name of benchmark
                     -> WriterState s
qf_aufbv_WriterState sc nm = emptyWriterState sc nm "QF_AUFBV" bitvectorRules

bitvectorRules :: forall s . RuleSet s
bitvectorRules
  = coreRules
  <> sortRule (matchDef      "Prelude.bitvector" smt_bitvector)
  <> sortRule (matchDataType "Prelude.Vec"       smt_bitvector_type)
  <> sortRule (matchDataType "Prelude.Vec"       smt_array_of_bitvectors)
  <> termRule (matchDef      "Prelude.bvNat"     smt_bv)

  <> formulaRule (bvBinOpRule "Prelude.bvEq" (SMT.===))

  <> termRule (bvBinOpRule "Prelude.bvAdd" SMT.bvadd)
  <> termRule (bvBinOpRule "Prelude.bvSub" SMT.bvsub)
  <> termRule (bvBinOpRule "Prelude.bvMul" SMT.bvmul)

  <> termRule (bvBinOpRule "Prelude.bvUdiv" SMT.bvudiv)
  <> termRule (bvBinOpRule "Prelude.bvUrem" SMT.bvurem)
  <> termRule (bvBinOpRule "Prelude.bvSdiv" SMT.bvsdiv)
  <> termRule (bvBinOpRule "Prelude.bvSrem" SMT.bvsrem)

  <> termRule (bvShiftOpRule "Prelude.bvShl"  smt_bvshl)
  <> termRule (bvShiftOpRule "Prelude.bvShr"  smt_bvlshr)
  <> termRule (bvShiftOpRule "Prelude.bvSShr" smt_bvashr)

  <> termRule (bvBinOpRule "Prelude.bvAnd" SMT.bvand)
  <> termRule (bvBinOpRule "Prelude.bvOr"  SMT.bvor)
  <> termRule (bvBinOpRule "Prelude.bvXor" SMT.bvxor)

  <> formulaRule (bvBinOpRule "Prelude.bvugt" SMT.bvugt)
  <> formulaRule (bvBinOpRule "Prelude.bvuge" SMT.bvuge)
  <> formulaRule (bvBinOpRule "Prelude.bvult" smt_bvult)
  <> formulaRule (bvBinOpRule "Prelude.bvule" SMT.bvule)

  <> formulaRule (bvBinOpRule "Prelude.bvsgt" SMT.bvsgt)
  <> formulaRule (bvBinOpRule "Prelude.bvsge" SMT.bvsge)
  <> formulaRule (bvBinOpRule "Prelude.bvslt" SMT.bvslt)
  <> formulaRule (bvBinOpRule "Prelude.bvsle" SMT.bvsle)
     -- Trunc and extension.
  <> termRule (matchArgs (asGlobalDef "Prelude.bvTrunc" <:> asAny) 
                         (smt_trunc :: Nat -> SMT.Term -> RuleWriter s SMT.Term))
  <> termRule (matchDef "Prelude.bvUExt" smt_uext)
  <> termRule (matchDef "Prelude.bvSExt" smt_sext)

-- | Matches expressions with an extra int size argument.
bvBinOpRule :: (Applicative m, Monad m, Termlike t, Renderable a m t b)
            => Ident -> a -> Matcher m t b
bvBinOpRule d = matchArgs (asGlobalDef d <:> asAnyNatLit)

bvShiftOpRule :: (Applicative m, Monad m, Termlike t, Renderable a m t b)
            => Ident -> a -> Matcher m t b
bvShiftOpRule d = matchArgs (asGlobalDef d)

smt_bitvector :: Nat -> SMT.Sort
smt_bitvector = SMT.tBitVec . fromIntegral

smt_bitvector_type :: Nat -> BoolType -> SMT.Sort
smt_bitvector_type n _ = smt_bitvector n

-- | Create an array of bitvectors.
smt_array_of_bitvectors :: Nat -> BitvectorType -> SMT.Sort
smt_array_of_bitvectors n (BitvectorType w) = SMT.tArray (needBits n) (fromIntegral w)

-- | @smt_bv n x@ creates a @n@-bit bitvector containing @x `mod` 2^n-1@.
smt_bv :: Nat -> Nat -> SMT.Term
smt_bv n x = SMT.bv (toInteger x) (toInteger n)

-- | Perform unsigned less then.
-- For some reason, this is missing from smtLib library as of version 1.0.4.
smt_bvult :: SMT.Term -> SMT.Term -> SMT.Formula
smt_bvult s t = SMT.FPred "bvult" [s,t]

smt_trunc :: Monad m => Nat -> SMT.Term -> m SMT.Term
smt_trunc 0 _ = fail "SMTLIB does not support size 0 bitvectors."
smt_trunc y v = return $ SMT.extract (toInteger y-1) 0 v

-- | @smt_uext i n x@ zero extends a @n@-bit bitvector @x@ to a
-- @n+i@-bit bitvector.
smt_uext :: Nat -> Nat -> SMT.Term -> SMT.Term
smt_uext i _ x = SMT.zero_extend (toInteger i) x

-- | @smt_sext i n x@ sign extends a @n@-bit bitvector @x@ to a
-- @n+i@-bit bitvector.
smt_sext :: Nat -> Nat -> SMT.Term -> SMT.Term
smt_sext i _ x = SMT.sign_extend (toInteger i) x

smt_bvshl :: Nat -> SMT.Term -> Nat -> SMT.Term
smt_bvshl w t n = SMT.bvshl t (smt_bv w n)

smt_bvlshr :: Nat -> SMT.Term -> Nat -> SMT.Term
smt_bvlshr w t n = SMT.bvlshr t (smt_bv w n)

smt_bvashr :: Nat -> SMT.Term -> Nat -> SMT.Term
smt_bvashr w t n = SMT.bvashr t (smt_bv w n)
