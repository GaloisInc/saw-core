{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.BitBlast
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.BitBlast
  {-# DEPRECATED "Use Verifier.SAW.Simulator.BitBlast instead" #-}
  ( BValue(..)
  , FiniteType(..)
  , flattenBValue
  , bitBlast
  , bitBlastWithEnv
  , lvVector
  , getShape
  , parseShape
    -- * Explicitly cached interface
  , LV.Storable
  , BCache
  , bcEngine
  , newBCache
  , addCut
  , bitBlastWith
    -- * Rules for bitblasting.
  , RuleSet
  , Rule
  , termRule
  , RuleBlaster
  , Bitblaster
  , blastBV
    -- * Standard prelude bitvector rules.
  , bvRules
     -- * Re-exports
  , (<>)
  , Matcher
  , Renderable
  , Termlike
  , matchArgs
    -- Lifting results back to Terms
  , liftCounterExample
  , liftCounterExamples
  , liftConcreteBValue
  ) where

import Control.Applicative
import Control.Exception (assert)
import Control.Lens
import Control.Monad
import Control.Monad.Reader
import qualified Control.Monad.State as S
import Control.Monad.Error
import Control.Monad.Trans.Maybe
import Data.Foldable (Foldable)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Traversable as T
import qualified Data.Vector as V
import qualified Data.Vector.Storable as LV
import Text.PrettyPrint.Leijen hiding ((<$>), (<>))

import Data.AIG (IsAIG, IsLit)
import qualified Data.AIG as AIG


import Verifier.SAW.FiniteValue
import Verifier.SAW.Export.SMT.Common
import Verifier.SAW.Prim
import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.Rewriter ()
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.TypedAST

type LitVector = AIG.BV

beAndInt :: IsAIG l g => g s -> LitVector (l s) -> LitVector (l s) -> IO (LitVector (l s))
beAndInt g = AIG.zipWithM (AIG.and g)

beOrInt :: IsAIG l g => g s -> LitVector (l s) -> LitVector (l s) -> IO (LitVector (l s))
beOrInt g = AIG.zipWithM (AIG.or g)

beXorInt :: IsAIG l g => g s -> LitVector (l s) -> LitVector (l s) -> IO (LitVector (l s))
beXorInt g = AIG.zipWithM (AIG.xor g)

lvFromV :: V.Vector l -> LitVector l
lvFromV v = AIG.generate_msb0 (V.length v) (v V.!)

lvShl :: AIG.BV (l s) ->  Nat -> l s -> AIG.BV (l s)
lvShl x i l = AIG.slice x j (n-j) AIG.++ AIG.replicate j l
  where n = AIG.length x
        -- Number of bits to insert on left, and bits to drop.
        j = fromIntegral i `min` n

lvShr :: LitVector (l s) ->  Nat -> l s -> LitVector (l s)
lvShr x i l = AIG.replicate j l AIG.++ AIG.slice x 0 (n-j)
  where n = AIG.length x
        j = fromIntegral i `min` n

-- | Bit-blasted representations of terms.
data BValue l
    = BBool !l
    | BVector (V.Vector (BValue l))
    | BTuple [BValue l]
    | BRecord (Map FieldName (BValue l))
  deriving (Functor, Foldable, Show, Traversable)

bTupleSelect :: Monad m => BValue l -> Int -> m (BValue l)
bTupleSelect (BTuple l) i | 0 <= i && i < length l = return (l !! i)
bTupleSelect _ _ = fail "Invalid tuple selector."

bRecordSelect :: Monad m => BValue l -> FieldName -> m (BValue l)
bRecordSelect (BRecord m) nm | Just v <- Map.lookup nm m = return v
bRecordSelect _ _ = fail "Invalid record selector."

lvVector :: LitVector l -> BValue l
lvVector lv = BVector v 
  where v = V.generate (AIG.length lv) (\i -> BBool (lv `AIG.at` i)) 

flattenBValue :: BValue l -> LitVector l
flattenBValue (BBool l)    = AIG.replicate 1 l
flattenBValue (BVector v)  = AIG.concat (flattenBValue <$> V.toList v)
flattenBValue (BTuple vs)  = AIG.concat (flattenBValue <$> vs)
flattenBValue (BRecord vm) = AIG.concat (flattenBValue <$> Map.elems vm)

liftCounterExamples' :: FiniteType -> S.StateT [Bool] (Either BBErr) (BValue Bool)
liftCounterExamples' shape =
  case shape of
    FTBit -> do
      bs' <- S.get
      case bs' of
        [] -> fail "liftCounterExamples': ran out of bits"
        b:rest -> S.put rest >> return (BBool b)
    FTVec n s ->
      (BVector . V.fromList) <$>
      replicateM (fromIntegral n) (liftCounterExamples' s)
    FTTuple ss -> BTuple <$> mapM liftCounterExamples' ss
    FTRec m -> BRecord <$> T.mapM liftCounterExamples' m

liftCounterExamples :: [FiniteType] -> [Bool]
                    -> Either BBErr [BValue Bool]
liftCounterExamples shapes bs = do
  (bvals, rest) <- S.runStateT (mapM liftCounterExamples' shapes) bs
  case rest of
    [] -> return bvals
    _  -> fail "liftCounterExamples: leftover bits"

liftCounterExample :: FiniteType -> [Bool] -> Either BBErr (BValue Bool)
liftCounterExample shape bs = do
  bvals <- liftCounterExamples [shape] bs
  case bvals of
    [bval] -> return bval
    _ -> fail "liftCounterExample: too many values"

liftConcreteBValue :: BValue Bool -> Term
liftConcreteBValue = go
  where
    go bval = Term . FTermF $
      case bval of
        BBool True -> CtorApp "Prelude.True" []
        BBool False -> CtorApp "Prelude.False" []
        BVector bvs ->
          ArrayValue (liftShape (getShape (V.head bvs))) (V.map go bvs)
        BTuple bvs -> TupleValue (map go bvs)
        BRecord m -> RecordValue (fmap go m)

liftShape :: FiniteType -> Term
liftShape = go
  where
    go bval = Term . FTermF $
      case bval of
        FTBit -> DataTypeApp "Prelude.Bool" []
        FTVec n es ->
          DataTypeApp "Prelude.Vec" [ Term . FTermF $ NatLit (fromIntegral n)
                                  , go es]
        FTTuple ss -> TupleType (map go ss)
        FTRec m -> RecordType (fmap go m)

type BBErr = String
type BBMonad = ErrorT BBErr IO

wrongArity :: (Show t) => String -> [t] -> BBMonad a
wrongArity s args =
  fail $ "wrong number or type of function arguments to " ++
         s ++ ": " ++ show args

----------------------------------------------------------------------

parseShape :: (Applicative m, Monad m) => SharedTerm t -> m FiniteType
parseShape (R.asBoolType -> Just ()) = return FTBit
parseShape (R.isVecType return -> Just (n R.:*: tp)) =
  FTVec n <$> parseShape tp
parseShape (R.asBitvectorType -> Just n) = pure (FTVec n FTBit)
parseShape (R.asTupleType -> Just ts) = FTTuple <$> traverse parseShape ts
parseShape (R.asRecordType -> Just tm) = FTRec <$> traverse parseShape tm
parseShape t = do
  fail $ "bitBlast: unsupported argument type: " ++ show t

-- | @checkShape s v@ verifies that @v@ has shape @s@.
checkShape :: Monad m => FiniteType -> BValue l -> m ()
checkShape FTBit BBool{} = return ()
checkShape (FTVec n tp) (BVector v) = do
  when (fromIntegral (V.length v) /= n) $ fail "Unexpected length"
  V.mapM_ (checkShape tp) v
checkShape (FTTuple tpl) (BTuple l) =
  zipWithM_ checkShape tpl l
checkShape (FTRec tpm) (BRecord m) = do
  when (Map.keysSet tpm /= Map.keysSet m) $ fail "Record keys don't match"
  zipWithM_ checkShape (Map.elems tpm) (Map.elems m)
checkShape _ _ = fail "Bitblast shape doesn't match."

getShape :: BValue l -> FiniteType
getShape (BBool _) = FTBit
getShape (BVector bvs)
  | V.null bvs = error "getShape: empty vector"
  | otherwise = FTVec (fromIntegral (V.length bvs)) (getShape (V.head bvs))
getShape (BTuple l) = FTTuple (map getShape l)
getShape (BRecord m) = FTRec (fmap getShape m)

newVars :: IsAIG l g => g s -> FiniteType -> IO (BValue (l s))
newVars be FTBit = BBool <$> AIG.newInput be
newVars be (FTVec n tp) = do
  BVector <$> V.replicateM (fromIntegral n) (newVars be tp)
newVars be (FTTuple ts) = BTuple <$> traverse (newVars be) ts
newVars be (FTRec tm ) = BRecord <$> traverse (newVars be) tm

bitBlast :: IsAIG l g => g s -> SharedTerm t -> IO (Either BBErr (BValue (l s)))
bitBlast be = bitBlastWithEnv be Map.empty

bitBlastWithEnv :: IsAIG l g
                => g s
                -> Map VarIndex (BValue (l s))
                -> SharedTerm t
                -> IO (Either BBErr (BValue (l s)))
bitBlastWithEnv be ecEnv (R.asLambdaList -> (args, rhs)) = do
  bc <- newBCache be (bvRulesWithEnv ecEnv)
  case runIdentity $ runErrorT $ traverse (parseShape . snd) args of
    Left msg -> return (Left msg)
    Right shapes -> do
      vars <- traverse (newVars be) shapes
      let bc' = bc { bcVarMap = Map.fromList ([0..] `zip` reverse vars) }
      bitBlastWith bc' rhs

data BCache t g (l :: * -> *) s
   = BCache { bcEngine :: !(g s)
            , bcValueNet :: Net (Rule t g l s (BValue (l s)))
            , bcTermCache :: !(IORef (Map TermIndex (BValue (l s))))
            , bcVarMap :: !(Map DeBruijnIndex (BValue (l s)))
            }

newBCache :: g s -> RuleSet t g l s -> IO (BCache t g l s)
newBCache be (RuleSet tr) = do
  tcache <- newIORef Map.empty
  let addRule rule = Net.insert_term (rule, rule)
  let valueNet = foldr addRule Net.empty tr
  return BCache { bcEngine = be
                , bcValueNet = valueNet
                , bcTermCache = tcache
                , bcVarMap = Map.empty
                }

addCut :: BCache t g l s -> SharedTerm t -> BValue (l s) -> IO ()
addCut _ (Unshared _) _ = error "FIXME: unimplemented addCut Unshared"
addCut bc (STApp t _) bits = do
  m <- readIORef (bcTermCache bc)
  when (Map.member t m) $
    fail "internal: addCut given term that has already been bitblasted."
  writeIORef (bcTermCache bc) $! Map.insert t bits m

tryMatch :: BCache t g l s
         -> SharedTerm t
         -> BBMonad (Maybe (BValue (l s)))
tryMatch bc t = liftIO $ go (Net.match_term (bcValueNet bc) t)
  where go [] = return Nothing
        go (rl:rls) = do
          mr <- runReaderT (unBB $ runMaybeT $ runMatcher rl t) bc
          case mr of
            Nothing -> go rls
            Just v -> return (Just v)

bitBlastWith :: forall t g l s
              . IsAIG l g
             => BCache t g l s
             -> SharedTerm t
             -> IO (Either BBErr (BValue (l s)))
bitBlastWith bc t0 = runErrorT (go t0)
  where be = bcEngine bc
        -- Bitblast term.
        go :: SharedTerm t -> BBMonad (BValue (l s))
        go (R.asCtor -> Just (ident, []))
          | ident == "Prelude.False" = return (BBool (AIG.falseLit be))
          | ident == "Prelude.True"  = return (BBool (AIG.trueLit be))
        go t@(Unshared _) = do
          mdef <- tryMatch bc t
          case mdef of
            Just r -> return r
            Nothing
              | (unwrapTermF -> FTermF (GlobalDef ident), xs) <- R.asApplyAll t
              , Just f <- Map.lookup ident opTable -> f be go xs
              | otherwise ->
                  fail $ show $
                   text "unsupported expression passed to bitBlast:" <$$>
                   indent 2 (scPrettyTermDoc t)
        go t@(STApp termidx _) = do
          let pushNew r = r <$ lift (addCut bc t r)
          m <- lift $ readIORef (bcTermCache bc)
          case Map.lookup termidx m of
           Just r -> return r
           Nothing -> do
            mdef <- tryMatch bc t
            case mdef of
             Just r -> pushNew r
             Nothing
              | (unwrapTermF -> FTermF (GlobalDef ident), xs) <- R.asApplyAll t
              , Just f <- Map.lookup ident opTable ->
                   pushNew =<< f be go xs
              | otherwise ->
                  fail $ show $
                   text "unsupported expression passed to bitBlast:" <$$>
                   indent 2 (scPrettyTermDoc t)

type BValueOp t g l s
  = g s
  -> (SharedTerm t -> BBMonad (BValue (l s)))
  -> [SharedTerm t]
  -> BBMonad (BValue (l s))

newtype Bitblaster t g l s a = BB { unBB :: ReaderT (BCache t g l s) IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadIO
           , MonadReader (BCache t g l s)
           )

blastAny :: IsAIG l g => SharedTerm t -> Bitblaster t g l s (BValue (l s))
blastAny t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Left msg -> fail msg
    Right v -> return v

blastWithShape :: IsAIG l g
               => FiniteType
               -> SharedTerm t
               -> Bitblaster t g l s (BValue (l s))
blastWithShape shape t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Left msg -> fail msg
    Right v -> v <$ checkShape shape v

blastBit :: IsAIG l g => SharedTerm t -> Bitblaster t g l s (l s)
blastBit t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Right (BBool l) -> return l
    Left msg -> fail msg -- Bitblast failed.
    Right{} -> fail "blastBit given bad term."

blastBV :: IsAIG l g
        => Nat
        -> SharedTerm t
        -> Bitblaster t g l s (LitVector (l s))
blastBV n t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Left msg -> fail msg -- Bitblast failed.
    Right v -> do
      lv <- asLitVector v
      when (fromIntegral (AIG.length lv) /= n) $ do
        fail $ "blastBit given bad vector (" ++
               show (AIG.length lv) ++ " vs " ++ show n ++
               "): " ++ show t ++ "."
      return lv
                                                       
type Rule t g l s = Matcher (RuleBlaster t g l s) (SharedTerm t)

-- HACK!
instance Eq (Rule t g l s a) where
  _ == _ = False

type RuleBlaster t g l s = MaybeT (Bitblaster t g l s)

data RuleSet t g l s = RuleSet { _valueRules :: [ Rule t g l s (BValue (l s)) ] }

instance Monoid (RuleSet t g l s) where
  mempty = RuleSet []
  mappend (RuleSet tx) (RuleSet ty) = RuleSet (tx ++ ty)

binBVRule :: forall t g l s
           . IsAIG l g
          => Ident
          -> (g s -> LitVector (l s) -> LitVector (l s) -> IO (LitVector (l s)))
          -> Rule t g l s (BValue (l s))
binBVRule d litFn = matchArgs (asGlobalDef d) termFn
  where termFn :: Nat -> SharedTerm t -> SharedTerm t -> RuleBlaster t g l s (BValue (l s))
        termFn n x y = lift $ do
          x' <- blastBV n x
          y' <- blastBV n y
          be <- asks bcEngine
          liftIO $ lvVector <$> litFn be x' y'

bvRelRule :: forall t g l s
           . IsAIG l g
          => Ident
          -> (g s -> LitVector (l s) -> LitVector (l s) -> IO (l s))
          -> Rule t g l s (BValue (l s))
bvRelRule d litFn = matchArgs (asGlobalDef d) termFn
  where termFn :: Nat
               -> SharedTerm t
               -> SharedTerm t
               -> RuleBlaster t g l s (BValue (l s))
        termFn n x y = lift $ do
          x' <- blastBV n x
          y' <- blastBV n y
          be <- asks bcEngine
          liftIO $ BBool <$> litFn be x' y'

bvRules :: IsAIG l g => RuleSet t g l s
bvRules = bvRulesWithEnv Map.empty

beFlip :: (g -> x -> y -> z)
       -> (g -> y -> x -> z)
beFlip f be x y = f be y x

bvRulesWithEnv :: forall t g l s
                . IsAIG l g
               => Map VarIndex (BValue (l s))
               -> RuleSet t g l s
bvRulesWithEnv ecEnv
  = termRule (asExtCns `thenMatcher` matchExtCns ecEnv)
  <> termRule bvNat_rule
  <> termRule (binBVRule "Prelude.bvAdd" AIG.add)
  <> termRule (binBVRule "Prelude.bvSub" AIG.sub)
  <> termRule (binBVRule "Prelude.bvMul" AIG.mul)
  <> termRule (binBVRule "Prelude.bvAnd" beAndInt)
  <> termRule (binBVRule "Prelude.bvOr"  beOrInt)
  <> termRule (binBVRule "Prelude.bvXor" beXorInt)
  <> termRule (binBVRule "Prelude.bvUDiv" AIG.uquot)
  <> termRule (binBVRule "Prelude.bvURem" AIG.urem)
  <> termRule (binBVRule "Prelude.bvSDiv" AIG.squot)
  <> termRule (binBVRule "Prelude.bvSRem" AIG.srem)
  -- Relations
  <> termRule (bvRelRule  "Prelude.bvEq"  AIG.bvEq)
  <> termRule (bvRelRule "Prelude.bvsle" AIG.sle)
  <> termRule (bvRelRule "Prelude.bvslt" AIG.slt)
  <> termRule (bvRelRule  "Prelude.bvule" AIG.ule)
  <> termRule (bvRelRule  "Prelude.bvult" AIG.ult)
  -- TODO: should we do an ordering normalization pass before bit blasting?
  <> termRule (bvRelRule "Prelude.bvsge" (beFlip AIG.sle))
  <> termRule (bvRelRule "Prelude.bvsgt" (beFlip AIG.slt))
  <> termRule (bvRelRule  "Prelude.bvuge" (beFlip AIG.ule))
  <> termRule (bvRelRule  "Prelude.bvugt" (beFlip AIG.ult))
  -- Shift
  <> termRule prelude_bvShl_bv
  <> termRule prelude_bvShl_nat
  <> termRule prelude_bvShr_bv
  <> termRule prelude_bvShr_nat
  <> termRule prelude_bvSShr_bv
  <> termRule prelude_bvSShr_nat

  <> termRule (asGlobalDef "Prelude.ite" `matchArgs` 
               (iteOp :: SharedTerm t
                      -> SharedTerm t
                      -> SharedTerm t
                      -> SharedTerm t
                      -> RuleBlaster t g l s (BValue (l s))))
  -- Primitives
  <> termRule (asLocalVar `thenMatcher` matchLocalVar)
  <> termRule (asAnyTupleValue `thenMatcher` matchTupleValue)
  <> termRule (asTupleSelector blastMatcher
                 `thenMatcher` uncurry bTupleSelect)
  <> termRule (asAnyRecordValue `thenMatcher` matchRecordValue)
  <> termRule (asRecordSelector blastMatcher
                 `thenMatcher` uncurry bRecordSelect)
  <> termRule (asAnyVecLit `thenMatcher` matchVecValue)

asBvToNat :: (Applicative m, Monad m, Termlike t) => Matcher m t (Nat :*: t)
asBvToNat = asGlobalDef "Prelude.bvToNat" <:>> asAnyNatLit <:> asAny

-- | Shift-left
-- Second argument may be (bvToNat _ x)
prelude_bvShl_bv :: IsAIG l g => Rule t g l s (BValue (l s))
prelude_bvShl_bv = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShl" <:>> asAnyNatLit <:> asAny <:> asBvToNat
        litFn (w :*: x :*: (w' :*: n)) = lift $ do
          x' <- blastBV w x
          assert (w == w') $ do
            n' <- blastBV w' n
            be <- asks bcEngine
            liftIO $ lvVector <$> AIG.shl be x' n'

-- | Shift-left
prelude_bvShl_nat :: IsAIG l g => Rule t g l s (BValue (l s))
prelude_bvShl_nat = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShl" <:>> asAnyNatLit <:> asAny <:> asAnyNatLit
        litFn (w :*: x :*: n) = lift $ do
          x' <- blastBV w x
          f <- AIG.falseLit <$> asks bcEngine
          return $ lvVector $ lvShl x' n f

-- | Unsigned shift-right
-- Second argument may be (bvToNat _ x)
prelude_bvShr_bv :: IsAIG l g => Rule t g l s (BValue (l s))
prelude_bvShr_bv = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShr" <:>> asAnyNatLit <:> asAny <:> asBvToNat
        litFn (w :*: x :*: (w' :*: n)) = lift $ do
          x' <- blastBV w x
          assert (w == w') $ do
            n' <- blastBV w' n
            be <- asks bcEngine
            liftIO $ lvVector <$> AIG.ushr be x' n'

-- | Unsigned shift-right
prelude_bvShr_nat :: IsAIG l g => Rule t g l s (BValue (l s))
prelude_bvShr_nat = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShr" <:>> asAnyNatLit <:> asAny <:> asAnyNatLit
        litFn (w :*: x :*: n) = lift $ do
          x' <- blastBV w x
          f <- AIG.falseLit <$> asks bcEngine
          return $ lvVector $ lvShr x' n f

-- | Signed shift-right
-- Second argument may be (bvToNat _ x)
prelude_bvSShr_bv :: IsAIG l g => Rule t g l s (BValue (l s))
prelude_bvSShr_bv = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvSShr" <:>> asAnyNatLit <:> asAny <:> asBvToNat
        litFn (w :*: x :*: (w' :*: n)) = lift $ do
          x' <- blastBV (w+1) x
          assert (w == w') $ do
            n' <- blastBV w' n
            be <- asks bcEngine
            liftIO $ lvVector <$> AIG.sshr be x' n'

-- | Signed shift-right
prelude_bvSShr_nat :: IsAIG l g => Rule t g l s (BValue (l s))
prelude_bvSShr_nat = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvSShr" <:>> asAnyNatLit <:> asAny <:> asAnyNatLit
        litFn (w :*: x :*: n) = lift $ do
          x' <- blastBV (w+1) x
          return $ lvVector $ lvShr x' n (AIG.msb x')

blastMatcher :: IsAIG l g => Matcher (RuleBlaster t g l s) (SharedTerm t) (BValue (l s))
blastMatcher = asVar $ \t -> lift (blastAny t)

instance Matchable (RuleBlaster t g l s) (SharedTerm t) FiniteType where
  defaultMatcher = asVar parseShape

matchExtCns :: IsAIG l g
            => Map VarIndex (BValue (l s)) 
            -> ExtCns (SharedTerm t)
            -> RuleBlaster t g l s (BValue (l s))
matchExtCns ecEnv ec =
  case Map.lookup (ecVarIndex ec) ecEnv of
    Just v -> return v
    Nothing -> lift $ do
      be <- asks bcEngine
      shape <- parseShape (ecType ec)
      liftIO (newVars be shape)

matchLocalVar :: DeBruijnIndex -> RuleBlaster t g l s (BValue (l s))
matchLocalVar i = lift $ do
  vm <- asks bcVarMap
  case Map.lookup i vm of
    Just v -> return v
    Nothing -> fail "Term contains unexpected free variable."

matchTupleValue :: IsAIG l g => [SharedTerm t] -> RuleBlaster t g l s (BValue (l s))
matchTupleValue m = lift $ BTuple <$> traverse blastAny m

matchRecordValue :: IsAIG l g
                 => Map FieldName (SharedTerm t)
                 -> RuleBlaster t g l s (BValue (l s))
matchRecordValue m = lift $ BRecord <$> traverse blastAny m

matchVecValue :: IsAIG l g
              => (SharedTerm t, V.Vector (SharedTerm t))
              -> RuleBlaster t g l s (BValue (l s))
matchVecValue (tp,v) = lift $ do
  shape <- parseShape tp
  BVector <$> V.mapM (blastWithShape shape) v

termRule :: Rule t g l s (BValue (l s)) -> RuleSet t g l s
termRule r = RuleSet [r]

opTable :: IsAIG l g => Map Ident (BValueOp t g l s)
opTable =
    Map.mapKeys (mkIdent preludeName) $
    Map.fromList $
    [ ("bvNot"    , bvNotOp     )
    , ("eq"       , equalOp     )
    , ("and"      , boolOp AIG.and)
    , ("xor"      , boolOp AIG.xor)
    , ("or"       , boolOp AIG.or )
    , ("boolEq"   , boolOp AIG.eq )
    , ("implies"  , boolOp AIG.implies)
    , ("not"      , notOp       )
    , ("append"   , appendOp    )
    , ("single"   , singleOp    )
    , ("bvTrunc"  , bvTruncOp   )
    , ("bvUExt"   , bvUExtOp    )
    , ("bvSExt"   , bvSExtOp    )
    , ("get"      , getOp       )
    , ("set"      , setOp       )
    , ("replicate", replicateOp )
    , ("slice"    , bvSliceOp   )
    , ("join"     , joinOp      )
    , ("split"    , splitOp     )
    , ("reverse"  , reverseOp   )
    ]

boolOp :: (g s -> l s -> l s -> IO (l s)) -> BValueOp t g l s
boolOp f be eval [mx, my] =
    do x <- asBBool =<< eval mx
       y <- asBBool =<< eval my
       liftIO (fmap BBool (f be x y))
boolOp _ _ _ args = wrongArity "boolean op" args

equalOp :: IsAIG l g => BValueOp t g l s
equalOp be eval [R.asBoolType -> Just (), mx, my] = boolOp AIG.eq be eval [mx, my]
equalOp be eval [_, mx, my] =
    do x <- flattenBValue <$> eval mx
       y <- flattenBValue <$> eval my
       liftIO $ BBool <$> AIG.bvEq be x y
equalOp _ _ args = wrongArity "equality op" args

bvNat_rule :: IsAIG l g => Rule t g l s (BValue (l s))
bvNat_rule = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvNat" <:>> asAnyNatLit <:> asAnyNatLit
        litFn (w :*: x) = do
          be <- asks bcEngine
          return (lvVector (AIG.bvFromInteger be (fromIntegral w) (toInteger x)))

notOp :: IsLit l => BValueOp t g l s
notOp _ eval [mx] =
    do x <- asBBool =<< eval mx
       return (BBool (AIG.not x))
notOp _ _ args = wrongArity "not op" args

bvNotOp :: IsLit l => BValueOp t g l s
bvNotOp _ eval [_, mx] =
    do x <- asLitVector =<< eval mx
       return (lvVector (AIG.not <$> x))
bvNotOp _ _ args = wrongArity "bvNot op" args

appendOp :: BValueOp t g l s
appendOp _ eval [_, _, _, mx, my] =
    do x <- asLitVector =<< eval mx
       y <- asLitVector =<< eval my
       return (lvVector (x AIG.++ y))
appendOp _ _ args = wrongArity "append op" args

singleOp :: BValueOp t g l s
singleOp _ eval [_, mx] =
    do x <- asBBool =<< eval mx
       return (lvVector (AIG.replicate 1 x))
singleOp _ _ args = wrongArity "single op" args

iteOp :: IsAIG l g
      => SharedTerm t
      -> SharedTerm t
      -> SharedTerm t
      -> SharedTerm t
      -> RuleBlaster t g l s (BValue (l s))
iteOp tp mb mx my = lift $ do
  shape <- parseShape tp
  b <- blastBit mb
  be <- asks bcEngine
  case () of
    _ | b AIG.=== AIG.trueLit be -> blastWithShape shape mx
      | b AIG.=== AIG.falseLit be -> blastWithShape shape my
      | otherwise -> do
            x <- blastWithShape shape mx
            y <- blastWithShape shape my
            liftIO $ iteFn be b x y

--iteFn :: BitEngine l -> l -> BValue l -> BValue l -> IO (BValue l)
iteFn :: IsAIG l g =>
         g s -> l s -> BValue (l s) -> BValue (l s) -> IO (BValue (l s))
iteFn be b (BBool x) (BBool y) = BBool <$> AIG.mux be b x y
iteFn be b (BVector x) (BVector y)
  | V.length x == V.length y
  = BVector <$> V.zipWithM (iteFn be b) x y
iteFn be b (BTuple x) (BTuple y)
  | length x == length y
  = BTuple <$> zipWithM (iteFn be b) x y
iteFn be b (BRecord x) (BRecord y)
  | Map.keys x == Map.keys y
  = fmap BRecord $ sequenceOf traverse
    $ Map.intersectionWith (iteFn be b) x y
iteFn _ _ _ _ = fail "malformed arguments."

bvTruncOp :: BValueOp t g l s
bvTruncOp _ eval [mi, mj, mx] =
    do i <- fromIntegral <$> asBNat mi "Trunc"
       j <- fromIntegral <$> asBNat mj "Trunc"
       x <- asLitVector =<< eval mx
       return (lvVector (AIG.slice x i j))
bvTruncOp _ _ args = wrongArity "trunc op" args

bvUExtOp :: IsAIG l g => BValueOp t g l s
bvUExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi "UExt"
       j <- asBNat mj "UExt"
       x <- asLitVector =<< eval mx
       return $ lvVector $ AIG.zext be x (fromIntegral (i + j))
bvUExtOp _ _ args = wrongArity "UExt op" args

bvSExtOp :: IsAIG l g => BValueOp t g l s
bvSExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi "SExt"
       j <- asBNat mj "SExt"
       x <- asLitVector =<< eval mx
       return $ lvVector $ AIG.sext be x (fromIntegral (i + j + 1))
bvSExtOp _ _ args = wrongArity "SExt op" args

getOp :: IsAIG l g => BValueOp t g l s
getOp be eval [mn, _mty, mv, mf] =
    do n <- asBNat mn "get"
       let vecOp (BVector v) i = (V.!) v (fromIntegral i)
           vecOp _ _ = error "vecOp applied to non-vector"
       v <- eval mv
       case R.asCtor mf of
         Just ("Prelude.FinVal", [R.asNatLit -> Just i, _]) -> do
           return (vecOp v i)
         Just ("Prelude.FinVal",
               [ R.asApplyAll -> (R.isGlobalDef "Prelude.bvToNat" -> Just (),
                                  [wt, it])
               , _
               ]) -> do
           w <- asBNat wt "get"
           iv <- eval it
           let def = lvVector (AIG.bvFromInteger be (fromIntegral w) 0)
           liftIO $ symIdx be vecOp n v iv  def
         _ -> fail $ "get: invalid index: " ++ show mf
getOp _ _ args = wrongArity "get op" args

-- set :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e -> Vec n e;
setOp :: IsAIG l g => BValueOp t g l s
setOp be eval [mn, _me, mv, mf, mx] =
    do n <- asBNat mn "set"
       x <- eval mx
       let vecOp (BVector v) i = BVector ((V.//) v [(fromIntegral i, x)])
           vecOp _ _ = error "vecOp applied to non-vector"
       v <- eval mv
       case R.asCtor mf of
         Just ("Prelude.FinVal", [R.asNatLit -> Just i, _]) -> do
           return (vecOp v i)
         Just ("Prelude.FinVal",
               [ R.asApplyAll -> (R.isGlobalDef "Prelude.bvToNat" -> Just (),
                                  [_wt, it])
               , _
               ]) -> do
           -- w <- asBNat wt "get"
           iv <- eval it
           liftIO $ symIdx be vecOp n v iv v
         _ -> fail $ "set: invalid index: " ++ show mf
setOp _ _ args = wrongArity "set op" args

symIdx :: (IsAIG l g) =>
          g s
       -> (BValue (l s) -> Nat -> BValue (l s))
       -> Nat
       -> BValue (l s)
       -> BValue (l s)
       -> BValue (l s)
       -> IO (BValue (l s))
symIdx be concOp n v i def = go 0
  where
    go j | j < n =
           do let iv = flattenBValue i
                  jv = AIG.bvFromInteger be (AIG.length iv) (fromIntegral n)
              eqLit <- AIG.bvEq be jv iv
              fv <- go (j + 1)
              iteFn be eqLit (concOp v j) fv
         | otherwise = return def

-- replicate :: (n :: Nat) -> (e :: sort 0) -> e -> Vec n e;
replicateOp :: BValueOp t g l s
replicateOp _be eval [mn, _me, mx] =
    do n <- fromIntegral <$> asBNat mn "replicate"
       x <- eval mx
       return (BVector (V.replicate n x))
replicateOp _ _ args = wrongArity "replicate op" args

bvSliceOp :: BValueOp t g l s
bvSliceOp _ eval [_, mi, mn, _, mx] =
    do i <- fromIntegral <$> asBNat mi "slice"
       n <- fromIntegral <$> asBNat mn "slice"
       x <- asLitVector =<< eval mx
       return (lvVector (AIG.slice x i n))
bvSliceOp _ _ args = wrongArity "slice op" args

joinOp :: BValueOp t g l s
joinOp _ eval [mm, mn, _me, mv] =
    do v <- eval mv
       m <- fromIntegral <$> asBNat mm "join"
       n <- fromIntegral <$> asBNat mn "join"
       checkShape (FTVec m (FTVec n FTBit)) v
       return (lvVector (flattenBValue v))
joinOp _ _ args = wrongArity "join op" args

chunk :: Int -> V.Vector a -> V.Vector (V.Vector a)
chunk n v | V.length v <= n = V.singleton v
          | otherwise = V.cons (V.take n v) (chunk n (V.drop n v))

splitOp :: BValueOp t g l s
splitOp _ eval [mm, mn, _me, mv] =
    do v <- eval mv
       m <- fromIntegral <$> asBNat mm "split"
       n <- fromIntegral <$> asBNat mn "split"
       checkShape (FTVec (m * n) FTBit) v
       lv <- asBVector v
       let lvParts = chunk (fromIntegral n) lv
           bvs = BVector (V.map BVector lvParts)
       checkShape (FTVec m (FTVec n FTBit)) bvs
       return bvs
splitOp _ _ args = wrongArity "split op" args

reverseOp :: BValueOp t g l s
reverseOp _ eval [_mn, _me, mv] =
    do v <- eval mv
       case v of
         (BVector v') -> return . BVector . V.reverse $ v'
         _ -> fail "reverse applied to non-vector"
reverseOp _ _ args = wrongArity "reverse op" args

----------------------------------------------------------------------
-- Destructors for BValues

asLitVector :: (Functor m, Monad m) => BValue l -> m (LitVector l)
asLitVector (BVector v) = lvFromV <$> V.mapM asBBool v
asLitVector _ = fail "expected Vector"

asBVector :: (Functor m, Monad m) => BValue l -> m (V.Vector (BValue l))
asBVector (BVector v) = return v
asBVector _ = fail "expected Vector"

asBBool :: Monad m => BValue l -> m l
asBBool (BBool l) = return l
asBBool _ = fail "expected Bool"

asBNat :: SharedTerm t -> String -> BBMonad Nat
asBNat t desc =
    case R.asNatLit t of
      Just n -> return n
      Nothing ->
        fail $ "expected NatLit (got " ++ show t ++ ") in argument to " ++ desc
