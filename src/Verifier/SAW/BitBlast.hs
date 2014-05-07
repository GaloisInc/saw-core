{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.BitBlast
  ( BValue(..)
  , flattenBValue
  , bitBlast
  , bitBlastWithEnv
  , lvVector
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
    -- * Standard prelude bitvecot rules.
  , bvRules
     -- * Re-exports
  , (<>)
  , Matcher
  , Renderable
  , Termlike
  , matchArgs
  ) where

import Control.Applicative
import Control.Exception (assert)
import Control.Lens
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Trans.Error
import Control.Monad.Trans.Maybe
import Data.Foldable (Foldable)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Vector as V
import qualified Data.Vector.Storable as LV
import Text.PrettyPrint.Leijen hiding ((<$>), (<>))

import Verifier.SAW.Prim
import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.Rewriter ()
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.TermNet as Net 
import Verifier.SAW.TypedAST
import Verinf.Symbolic.Lit
import Verifier.SAW.Export.SMT.Common

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

lvVector :: LV.Storable l => LitVector l -> BValue l
lvVector lv = BVector v 
  where v = V.generate (LV.length lv) (\i -> BBool (lv LV.! i)) 

lvFromV :: LV.Storable l => V.Vector l -> LV.Vector l
lvFromV v = LV.generate (V.length v) (v V.!)
  
flattenBValue :: LV.Storable l => BValue l -> LitVector l
flattenBValue (BBool l) = LV.singleton l
flattenBValue (BVector v) = LV.concat (flattenBValue <$> V.toList v)
flattenBValue (BTuple vs) = LV.concat (flattenBValue <$> vs)
flattenBValue (BRecord vm) = LV.concat (flattenBValue <$> Map.elems vm)

type BBErr = String
type BBMonad = ErrorT BBErr IO

wrongArity :: (Show t) => String -> [t] -> BBMonad a
wrongArity s args =
  fail $ "wrong number or type of function arguments to " ++
         s ++ ": " ++ show args

----------------------------------------------------------------------

-- | Describes an expected shape that a bitblasted
-- term is expected to have.  Used for typechecking during
-- bitblasting.
data BShape 
   = BoolShape
   | VecShape Nat BShape
   | TupleShape [BShape]
   | RecShape (Map FieldName BShape)

parseShape :: (Applicative m, Monad m) => SharedTerm s -> m BShape
parseShape (R.asBoolType -> Just ()) = return BoolShape
parseShape (R.isVecType return -> Just (n R.:*: tp)) =
  VecShape n <$> parseShape tp
parseShape (R.asBitvectorType -> Just n) = pure (VecShape n BoolShape)
parseShape (R.asTupleType -> Just ts) = TupleShape <$> traverse parseShape ts
parseShape (R.asRecordType -> Just tm) = RecShape <$> traverse parseShape tm
parseShape t = do
  fail $ "bitBlast: unsupported argument type: " ++ show t

-- | @checkShape s v@ verifies that @v@ has shape @s@.
checkShape :: Monad m => BShape -> BValue l -> m ()
checkShape BoolShape BBool{} = return ()
checkShape (VecShape n tp) (BVector v) = do
  when (fromIntegral (V.length v) /= n) $ fail "Unexpected length"
  V.mapM_ (checkShape tp) v
checkShape (TupleShape tpl) (BTuple l) =
  zipWithM_ checkShape tpl l
checkShape (RecShape tpm) (BRecord m) = do
  when (Map.keysSet tpm /= Map.keysSet m) $ fail "Record keys don't match"
  zipWithM_ checkShape (Map.elems tpm) (Map.elems m)
checkShape _ _ = fail "Bitblast shape doesn't match."

newVars :: BitEngine l -> BShape -> IO (BValue l)
newVars be BoolShape = BBool <$> beMakeInputLit be
newVars be (VecShape n tp) = do
  BVector <$> V.replicateM (fromIntegral n) (newVars be tp)
newVars be (TupleShape ts) = BTuple <$> traverse (newVars be) ts
newVars be (RecShape tm ) = BRecord <$> traverse (newVars be) tm

bitBlast :: (Eq l, LV.Storable l) => BitEngine l -> SharedTerm s -> IO (Either BBErr (BValue l))
bitBlast be = bitBlastWithEnv be Map.empty

bitBlastWithEnv :: (Eq l, LV.Storable l) => BitEngine l -> Map VarIndex (BValue l)
                -> SharedTerm s -> IO (Either BBErr (BValue l))
bitBlastWithEnv be ecEnv (R.asLambdaList -> (args, rhs)) = do
  bc <- newBCache be (bvRulesWithEnv ecEnv)
  case runIdentity $ runErrorT $ traverse (parseShape . snd) args of
    Left msg -> return (Left msg)
    Right shapes -> do
      vars <- traverse (newVars be) shapes
      let bc' = bc { bcVarMap = Map.fromList ([0..] `zip` reverse vars) }
      bitBlastWith bc' rhs

data BCache s l = BCache { bcEngine :: !(BitEngine l)
                         , bcValueNet :: Net (Rule s l (BValue l))
                         , bcTermCache :: !(IORef (Map TermIndex (BValue l)))
                         , bcVarMap :: !(Map DeBruijnIndex (BValue l))
                         }

newBCache :: (LV.Storable l) => BitEngine l -> RuleSet s l -> IO (BCache s l)
newBCache be (RuleSet tr) = do
  tcache <- newIORef Map.empty
  let addRule rule = Net.insert_term (rule, rule)
  let valueNet = foldr addRule Net.empty tr
  return BCache { bcEngine = be
                , bcValueNet = valueNet
                , bcTermCache = tcache
                , bcVarMap = Map.empty
                }

addCut :: BCache s l -> SharedTerm s -> BValue l -> IO ()
addCut bc (STApp t _) bits = do
  m <- readIORef (bcTermCache bc)
  when (Map.member t m) $
    fail "internal: addCut given term that has already been bitblasted."
  writeIORef (bcTermCache bc) $! Map.insert t bits m

tryMatch :: BCache s l
         -> SharedTerm s
         -> BBMonad (Maybe (BValue l))
tryMatch bc t = liftIO $ go (Net.match_term (bcValueNet bc) t)
  where go [] = return Nothing
        go (rl:rls) = do
          mr <- runReaderT (unBB $ runMaybeT $ runMatcher rl t) bc
          case mr of
            Nothing -> go rls
            Just v -> return (Just v)

bitBlastWith :: forall l s. (Eq l, LV.Storable l)
             => BCache s l -> SharedTerm s -> IO (Either BBErr (BValue l))
bitBlastWith bc t0 = runErrorT (go t0)
  where be = bcEngine bc
        -- Bitblast term.
        go :: SharedTerm s -> BBMonad (BValue l)
        go (R.asCtor -> Just (ident, []))
          | ident == "Prelude.False" = return (BBool (beFalse be))
          | ident == "Prelude.True"  = return (BBool (beTrue be))
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
              | (STApp _ (FTermF (GlobalDef ident)), xs) <- R.asApplyAll t
              , Just f <- Map.lookup ident opTable ->
                   pushNew =<< f be go xs
              | otherwise ->
                  fail $ show $ 
                   text "unsupported expression passed to bitBlast:" <$$>
                   indent 2 (scPrettyTermDoc t)

type BValueOp s l
  = BitEngine l
  -> (SharedTerm s -> BBMonad (BValue l))
  -> [SharedTerm s]
  -> BBMonad (BValue l)

newtype Bitblaster s l a = BB { unBB :: ReaderT (BCache s l) IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader (BCache s l))

blastAny :: (Eq l, LV.Storable l)
         => SharedTerm s
         -> Bitblaster s l (BValue l)
blastAny t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Left msg -> fail msg
    Right v -> return v

blastWithShape :: (Eq l, LV.Storable l)
               => BShape -> SharedTerm s -> Bitblaster s l (BValue l)
blastWithShape shape t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Left msg -> fail msg 
    Right v -> v <$ checkShape shape v

blastBit :: (Eq l, LV.Storable l) => SharedTerm s -> Bitblaster s l l
blastBit t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Right (BBool l) -> return l
    Left msg -> fail msg -- Bitblast failed.
    Right{} -> fail "blastBit given bad term."

blastBV :: (Eq l, LV.Storable l)
        => Nat -> SharedTerm s -> Bitblaster s l (LV.Vector l)
blastBV n t = do
  bc <- ask
  mr <- liftIO $ bitBlastWith bc t
  case mr of
    Left msg -> fail msg -- Bitblast failed.
    Right v -> do
      lv <- asLitVector v
      when (fromIntegral (LV.length lv) /= n) $ do
        fail $ "blastBit given bad vector (" ++
               show (LV.length lv) ++ " vs " ++ show n ++
               "): " ++ show t ++ "."
      return lv
                                                       
type Rule s l = Matcher (RuleBlaster s l) (SharedTerm s)

-- HACK!
instance Eq (Rule s l a) where
  _ == _ = False

type RuleBlaster s l = MaybeT (Bitblaster s l)

data RuleSet s l = RuleSet { _valueRules :: [ Rule s l (BValue l) ] }

instance Monoid (RuleSet s l) where
  mempty = RuleSet []
  mappend (RuleSet tx) (RuleSet ty) = RuleSet (tx ++ ty)

binBVRule :: forall s l
           . (Eq l, LV.Storable l)
          => Ident
          -> (BitEngine l -> LitVector l -> LitVector l -> IO (LitVector l))
          -> Rule s l (BValue l)
binBVRule d litFn = matchArgs (asGlobalDef d) termFn
  where termFn :: Nat -> SharedTerm s -> SharedTerm s -> RuleBlaster s l (BValue l)
        termFn n x y = lift $ do
          x' <- blastBV n x
          y' <- blastBV n y
          be <- asks bcEngine
          liftIO $ lvVector <$> litFn be x' y'

bvRelRule :: forall s l
           . (Eq l, LV.Storable l)
          => Ident
          -> (BitEngine l -> LitVector l -> LitVector l -> IO l)
          -> Rule s l (BValue l)
bvRelRule d litFn = matchArgs (asGlobalDef d) termFn
  where termFn :: Nat -> SharedTerm s -> SharedTerm s
               -> RuleBlaster s l (BValue l)
        termFn n x y = lift $ do
          x' <- blastBV n x
          y' <- blastBV n y
          be <- asks bcEngine
          liftIO $ BBool <$> litFn be x' y'

bvSRelRule :: forall s l
            . (Eq l, LV.Storable l)
           => Ident
           -> (BitEngine l -> LitVector l -> LitVector l -> IO l)
           -> Rule s l (BValue l)
bvSRelRule d litFn = matchArgs (asGlobalDef d) termFn
  where termFn :: Nat -> SharedTerm s -> SharedTerm s
               -> RuleBlaster s l (BValue l)
        termFn n x y = lift $ do
          let n' = n + 1
          x' <- blastBV n' x
          y' <- blastBV n' y
          be <- asks bcEngine
          liftIO $ BBool <$> litFn be x' y'

bvRules :: forall s l . (Eq l, LV.Storable l) => RuleSet s l
bvRules = bvRulesWithEnv Map.empty

beFlip :: (BitEngine l -> LitVector l -> LitVector l -> IO l)
       -> (BitEngine l -> LitVector l -> LitVector l -> IO l)
beFlip f be x y = f be y x

bvRulesWithEnv :: forall s l . (Eq l, LV.Storable l) => Map VarIndex (BValue l) -> RuleSet s l
bvRulesWithEnv ecEnv
  = termRule (asExtCns `thenMatcher` matchExtCns ecEnv)
  <> termRule bvNat_rule
  <> termRule (binBVRule "Prelude.bvAdd" beAddInt)
  <> termRule (binBVRule "Prelude.bvSub" beSubInt)
  <> termRule (binBVRule "Prelude.bvMul" beMulInt)
  <> termRule (binBVRule "Prelude.bvAnd" beAndInt)
  <> termRule (binBVRule "Prelude.bvOr"  beOrInt)
  <> termRule (binBVRule "Prelude.bvXor" beXorInt)
  <> termRule (binBVRule "Prelude.bvUDiv" beQuotUnsigned)
  <> termRule (binBVRule "Prelude.bvURem" beRemUnsigned)
  <> termRule (binBVRule "Prelude.bvSDiv" beQuot)
  <> termRule (binBVRule "Prelude.bvSRem" beRem)
  -- Relations
  <> termRule (bvRelRule  "Prelude.bvEq"  beEqVector)
  <> termRule (bvSRelRule "Prelude.bvsle" beSignedLeq)
  <> termRule (bvSRelRule "Prelude.bvslt" beSignedLt)
  <> termRule (bvRelRule  "Prelude.bvule" beUnsignedLeq)
  <> termRule (bvRelRule  "Prelude.bvult" beUnsignedLt)
  -- TODO: should we do an ordering normalization pass before bit blasting?
  <> termRule (bvSRelRule "Prelude.bvsge" (beFlip beSignedLeq))
  <> termRule (bvSRelRule "Prelude.bvsgt" (beFlip beSignedLt))
  <> termRule (bvRelRule  "Prelude.bvuge" (beFlip beUnsignedLeq))
  <> termRule (bvRelRule  "Prelude.bvugt" (beFlip beUnsignedLt))
  -- Shift
  <> termRule prelude_bvShl_bv_lsb
  <> termRule prelude_bvShl_nat_lsb
  <> termRule prelude_bvShr_bv_lsb
  <> termRule prelude_bvShr_nat_lsb
  <> termRule prelude_bvSShr_bv_lsb
  <> termRule prelude_bvSShr_nat_lsb

  <> termRule (asGlobalDef "Prelude.ite" `matchArgs` 
               (iteOp :: SharedTerm s
                      -> SharedTerm s
                      -> SharedTerm s
                      -> SharedTerm s
                      -> RuleBlaster s l (BValue l)))
  -- Primitives
  <> termRule (asLocalVar `thenMatcher` matchLocalVar)
  <> termRule (asAnyTupleValue              `thenMatcher` matchTupleValue)
  <> termRule (asTupleSelector blastMatcher
                 `thenMatcher` uncurry bTupleSelect)
  <> termRule (asAnyRecordValue `thenMatcher` matchRecordValue)
  <> termRule (asRecordSelector blastMatcher
                 `thenMatcher` uncurry bRecordSelect)
  <> termRule (asAnyVecLit `thenMatcher` matchVecValue)

lvShl :: LV.Storable l => LV.Vector l ->  Nat -> l -> LV.Vector l
lvShl v i l = LV.replicate j l LV.++ LV.take (n-j) v
  where n = LV.length v
        j = fromIntegral i `min` n

lvShr :: LV.Storable l => LV.Vector l ->  Nat -> l -> LV.Vector l
lvShr v i l = LV.drop j v LV.++ LV.replicate j l
  where j = fromIntegral i `min` LV.length v

asBvToNat :: (Applicative m, Monad m, Termlike t) => Matcher m t (Nat :*: t)
asBvToNat = asGlobalDef "Prelude.bvToNat" <:>> asAnyNatLit <:> asAny

-- | Shift-left; Least-significant bit first implementation.
-- Second argument may be (bvToNat _ x)
prelude_bvShl_bv_lsb :: (Eq l, LV.Storable l) => Rule s l (BValue l)
prelude_bvShl_bv_lsb = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShl" <:>> asAnyNatLit <:> asAny <:> asBvToNat
        litFn (w :*: x :*: (w' :*: n)) = lift $ do
          x' <- blastBV w x
          assert (w == w') $ do
            n' <- blastBV w' n
            be <- asks bcEngine
            liftIO $ lvVector <$> beShl be x' n'

-- | Shift-left; Least-significant bit first implementation.
prelude_bvShl_nat_lsb :: (Eq l, LV.Storable l) => Rule s l (BValue l)
prelude_bvShl_nat_lsb = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShl" <:>> asAnyNatLit <:> asAny <:> asAnyNatLit
        litFn (w :*: x :*: n) = lift $ do
          x' <- blastBV w x
          f <- beFalse <$> asks bcEngine
          return $ lvVector $ lvShl x' n f

-- | Unsigned shift-right; Least-significant bit first implementation.
-- Second argument may be (bvToNat _ x)
prelude_bvShr_bv_lsb :: (Eq l, LV.Storable l) => Rule s l (BValue l)
prelude_bvShr_bv_lsb = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShr" <:>> asAnyNatLit <:> asAny <:> asBvToNat
        litFn (w :*: x :*: (w' :*: n)) = lift $ do
          x' <- blastBV w x
          assert (w == w') $ do
            n' <- blastBV w' n
            be <- asks bcEngine
            liftIO $ lvVector <$> beUnsignedShr be x' n'

-- | Unsigned shift-right; Least-significant bit first implementation.
prelude_bvShr_nat_lsb :: (Eq l, LV.Storable l) => Rule s l (BValue l)
prelude_bvShr_nat_lsb = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvShr" <:>> asAnyNatLit <:> asAny <:> asAnyNatLit
        litFn (w :*: x :*: n) = lift $ do
          x' <- blastBV w x
          f <- beFalse <$> asks bcEngine
          return $ lvVector $ lvShr x' n f

-- | Signed shift-right; Least-significant bit first implementation.
-- Second argument may be (bvToNat _ x)
prelude_bvSShr_bv_lsb :: (Eq l, LV.Storable l) => Rule s l (BValue l)
prelude_bvSShr_bv_lsb = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvSShr" <:>> asAnyNatLit <:> asAny <:> asBvToNat
        litFn (w :*: x :*: (w' :*: n)) = lift $ do
          x' <- blastBV (w+1) x
          assert (w == w') $ do
            n' <- blastBV w' n
            be <- asks bcEngine
            liftIO $ lvVector <$> beSignedShr be x' n'

-- | Signed shift-right; Least-significant bit first implementation.
prelude_bvSShr_nat_lsb :: (Eq l, LV.Storable l) => Rule s l (BValue l)
prelude_bvSShr_nat_lsb = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvSShr" <:>> asAnyNatLit <:> asAny <:> asAnyNatLit
        litFn (w :*: x :*: n) = lift $ do
          x' <- blastBV (w+1) x
          let msb = LV.last x'
          return $ lvVector $ lvShr x' n msb

blastMatcher :: (Eq l, LV.Storable l) => Matcher (RuleBlaster s l) (SharedTerm s) (BValue l)
blastMatcher = asVar $ \t -> lift (blastAny t)

instance Matchable (RuleBlaster s l) (SharedTerm s) BShape where
  defaultMatcher = asVar parseShape

matchExtCns :: Map VarIndex (BValue l) -> ExtCns (SharedTerm s) -> RuleBlaster s l (BValue l)
matchExtCns ecEnv ec =
  case Map.lookup (ecVarIndex ec) ecEnv of
    Just bv -> return bv
    Nothing -> lift $ do
      be <- asks bcEngine
      shape <- parseShape (ecType ec)
      liftIO (newVars be shape)

matchLocalVar :: DeBruijnIndex -> RuleBlaster s l (BValue l)
matchLocalVar i = lift $ do
  vm <- asks bcVarMap
  case Map.lookup i vm of
    Just v -> return v
    Nothing -> fail "Term contains unexpected free variable."

matchTupleValue :: (Eq l, LV.Storable l) => [SharedTerm s] -> RuleBlaster s l (BValue l)
matchTupleValue m = lift $ BTuple <$> traverse blastAny m

matchRecordValue :: (Eq l, LV.Storable l)
                 => Map FieldName (SharedTerm s) -> RuleBlaster s l (BValue l)
matchRecordValue m = lift $ BRecord <$> traverse blastAny m


matchVecValue :: (Eq l, LV.Storable l)
              => (SharedTerm s, V.Vector (SharedTerm s))
              -> RuleBlaster s l (BValue l)
matchVecValue (tp,v) = lift $ do
  shape <- parseShape tp
  BVector <$> V.mapM (blastWithShape shape) v

termRule :: Rule s l (BValue l) -> RuleSet s l
termRule r = RuleSet [r]

opTable :: (Eq l, LV.Storable l) => Map Ident (BValueOp s l)
opTable =
    Map.mapKeys (mkIdent preludeName) $
    Map.fromList $
    [ ("bvNot"    , bvNotOp     )
    , ("eq"       , equalOp     )
    , ("and"      , boolOp beAnd)
    , ("xor"      , boolOp beXor)
    , ("or"       , boolOp beOr )
    , ("boolEq"   , boolOp beEq )
    , ("implies"  , boolOp beImplies)
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
    ]

bvRelOp :: (LV.Storable l)
        => (BitEngine l -> LitVector l -> LitVector l -> IO l)
        -> BValueOp s l
bvRelOp f be eval [_, mx, my] =
    do x <- asLitVector =<< eval mx
       y <- asLitVector =<< eval my
       liftIO $ BBool <$> f be x y
bvRelOp _ _ _ args = wrongArity "relational op" args

boolOp :: (BitEngine l -> l -> l -> IO l) -> BValueOp s l
boolOp f be eval [mx, my] =
    do x <- asBBool =<< eval mx
       y <- asBBool =<< eval my
       liftIO (fmap BBool (f be x y))
boolOp _ _ _ args = wrongArity "boolean op" args

equalOp :: (Eq l, LV.Storable l) => BValueOp s l
equalOp be eval [R.asBoolType -> Just (), mx, my] = boolOp beEq be eval [mx, my]
equalOp be eval [_, mx, my] =
    do x <- flattenBValue <$> eval mx
       y <- flattenBValue <$> eval my
       liftIO $ BBool <$> beEqVector be x y
equalOp _ _ args = wrongArity "equality op" args

bvNat_rule :: LV.Storable l => Rule s l (BValue l)
bvNat_rule = pat `thenMatcher` litFn
  where pat = asGlobalDef "Prelude.bvNat" <:>> asAnyNatLit <:> asAnyNatLit
        litFn (w :*: x) = do
          be <- asks bcEngine
          return (lvVector (beVectorFromInt be (fromIntegral w) (toInteger x)))

notOp :: BValueOp s l
notOp be eval [mx] =
    do x <- asBBool =<< eval mx
       return (BBool (beNeg be x))
notOp _ _ args = wrongArity "not op" args

bvNotOp :: LV.Storable l => BValueOp s l
bvNotOp be eval [_, mx] =
    do x <- asLitVector =<< eval mx
       return (lvVector (LV.map (beNeg be) x))
bvNotOp _ _ args = wrongArity "bvNot op" args

appendOp :: LV.Storable l => BValueOp s l
appendOp _ eval [_, _, _, mx, my] =
    do x <- asLitVector =<< eval mx
       y <- asLitVector =<< eval my
       return (lvVector ((LV.++) x y))
appendOp _ _ args = wrongArity "append op" args

singleOp :: LV.Storable l => BValueOp s l
singleOp _ eval [_, mx] =
    do x <- asBBool =<< eval mx
       return (lvVector (LV.singleton x))
singleOp _ _ args = wrongArity "single op" args

iteOp :: (Eq l, LV.Storable l)
      => SharedTerm s -> SharedTerm s -> SharedTerm s -> SharedTerm s
      -> RuleBlaster s l (BValue l)
iteOp tp mb mx my = lift $ do
  shape <- parseShape tp
  b <- blastBit mb
  be <- asks bcEngine
  case () of
    _ | beEqLit be b (beTrue be) -> blastWithShape shape mx
      | beEqLit be b (beFalse be) -> blastWithShape shape my
      | otherwise -> do
            x <- blastWithShape shape mx
            y <- blastWithShape shape my
            liftIO $ iteFn x y
          where iteFn (BBool x) (BBool y) = BBool <$> beMux be b x y
                iteFn (BVector x) (BVector y)
                  | V.length x == V.length y
                  = BVector <$> V.zipWithM iteFn x y
                iteFn (BTuple x) (BTuple y)
                  | length x == length y
                  = BTuple <$> zipWithM iteFn x y
                iteFn (BRecord x) (BRecord y)
                  | Map.keys x == Map.keys y
                  = fmap BRecord $ sequenceOf traverse 
                                 $ Map.intersectionWith iteFn x y
                iteFn _ _ = fail "malformed arguments."

bvTruncOp :: (Eq l, LV.Storable l) => BValueOp s l
bvTruncOp be eval [_, mj, mx] =
    do j <- asBNat mj
       x <- asLitVector =<< eval mx
       return (lvVector (beTrunc be (fromIntegral j) x))
bvTruncOp _ _ args = wrongArity "trunc op" args

bvUExtOp :: (Eq l, LV.Storable l) => BValueOp s l
bvUExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi
       j <- asBNat mj
       x <- asLitVector =<< eval mx
       return (lvVector (beZext be (fromIntegral (i + j)) x))
bvUExtOp _ _ args = wrongArity "UExt op" args

bvSExtOp :: (Eq l, LV.Storable l) => BValueOp s l
bvSExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi
       j <- asBNat mj
       x <- asLitVector =<< eval mx
       return (lvVector (beSext be (fromIntegral (i + j + 1)) x))
bvSExtOp _ _ args = wrongArity "SExt op" args

getOp :: LV.Storable l => BValueOp s l
getOp _be eval [mn, _mty, mx, mf] =
    do _n <- asBNat mn
       x <- asBVector =<< eval mx
       case R.asCtor mf of
         Just ("Prelude.FinVal", [mi, _]) -> do
           i <- asBNat mi
           return ((V.!) x (fromIntegral i))
         _ -> fail $ "get: invalid index: " ++ show mf
getOp _ _ args = wrongArity "get op" args

-- set :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e -> Vec n e;
setOp :: LV.Storable l => BValueOp s l
setOp _be eval [mn, _me, mv, mf, mx] =
    do _n <- asBNat mn
       v <- asBVector =<< eval mv
       x <- eval mx
       case R.asCtor mf of
         Just ("Prelude.FinVal", [mi, _]) -> do
           i <- asBNat mi
           return (BVector ((V.//) v [(fromIntegral i, x)]))
         _ -> fail $ "set: invalid index: " ++ show mf
setOp _ _ args = wrongArity "set op" args

-- replicate :: (n :: Nat) -> (e :: sort 0) -> e -> Vec n e;
replicateOp :: BValueOp s l
replicateOp _be eval [mn, _me, mx] =
    do n <- fromIntegral <$> asBNat mn
       x <- eval mx
       return (BVector (V.replicate n x))
replicateOp _ _ args = wrongArity "replicate op" args

bvSliceOp :: LV.Storable l => BValueOp s l
bvSliceOp _ eval [_, mi, mn, _, mx] =
    do i <- fromIntegral <$> asBNat mi
       n <- fromIntegral <$> asBNat mn
       x <- asLitVector =<< eval mx
       return (lvVector (LV.take n (LV.drop i x)))
bvSliceOp _ _ args = wrongArity "slice op" args

joinOp :: LV.Storable l => BValueOp s l
joinOp _ eval [mm, mn, _me, mv] =
    do v <- eval mv
       m <- fromIntegral <$> asBNat mm
       n <- fromIntegral <$> asBNat mn
       checkShape (VecShape m (VecShape n BoolShape)) v
       return (lvVector (flattenBValue v))
joinOp _ _ args = wrongArity "join op" args

chunk :: Int -> V.Vector a -> V.Vector (V.Vector a)
chunk n v | V.length v <= n = V.singleton v
          | otherwise = V.cons (V.take n v) (chunk n (V.drop n v))

splitOp :: LV.Storable l => BValueOp s l
splitOp _ eval [mm, mn, _me, mv] =
    do v <- eval mv
       m <- fromIntegral <$> asBNat mm
       n <- fromIntegral <$> asBNat mn
       checkShape (VecShape (m * n) BoolShape) v
       lv <- asBVector v
       let lvParts = chunk (fromIntegral n) lv
           bv = BVector (V.map BVector lvParts)
       checkShape (VecShape m (VecShape n BoolShape)) bv
       return bv
splitOp _ _ args = wrongArity "split op" args

----------------------------------------------------------------------
-- Destructors for BValues

asLitVector :: (LV.Storable l, Functor m, Monad m) => BValue l -> m (LitVector l)
asLitVector (BVector v) = lvFromV <$> V.mapM asBBool v
asLitVector _ = fail "expected Vector"

asBVector :: (LV.Storable l, Functor m, Monad m) => BValue l -> m (V.Vector (BValue l))
asBVector (BVector v) = return v
asBVector _ = fail "expected Vector"

asBBool :: Monad m => BValue l -> m l
asBBool (BBool l) = return l
asBBool _ = fail "expected Bool"

asBNat :: SharedTerm s -> BBMonad Nat
asBNat t =
    case R.asNatLit t of
      Just n -> return n
      Nothing -> fail $ "expected NatLit (got " ++ show t ++ ")"
