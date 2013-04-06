{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.BitBlast
  ( BValue(..)
  , bitBlast
  , bitBlastWith
  ) where

import Control.Monad.IO.Class
import Control.Monad.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector.Storable as LV
import qualified Data.Vector.Storable.Mutable as LV (new,write)

import Verifier.SAW.Cache
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verinf.Symbolic.Lit

data BValue l
    = BNat Integer
    | BBool l
    | BVector (LitVector l)
    -- TODO: we could add support for tuples and records.

type BBMonad = MaybeT IO

liftMaybe :: Maybe a -> BBMonad a
liftMaybe m = MaybeT (return m)

----------------------------------------------------------------------

bitBlast :: (Eq l, LV.Storable l) => BitEngine l -> SharedTerm s -> IO (Maybe (BValue l))
bitBlast = bitBlastWith Map.empty Map.empty

bitBlastWith :: (Eq l, LV.Storable l) =>
                Map VarIndex (BValue l) ->
                Map TermIndex (BValue l) ->
                BitEngine l ->
                SharedTerm s ->
                IO (Maybe (BValue l))
bitBlastWith vmap0 tmap0 be t = runMaybeT $ do
  vcache <- newCacheIORefMap' vmap0
  tcache <- newCacheIORefMap' tmap0
  let newVars (asBoolType -> Just ()) = liftIO (fmap BBool (beMakeInputLit be))
      newVars (asBitvectorType -> Just n) =
          do ls <- liftIO (sequence (replicate (fromIntegral n) (beMakeInputLit be)))
             return (BVector (LV.fromList ls))
      newVars _ = liftMaybe Nothing
  let go (STVar varidx _ ty) = useCache vcache varidx (newVars ty)
      go (STApp _ (FTermF (NatLit n))) = return (BNat n)
      go (STApp _ (FTermF (CtorApp ident [])))
          | ident == mkIdent preludeName "False" = return (BBool (beFalse be))
          | ident == mkIdent preludeName "True" = return (BBool (beTrue be))
      go t@(STApp termidx _) =
        useCache tcache termidx $
          let (c, xs) = asApplyAll t in
          case c of
            STApp _ (FTermF (GlobalDef ident)) ->
              case Map.lookup ident opTable of
                Just op -> op be (map go xs)
                Nothing -> liftMaybe Nothing
            _ -> liftMaybe Nothing
  go t

type BValueOp l = BitEngine l -> [BBMonad (BValue l)] -> BBMonad (BValue l)

opTable :: (Eq l, LV.Storable l) => Map Ident (BValueOp l)
opTable =
    Map.mapKeys (mkIdent preludeName) $
    Map.fromList $
    [ ("bvAdd", bvBinOp beAddInt)
    , ("bvSub", bvBinOp beSubInt)
    , ("bvMul", bvBinOp beMulInt)
    , ("bvAnd", bvBinOp beAndInt)
    , ("bvOr", bvBinOp beOrInt)
    , ("bvXor", bvBinOp beXorInt)
    , ("bvUDiv", bvBinOp beQuotUnsigned)
    , ("bvURem", bvBinOp beRemUnsigned)
    , ("bvSDiv", bvBinOp beQuot)
    , ("bvSRem", bvBinOp beRem)
    , ("bvsle", bvRelOp beSignedLeq)
    , ("bvslt", bvRelOp beSignedLt)
    , ("bvule", bvRelOp beUnsignedLeq)
    , ("bvult", bvRelOp beUnsignedLt)
    , ("bvEq", bvRelOp beEqVector)
    , ("bvNat", bvNatOp)
    , ("and", boolOp beAnd)
    , ("xor", boolOp beXor)
    , ("or", boolOp beOr)
    , ("not", notOp)
    , ("append", appendOp)
    , ("single", singleOp)
    , ("ite", iteOp)
    , ("bvTrunc", bvTruncOp)
    , ("bvUExt", bvUExtOp)
    , ("bvSExt", bvSExtOp)
    ]

bvBinOp :: (BitEngine l -> LitVector l -> LitVector l -> IO (LitVector l)) -> BValueOp l
bvBinOp f be [_, mx, my] =
    do x <- liftMaybe . asBVector =<< mx
       y <- liftMaybe . asBVector =<< my
       liftIO (fmap BVector (f be x y))
bvBinOp _ _ _ = liftMaybe Nothing

bvRelOp :: (BitEngine l -> LitVector l -> LitVector l -> IO l) -> BValueOp l
bvRelOp f be [_, mx, my] =
    do x <- liftMaybe . asBVector =<< mx
       y <- liftMaybe . asBVector =<< my
       liftIO (fmap BBool (f be x y))
bvRelOp _ _ _ = liftMaybe Nothing

boolOp :: (BitEngine l -> l -> l -> IO l) -> BValueOp l
boolOp f be [mx, my] =
    do x <- liftMaybe . asBBool =<< mx
       y <- liftMaybe . asBBool =<< my
       liftIO (fmap BBool (f be x y))
boolOp _ _ _ = liftMaybe Nothing

bvNatOp :: LV.Storable l => BValueOp l
bvNatOp be [mw, mx] =
    do w <- liftMaybe . asBNat =<< mw
       x <- liftMaybe . asBNat =<< mx
       return (BVector (beVectorFromInt be (fromIntegral w) x))
bvNatOp _ _ = liftMaybe Nothing

notOp :: BValueOp l
notOp be [mx] =
    do x <- liftMaybe . asBBool =<< mx
       return (BBool (beNeg be x))
notOp _ _ = liftMaybe Nothing

appendOp :: LV.Storable l => BValueOp l
appendOp be [_, _, _, mx, my] =
    do x <- liftMaybe . asBVector =<< mx
       y <- liftMaybe . asBVector =<< my
       return (BVector ((LV.++) x y))
appendOp _ _ = liftMaybe Nothing

singleOp :: LV.Storable l => BValueOp l
singleOp be [_, mx] =
    do x <- liftMaybe . asBBool =<< mx
       return (BVector (LV.singleton x))
singleOp _ _ = liftMaybe Nothing

iteOp :: (Eq l, LV.Storable l) => BValueOp l
iteOp be [_, mb, mx, my] =
    do b <- liftMaybe . asBBool =<< mb
       case () of
         _ | b == beTrue be -> mx
           | b == beFalse be -> my
           | otherwise ->
               do bx <- mx
                  by <- mx
                  case (bx, by) of
                    (BBool x, BBool y) -> liftIO (fmap BBool (beMux be b x y))
                    (BVector x, BVector y) ->
                        liftIO (fmap BVector (beIteVector be b (return x) (return y)))
                    _ -> liftMaybe Nothing
iteOp _ _ = liftMaybe Nothing

bvTruncOp :: (Eq l, LV.Storable l) => BValueOp l
bvTruncOp be [mi, mj, mx] =
    do j <- liftMaybe . asBNat =<< mj
       x <- liftMaybe . asBVector =<< mx
       return (BVector (beTrunc be (fromIntegral j) x))
bvTruncOp _ _ = liftMaybe Nothing

bvUExtOp :: (Eq l, LV.Storable l) => BValueOp l
bvUExtOp be [mi, mj, mx] =
    do i <- liftMaybe . asBNat =<< mi
       j <- liftMaybe . asBNat =<< mj
       x <- liftMaybe . asBVector =<< mx
       return (BVector (beZext be (fromIntegral (i + j)) x))
bvUExtOp _ _ = liftMaybe Nothing

bvSExtOp :: (Eq l, LV.Storable l) => BValueOp l
bvSExtOp be [mi, mj, mx] =
    do i <- liftMaybe . asBNat =<< mi
       j <- liftMaybe . asBNat =<< mj
       x <- liftMaybe . asBVector =<< mx
       return (BVector (beSext be (fromIntegral (i + j + 1)) x))
bvSExtOp _ _ = liftMaybe Nothing

----------------------------------------------------------------------
-- Destructors for BValues

asBVector :: BValue l -> Maybe (LitVector l)
asBVector (BVector lv) = Just lv
asBVector _ = Nothing

asBBool :: BValue l -> Maybe l
asBBool (BBool l) = Just l
asBBool _ = Nothing

asBNat :: BValue l -> Maybe Integer
asBNat (BNat n) = Just n
asBNat _ = Nothing

----------------------------------------------------------------------
-- Destructors for terms

asApp :: SharedTerm s -> Maybe (SharedTerm s, SharedTerm s)
asApp (STApp _ (FTermF (App x y))) = Just (x, y)
asApp _ = Nothing

asApplyAll :: SharedTerm s -> (SharedTerm s, [SharedTerm s])
asApplyAll t = go t []
    where
      go t xs =
          case asApp t of
            Nothing -> (t, xs)
            Just (t', x) -> go t' (x : xs)


asBoolType :: SharedTerm s -> Maybe ()
asBoolType (STApp _ (FTermF (DataTypeApp ident [])))
    | ident == mkIdent preludeName "Bool" = Just ()
asBoolType _ = Nothing

asBitvectorType :: SharedTerm s -> Maybe Integer
asBitvectorType (STApp _ (FTermF (App (STApp _ (FTermF (GlobalDef ident)))
                                      (STApp _ (FTermF (NatLit n))))))
    | ident == mkIdent preludeName "bitvector" = Just n
asBitvectorType (STApp _ (FTermF (DataTypeApp ident [STApp _ (FTermF (NatLit n)),
                                                     STApp _ (FTermF (DataTypeApp ident' []))])))
    | ident == mkIdent preludeName "Vec" &&
      ident' == mkIdent preludeName "Bool" = Just n
asBitVectorType _ = Nothing
