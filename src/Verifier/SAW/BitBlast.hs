{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.BitBlast
  ( BValue(..)
  , flattenBValue
  , bitBlast
    -- * Explicitly cached interface
  , LV.Storable
  , BCache
  , bcEngine
  , newBCache
  , bitBlastWith
  ) where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector.Storable as LV

import Verifier.SAW.Cache
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verinf.Symbolic.Lit

data BValue l
    = BBool l
    | BVector (LitVector l)
    -- TODO: we could add support for tuples and records.

flattenBValue :: LV.Storable l => BValue l -> LitVector l
flattenBValue (BBool l) = LV.singleton l
flattenBValue (BVector v) = v

type BBMonad = MaybeT IO

liftMaybe :: Maybe a -> BBMonad a
liftMaybe m = MaybeT (return m)

----------------------------------------------------------------------

bitBlast :: (Eq l, LV.Storable l) => BitEngine l -> SharedTerm s -> IO (Maybe (BValue l))
bitBlast be t = do
  bc <- newBCache be Map.empty
  bitBlastWith bc t

data BCache l = BCache { bcEngine :: BitEngine l
                       , bcVarCache :: Cache IORef VarIndex (BValue l)
                       , bcTermCache :: Cache IORef TermIndex (BValue l)
                       }

newBCache :: BitEngine l
          -> Map VarIndex (BValue l)
          -> IO (BCache l)
newBCache be vmap0 = do
  vcache <- newCacheMap' vmap0
  tcache <- newCacheMap' Map.empty
  return BCache { bcEngine = be
                , bcVarCache = vcache
                , bcTermCache = tcache
                }

bitBlastWith :: (Eq l, LV.Storable l) => BCache l -> SharedTerm s -> IO (Maybe (BValue l))
bitBlastWith bc t0 = runMaybeT (go t0)
  where be = bcEngine bc
        newVars (asBoolType -> Just ()) = liftIO $ BBool <$> beMakeInputLit be
        newVars (asBitvectorType -> Just n) = liftIO $
          BVector <$> LV.replicateM (fromInteger n) (beMakeInputLit be)
        newVars _ = liftMaybe Nothing
        -- Bitblast term.
        go (asCtor -> Just (ident, []))
          | ident == "Prelude.False" = return (BBool (beFalse be))
          | ident == "Prelude.True"  = return (BBool (beTrue be))
        go (STApp _ (FTermF (ExtCns ec))) =
          useCache (bcVarCache bc) (ecVarIndex ec) (newVars (ecType ec))
        go t@(STApp termidx _) =
          useCache (bcTermCache bc) termidx $
            let (c, xs) = asApplyAll t in
            case c of
              STApp _ (FTermF (GlobalDef ident)) ->
                case Map.lookup ident opTable of
                  Just op -> op be go xs
                  Nothing -> liftMaybe Nothing
              _ -> liftMaybe Nothing

type BValueOp s l
  = BitEngine l
  -> (SharedTerm s -> BBMonad (BValue l))
  -> [SharedTerm s]
  -> BBMonad (BValue l)

opTable :: (Eq l, LV.Storable l) => Map Ident (BValueOp s l)
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

bvBinOp :: (BitEngine l -> LitVector l -> LitVector l -> IO (LitVector l)) -> BValueOp s l
bvBinOp f be eval [_, mx, my] =
    do x <- liftMaybe . asBVector =<< eval mx
       y <- liftMaybe . asBVector =<< eval my
       liftIO $ BVector <$> f be x y
bvBinOp _ _ _ _ = liftMaybe Nothing

bvRelOp :: (BitEngine l -> LitVector l -> LitVector l -> IO l) -> BValueOp s l
bvRelOp f be eval [_, mx, my] =
    do x <- liftMaybe . asBVector =<< eval mx
       y <- liftMaybe . asBVector =<< eval my
       liftIO $ BBool <$> f be x y
bvRelOp _ _ _ _ = liftMaybe Nothing

boolOp :: (BitEngine l -> l -> l -> IO l) -> BValueOp s l
boolOp f be eval [mx, my] =
    do x <- liftMaybe . asBBool =<< eval mx
       y <- liftMaybe . asBBool =<< eval my
       liftIO (fmap BBool (f be x y))
boolOp _ _ _ _ = liftMaybe Nothing

bvNatOp :: LV.Storable l => BValueOp s l
bvNatOp be _ [mw, mx] = do
  w <- asBNat mw
  x <- asBNat mx
  return (BVector (beVectorFromInt be (fromIntegral w) x))
bvNatOp _ _ _ = liftMaybe Nothing

notOp :: BValueOp s l
notOp be eval [mx] =
    do x <- liftMaybe . asBBool =<< eval mx
       return (BBool (beNeg be x))
notOp _ _ _ = liftMaybe Nothing

appendOp :: LV.Storable l => BValueOp s l
appendOp _ eval [_, _, _, mx, my] =
    do x <- liftMaybe . asBVector =<< eval mx
       y <- liftMaybe . asBVector =<< eval my
       return (BVector ((LV.++) x y))
appendOp _ _ _ = liftMaybe Nothing

singleOp :: LV.Storable l => BValueOp s l
singleOp _ eval [_, mx] =
    do x <- liftMaybe . asBBool =<< eval mx
       return (BVector (LV.singleton x))
singleOp _ _ _ = liftMaybe Nothing

iteOp :: (Eq l, LV.Storable l) => BValueOp s l
iteOp be eval [_, mb, mx, my] =
    do b <- liftMaybe . asBBool =<< eval mb
       case () of
         _ | b == beTrue be -> eval mx
           | b == beFalse be -> eval my
           | otherwise ->
               do bx <- eval mx
                  by <- eval my
                  case (bx, by) of
                    (BBool x, BBool y) -> liftIO (fmap BBool (beMux be b x y))
                    (BVector x, BVector y) ->
                        liftIO (fmap BVector (beIteVector be b (return x) (return y)))
                    _ -> liftMaybe Nothing
iteOp _ _ _ = liftMaybe Nothing

bvTruncOp :: (Eq l, LV.Storable l) => BValueOp s l
bvTruncOp be eval [_, mj, mx] =
    do j <- asBNat mj
       x <- liftMaybe . asBVector =<< eval mx
       return (BVector (beTrunc be (fromIntegral j) x))
bvTruncOp _ _ _ = liftMaybe Nothing

bvUExtOp :: (Eq l, LV.Storable l) => BValueOp s l
bvUExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi
       j <- asBNat mj
       x <- liftMaybe . asBVector =<< eval mx
       return (BVector (beZext be (fromIntegral (i + j)) x))
bvUExtOp _ _ _ = liftMaybe Nothing

bvSExtOp :: (Eq l, LV.Storable l) => BValueOp s l
bvSExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi
       j <- asBNat mj
       x <- liftMaybe . asBVector =<< eval mx
       return (BVector (beSext be (fromIntegral (i + j + 1)) x))
bvSExtOp _ _ _ = liftMaybe Nothing

----------------------------------------------------------------------
-- Destructors for BValues

asBVector :: BValue l -> Maybe (LitVector l)
asBVector (BVector lv) = Just lv
asBVector _ = Nothing

asBBool :: BValue l -> Maybe l
asBBool (BBool l) = Just l
asBBool _ = Nothing

asBNat :: SharedTerm s -> BBMonad Integer
asBNat = liftMaybe . asNatLit