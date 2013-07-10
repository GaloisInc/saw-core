{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  , addCut
  , bitBlastWith
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Error
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (traverse)
import qualified Data.Vector as V
import qualified Data.Vector.Storable as LV

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verinf.Symbolic.Lit

data BValue l
    = BBool l
    | BVector (LitVector l)
    | BTuple [BValue l]
    | BRecord (Map FieldName (BValue l))

bTupleSelect :: Int -> BValue l -> BValue l
bTupleSelect n (BTuple vs) = vs !! (n - 1)
bTupleSelect _ _ = error "expected Tuple"

bRecordSelect :: FieldName -> BValue l -> BValue l
bRecordSelect n (BRecord (Map.lookup n -> Just v)) = v
bRecordSelect _ _ = error "expected Record"

flattenBValue :: LV.Storable l => BValue l -> LitVector l
flattenBValue (BBool l) = LV.singleton l
flattenBValue (BVector v) = v
flattenBValue (BTuple vs) = LV.concat (map flattenBValue vs)
flattenBValue (BRecord vm) = LV.concat (map flattenBValue (Map.elems vm))

type BBErr = String
type BBMonad = ErrorT BBErr IO

wrongArity :: String -> BBMonad a
wrongArity s = fail $ "wrong number of function arguments to " ++ s

----------------------------------------------------------------------

bitBlast :: (Eq l, LV.Storable l) => BitEngine l -> SharedTerm s -> IO (Either BBErr (BValue l))
bitBlast be t = do
  bc <- newBCache be
  bitBlastWith bc t

data BCache l = BCache { bcEngine :: !(BitEngine l)
                       , bcTermCache :: !(IORef (Map TermIndex (BValue l)))
                       }

newBCache :: BitEngine l
          -> IO (BCache l)
newBCache be = do
  tcache <- newIORef Map.empty
  return BCache { bcEngine = be
                , bcTermCache = tcache
                }

addCut :: BCache l -> SharedTerm s -> BValue l -> IO ()
addCut bc (STApp t _) bits = do
  m <- readIORef (bcTermCache bc)
  when (Map.member t m) $
    fail "internal: addCut given term that has already been bitblasted."
  writeIORef (bcTermCache bc) $! Map.insert t bits m

bitBlastWith :: forall l s. (Eq l, LV.Storable l) =>
                BCache l -> SharedTerm s -> IO (Either BBErr (BValue l))
bitBlastWith bc t0 = runErrorT (go [] t0)
  where be = bcEngine bc
        newVars :: SharedTerm s -> BBMonad (BValue l)
        newVars (asBoolType -> Just ()) = liftIO $ BBool <$> beMakeInputLit be
        newVars (asBitvectorType -> Just n) = liftIO $
          BVector <$> LV.replicateM (fromInteger n) (beMakeInputLit be)
        newVars (asTupleType -> Just ts) = BTuple <$> traverse newVars ts
        newVars (asRecordType -> Just tm) = BRecord <$> traverse newVars tm
        newVars t = fail $ "bitBlast: unsupported argument type: " ++ show t
        -- Bitblast term.
        go :: [BValue l] -> SharedTerm s -> BBMonad (BValue l)
        go _ (asCtor -> Just (ident, []))
          | ident == "Prelude.False" = return (BBool (beFalse be))
          | ident == "Prelude.True"  = return (BBool (beTrue be))
        go ls (asLambda -> Just (_, ty, body)) = do
          v <- newVars ty
          go (v : ls) body
        go ls t@(STApp termidx tf) = do
          let pushNew r = r <$ lift (addCut bc t r)
              go' = go ls
          m <- lift $ readIORef (bcTermCache bc)
          case Map.lookup termidx m of
            Just r -> return r
            Nothing
              | FTermF (ExtCns ec) <- tf ->
                  pushNew =<< newVars (ecType ec)
              | LocalVar i _ty <- tf -> return (ls !! i)
              | (STApp _ (FTermF (GlobalDef ident)), xs) <- asApplyAll t ->
                 case Map.lookup ident opTable of
                   Just op -> pushNew =<< op be go' xs
                   Nothing -> fail $ "bitBlast: unsupported operator " ++ show ident
              | FTermF (TupleValue ts) <- tf ->
                  pushNew =<< (BTuple <$> traverse go' ts)
              | FTermF (RecordValue tm) <- tf ->
                  pushNew =<< (BRecord <$> traverse go' tm)
              | FTermF (TupleSelector t' n) <- tf ->
                  pushNew =<< (bTupleSelect n <$> go' t')
              | FTermF (RecordSelector t' n) <- tf ->
                  pushNew =<< (bRecordSelect n <$> go' t')
              | FTermF (ArrayValue ty es) <- tf
              , Just () <- asBoolType ty -> do
                  xs <- V.mapM (go' >=> asBBool) es
                  pushNew (BVector (LV.fromList (V.toList xs)))
              | otherwise ->
                  fail $ "bitBlast: unsupported expression: " ++ take 20 (show t)

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
    , ("bvSShr", bvSignedShrOp)
    , ("bvShr", bvUnsignedShrOp)
    , ("bvShl", bvShlOp)
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
    , ("get", bvGetBitOp)
    ]

bvBinOp :: (BitEngine l -> LitVector l -> LitVector l -> IO (LitVector l)) -> BValueOp s l
bvBinOp f be eval [_, mx, my] =
    do x <- asBVector =<< eval mx
       y <- asBVector =<< eval my
       liftIO $ BVector <$> f be x y
bvBinOp _ _ _ _ = wrongArity "binary op"

bvRelOp :: (BitEngine l -> LitVector l -> LitVector l -> IO l) -> BValueOp s l
bvRelOp f be eval [_, mx, my] =
    do x <- asBVector =<< eval mx
       y <- asBVector =<< eval my
       liftIO $ BBool <$> f be x y
bvRelOp _ _ _ _ = wrongArity "relational op"

boolOp :: (BitEngine l -> l -> l -> IO l) -> BValueOp s l
boolOp f be eval [mx, my] =
    do x <- asBBool =<< eval mx
       y <- asBBool =<< eval my
       liftIO (fmap BBool (f be x y))
boolOp _ _ _ _ = wrongArity "boolean op"

bvNatOp :: LV.Storable l => BValueOp s l
bvNatOp be _ [mw, mx] = do
  w <- asBNat mw
  x <- asBNat mx
  return (BVector (beVectorFromInt be (fromIntegral w) x))
bvNatOp _ _ _ = wrongArity "bvNat op"

notOp :: BValueOp s l
notOp be eval [mx] =
    do x <- asBBool =<< eval mx
       return (BBool (beNeg be x))
notOp _ _ _ = wrongArity "not op"

appendOp :: LV.Storable l => BValueOp s l
appendOp _ eval [_, _, _, mx, my] =
    do x <- asBVector =<< eval mx
       y <- asBVector =<< eval my
       return (BVector ((LV.++) x y))
appendOp _ _ _ = wrongArity "append op"

singleOp :: LV.Storable l => BValueOp s l
singleOp _ eval [_, mx] =
    do x <- asBBool =<< eval mx
       return (BVector (LV.singleton x))
singleOp _ _ _ = wrongArity "single op"

iteOp :: (Eq l, LV.Storable l) => BValueOp s l
iteOp be eval [_, mb, mx, my] =
    do b <- asBBool =<< eval mb
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
                    _ -> fail "malformed arguments"
iteOp _ _ _ = wrongArity "ite op"

bvTruncOp :: (Eq l, LV.Storable l) => BValueOp s l
bvTruncOp be eval [_, mj, mx] =
    do j <- asBNat mj
       x <- asBVector =<< eval mx
       return (BVector (beTrunc be (fromIntegral j) x))
bvTruncOp _ _ _ = wrongArity "trunc op"

bvUExtOp :: (Eq l, LV.Storable l) => BValueOp s l
bvUExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi
       j <- asBNat mj
       x <- asBVector =<< eval mx
       return (BVector (beZext be (fromIntegral (i + j)) x))
bvUExtOp _ _ _ = wrongArity "UExt op"

bvSExtOp :: (Eq l, LV.Storable l) => BValueOp s l
bvSExtOp be eval [mi, mj, mx] =
    do i <- asBNat mi
       j <- asBNat mj
       x <- asBVector =<< eval mx
       return (BVector (beSext be (fromIntegral (i + j + 1)) x))
bvSExtOp _ _ _ = wrongArity "SExt op"

bvGetBitOp :: (Eq l, LV.Storable l) => BValueOp s l
bvGetBitOp _ eval [mn, mty, mx, mf] =
    do _n <- asBNat mn
       () <- asBoolType mty
       x <- asBVector =<< eval mx
       case asCtor mf of
         Just ("Prelude.FinVal", [mi, _]) -> do
           i <- asBNat mi
           return (BBool (x LV.! fromIntegral i))
         _ -> fail "badly typed bitvector get"
bvGetBitOp _ _ _ = wrongArity "get op"

bvSignedShrOp :: (Eq l, LV.Storable l) => BValueOp s l
bvSignedShrOp be eval [_, xt, nt] =
    do x <- asBVector =<< eval xt
       n <- asBNat nt
       let w = LV.length x
           nv = beVectorFromInt be w n
       liftIO (fmap BVector (beSignedShr be x nv))
bvSignedShrOp _ _ _ = wrongArity "SShr op"

bvUnsignedShrOp :: (Eq l, LV.Storable l) => BValueOp s l
bvUnsignedShrOp be eval [_, xt, nt] =
    do x <- asBVector =<< eval xt
       n <- asBNat nt
       let w = LV.length x
           nv = beVectorFromInt be w n
       liftIO (fmap BVector (beUnsignedShr be x nv))
bvUnsignedShrOp _ _ _ = wrongArity "SShr op"

bvShlOp :: (Eq l, LV.Storable l) => BValueOp s l
bvShlOp be eval [_, xt, nt] =
    do x <- asBVector =<< eval xt
       n <- asBNat nt
       let w = LV.length x
           nv = beVectorFromInt be w n
       liftIO (fmap BVector (beShl be x nv))
bvShlOp _ _ _ = wrongArity "Shl op"

----------------------------------------------------------------------
-- Destructors for BValues

asBVector :: BValue l -> BBMonad (LitVector l)
asBVector (BVector lv) = return lv
asBVector _ = fail "expected Vector"

asBBool :: BValue l -> BBMonad l
asBBool (BBool l) = return l
asBBool _ = fail "expected Bool"

asBNat :: SharedTerm s -> BBMonad Integer
asBNat t =
    case asNatLit t of
      Just n -> return n
      Nothing -> fail "expected NatLit"
