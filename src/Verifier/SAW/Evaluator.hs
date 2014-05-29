{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Evaluator where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict as State
import Data.Bits
import Data.List ( intersperse )
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Maybe (fromMaybe)
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.Prelude (preludeModule)
import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

data Value
    = VFun !(Value -> Value)
    | VTrue
    | VFalse
    | VNat !Integer
    | VWord !Int !Integer
    | VString !String
    -- TODO: Use strict, packed string datatype
    | VTuple !(Vector Value)
    | VRecord !(Map FieldName Value)
    | VCtorApp !Ident !(Vector Value)
    -- TODO: Use strict, packed string datatype
    | VVector !(Vector Value)
    | VFloat !Float
    | VDouble !Double
    | VType

newtype SC s a = SC (ReaderT (SharedContext s) IO a)
    deriving ( Functor, Applicative, Monad )

mkSC :: (SharedContext s -> IO a) -> SC s a
mkSC = SC . ReaderT

runSC :: SC s a -> SharedContext s -> IO a
runSC (SC r) sc = runReaderT r sc

instance Show Value where
    showsPrec p v =
      case v of
        VFun {} -> showString "<<fun>>"
        VTrue -> showString "True"
        VFalse -> showString "False"
        VNat n -> shows n
        VWord w x -> showParen (p > 9) (shows x . showString "::[" . shows w . showString "]")
        VTuple vv -> showParen True
                     (foldr (.) id (intersperse (showString ",") (map shows (V.toList vv))))
        VRecord _ -> error "unimplemented: show VRecord" -- !(Map FieldName Value)
        VCtorApp s vv
            | V.null vv -> shows s
            | otherwise -> shows s . showList (V.toList vv)
        VVector vv -> showList (V.toList vv)
        VFloat float -> shows float
        VDouble double -> shows double
        VString s -> shows s
        VType -> showString "_"

instance Eq Value where
    VTrue        == VTrue        = True
    VTrue        == VFalse       = False
    VFalse       == VTrue        = False
    VFalse       == VFalse       = True
    VNat x       == VNat y       = x == y
    VWord m x    == VWord n y    = Prim.bvEq m (Prim.BV m x) (Prim.BV n y)
    VString x    == VString y    = x == y
    VTuple x     == VTuple y     = x == y
    VRecord x    == VRecord y    = x == y
    VCtorApp a x == VCtorApp b y = a == b && x == y
    VVector x    == VVector y    = x == y
    VFloat x     == VFloat y     = x == y
    VDouble x    == VDouble y    = x == y
    VWord m x    == VVector y    = m == V.length y && x == bvToInteger (fmap fromValue y)
    VVector x    == VWord n y    = V.length x == n && bvToInteger (fmap fromValue x) == y
    _            == _            = error "values not comparable"

------------------------------------------------------------
-- Basic operations on values

valTupleSelect :: Int -> Value -> Value
valTupleSelect i (VTuple v) = (V.!) v (i - 1)
valTupleSelect i v = VCtorApp (mkIdent preludeName (show i)) (V.singleton v)
--valTupleSelect _ _ = error "valTupleSelect"

valRecordSelect :: FieldName -> Value -> Value
valRecordSelect k (VRecord vm) | Just v <- Map.lookup k vm = v
valRecordSelect k v = VCtorApp (mkIdent preludeName k) (V.singleton v)
--valRecordSelect _ _ = error "valRecordSelect"

apply :: Value -> Value -> Value
apply (VFun f) v = f v
apply _ _ = error "apply"

applyAll :: Value -> [Value] -> Value
applyAll = foldl apply

------------------------------------------------------------

-- | Pattern matching for values.
matchValue :: Pat e -> Value -> Maybe (Map Int Value)
matchValue p x =
    case p of
      PVar _ i _  -> Just (Map.singleton i x)
      PUnused _ _ -> Just Map.empty
      PTuple ps   -> case x of VTuple xv -> matchValues ps (V.toList xv)
                               _         -> Nothing
      PRecord _   -> error "matchValue PRecord unimplemented"
      PCtor i ps  -> case x of
                       VCtorApp s xv | i == s -> matchValues ps (V.toList xv)
                       VTrue | i == "Prelude.True" && null ps -> Just Map.empty
                       VFalse | i == "Prelude.False" && null ps -> Just Map.empty
                       _ -> Nothing

-- | Simultaneous pattern matching for lists of values.
matchValues :: [Pat e] -> [Value] -> Maybe (Map Int Value)
matchValues [] [] = Just Map.empty
matchValues [] (_ : _) = Nothing
matchValues (_ : _) [] = Nothing
matchValues (p : ps) (x : xs) = Map.union <$> matchValue p x <*> matchValues ps xs

-- | Evaluator for pattern-matching function definitions,
-- parameterized by an evaluator for right-hand sides.
evalDef :: forall n e. Show n => ([Value] -> e -> Value) -> GenericDef n e -> Value
evalDef rec (Def ident _ eqns) = vFuns arity (tryEqns eqns)
  where
    arity :: Int
    arity = lengthDefEqn (head eqns)
    lengthDefEqn :: DefEqn e -> Int
    lengthDefEqn (DefEqn ps _) = length ps
    vFuns :: Int -> ([Value] -> Value) -> Value
    vFuns 0 f = f []
    vFuns n f = VFun (\x -> vFuns (n - 1) (\xs -> f (x : xs)))
    tryEqns :: [DefEqn e] -> [Value] -> Value
    tryEqns (eqn : eqns') xs = fromMaybe (tryEqns eqns' xs) (tryEqn eqn xs)
    tryEqns [] _ = error $ "Pattern match failure: " ++ show ident
    tryEqn :: DefEqn e -> [Value] -> Maybe Value
    tryEqn (DefEqn ps e) xs =
        do inst <- matchValues ps xs
           let env = reverse (Map.elems inst)
           return (rec env e)

------------------------------------------------------------

-- | Generic applicative evaluator for TermFs.
evalTermF :: (Show t, Applicative f) => (Ident -> Value) -> ([Value] -> t -> Value)
              -> (t -> f Value) -> [Value] -> TermF t -> f Value
evalTermF global lam rec env tf =
  case tf of
    App t1 t2               -> apply <$> rec t1 <*> rec t2
    Lambda _ _ t            -> pure $ VFun (\x -> lam (x : env) t)
    Pi {}                   -> pure $ VType
    Let ds t                -> pure $ lam env' t
                                 where
                                   env' = reverse vs ++ env
                                   vs = map (evalDef (\xs -> lam (xs ++ env'))) ds
    LocalVar i              -> pure $ (env !! i)
    Constant _ t            -> rec t
    FTermF ftf              ->
      case ftf of
        GlobalDef ident     -> pure $ global ident
        TupleValue ts       -> VTuple <$> traverse rec (V.fromList ts)
        TupleType {}        -> pure VType
        TupleSelector t j   -> valTupleSelect j <$> rec t
        RecordValue tm      -> VRecord <$> traverse rec tm
        RecordSelector t k  -> valRecordSelect k <$> rec t
        RecordType {}       -> pure VType
        CtorApp ident ts    -> VCtorApp ident <$> traverse rec (V.fromList ts)
        DataTypeApp {}      -> pure VType
        Sort {}             -> pure VType
        NatLit n            -> pure $ VNat n
        ArrayValue _ tv     -> VVector <$> traverse rec tv
        FloatLit x          -> pure $ VFloat x
        DoubleLit x         -> pure $ VDouble x
        StringLit s         -> pure $ VString s
        ExtCns _            -> error "evalTermF ExtCns unimplemented"

-- | Evaluator for unshared terms.
evalTerm :: (Ident -> Value) -> [Value] -> Term -> Value
evalTerm global env (Term tf) = runIdentity (evalTermF global lam rec env tf)
  where
    lam = evalTerm global
    rec t = pure (evalTerm global env t)

evalTypedDef :: (Ident -> Value) -> TypedDef -> Value
evalTypedDef global = evalDef (evalTerm global)

evalGlobal :: Module -> Map Ident Value -> Ident -> Value
evalGlobal m prims ident =
  case Map.lookup ident prims of
    Just v -> v
    Nothing ->
      case findDef m ident of
        Just td | not (null (defEqs td)) -> evalTypedDef (evalGlobal m prims) td
        _ -> error $ "Unimplemented global: " ++ show ident

------------------------------------------------------------
-- The evaluation strategy for SharedTerms involves two memo tables:
-- The first, @memoClosed@, is precomputed and contains the result of
-- evaluating all _closed_ subterms. The same @memoClosed@ table is
-- used for evaluation under lambdas, since the meaning of a closed
-- term does not depend on the local variable context. The second memo
-- table is @memoLocal@, which caches the result of evaluating _open_
-- terms in the current variable context. It is created anew whenever
-- we descend under a lambda binder.

-- | Evaluator for shared terms.
evalSharedTerm :: (Ident -> Value) -> SharedTerm s -> Value
evalSharedTerm global t = evalOpen global (mkMemoClosed global t) [] t

-- | Precomputing the memo table for closed subterms.
mkMemoClosed :: forall s. (Ident -> Value) -> SharedTerm s -> IntMap Value
mkMemoClosed global t = memoClosed
  where
    memoClosed = fst (State.execState (go t) (IMap.empty, IMap.empty))
    go :: SharedTerm s -> State.State (IntMap Value, IntMap BitSet) BitSet
    go (STApp i tf) = do
      (_, bmemo) <- State.get
      case IMap.lookup i bmemo of
        Just b -> return b
        Nothing -> do
          b <- freesTermF <$> traverse go tf
          let v = evalClosedTermF global memoClosed tf
          State.modify (\(vm, bm) ->
            (if b == 0 then IMap.insert i v vm else vm, IMap.insert i b bm))
          return b

-- | Evaluator for closed terms, used to populate @memoClosed@.
evalClosedTermF :: (Ident -> Value) -> IntMap Value -> TermF (SharedTerm s) -> Value
evalClosedTermF global memoClosed tf = runIdentity (evalTermF global lam rec [] tf)
  where
    lam = evalOpen global memoClosed
    rec (STApp i _) =
      case IMap.lookup i memoClosed of
        Just v -> pure v
        Nothing -> error "evalClosedTermF: internal error"

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall s. (Ident -> Value) -> IntMap Value
         -> [Value] -> SharedTerm s -> Value
evalOpen global memoClosed env t = State.evalState (go t) IMap.empty
  where
    go :: SharedTerm s -> State.State (IntMap Value) Value
    go (STApp i tf) =
      case IMap.lookup i memoClosed of
        Just v -> return v
        Nothing -> do
          memoLocal <- State.get
          case IMap.lookup i memoLocal of
            Just v -> return v
            Nothing -> do
              v <- evalF tf
              State.modify (IMap.insert i v)
              return v
    evalF :: TermF (SharedTerm s) -> State.State (IntMap Value) Value
    evalF tf = evalTermF global (evalOpen global memoClosed) go env tf

------------------------------------------------------------
-- Representing primitives as Values

class IsValue a where
    toValue   :: a -> Value
    fromValue :: Value -> a

instance IsValue Value where
    toValue x = x
    fromValue x = x

instance (IsValue a, IsValue b) => IsValue (a -> b) where
    toValue f = VFun (\v -> toValue (f (fromValue v)))
    fromValue (VFun g) = \x -> fromValue (g (toValue x))
    fromValue _        = error "fromValue (->)"

instance IsValue Bool where
    toValue True  = VTrue
    toValue False = VFalse
    fromValue VTrue  = True
    fromValue VFalse = False
    fromValue _      = error "fromValue Bool"

instance IsValue Prim.Nat where
    toValue n = VNat (toInteger n)
    fromValue (VNat n) = (fromInteger n)
    fromValue (VCtorApp ident (V.toList -> [v])) | ident == "Prelude.Succ" = 1 + fromValue v
    fromValue v        = error $ "fromValue: expected Nat, found " ++ show v

instance IsValue Integer where
    toValue n = VNat n
    fromValue (VNat n) = n
    fromValue (VCtorApp ident (V.toList -> [v])) | ident == "Prelude.Succ" = 1 + fromValue v
    fromValue v        = error $ "fromValue: expected Integer, found " ++ show v

instance IsValue Int where
    toValue n = VNat (toInteger n)
    fromValue (VNat n) | 0 <= n && n <= toInteger (maxBound :: Int) = fromInteger n
    fromValue _ = error "fromValue Int"

instance IsValue String where
    toValue n = VString n
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

--instance IsValue Float where
instance IsValue Float where
    toValue n = VFloat n
    fromValue (VFloat n) = n
    fromValue _        = error "fromValue Float"

instance IsValue Double where
    toValue n = VDouble n
    fromValue (VDouble n) = n
    fromValue _        = error "fromValue Double"

-- | Conversion from list of bits to integer (big-endian)
bvToInteger :: Vector Bool -> Integer
bvToInteger = V.foldl' (\x b -> if b then 2*x+1 else 2*x) 0
-- little-endian version:
-- bvToInteger = V.foldr' (\b x -> if b then 2*x+1 else 2*x) 0

instance IsValue a => IsValue (Vector a) where
    toValue av = VVector (fmap toValue av)
{-
        case traverse toBool vv of
          Nothing -> VVector vv
          Just bv -> VWord (V.length bv) (bvToInteger bv)
        where
          vv = fmap toValue av
          toBool VTrue  = Just True
          toBool VFalse = Just False
          toBool _      = Nothing
-}
    fromValue (VVector v) = fmap fromValue v
    fromValue (VWord w x) = V.generate w (fromValue . (toValue :: Bool -> Value) . testBit x)
    fromValue _           = error "fromValue Vector"

instance (IsValue a, IsValue b) => IsValue (a, b) where
    toValue (x, y) = VTuple (V.fromList [toValue x, toValue y])
    fromValue (VTuple (V.toList -> [x, y])) = (fromValue x, fromValue y)
    fromValue _                             = error "fromValue (,)"

instance IsValue Prim.BitVector where
    toValue (Prim.BV w x) = VWord w x
    fromValue (VWord w x) = Prim.BV w x
    fromValue (VVector v) = Prim.BV (V.length v) (bvToInteger (fmap fromValue v))
    fromValue v           = error $ "fromValue BitVector: " ++ show v

instance IsValue Prim.Fin where
    toValue (Prim.FinVal i j) =
        VCtorApp "Prelude.FinVal" (V.fromList [VNat (toInteger i), VNat (toInteger j)])
    fromValue (VCtorApp "Prelude.FinVal" (V.toList -> [VNat i, VNat j])) =
        Prim.FinVal (fromInteger i) (fromInteger j)
    fromValue _ = error "fromValue Fin"

instance IsValue () where
    toValue _ = VTuple V.empty
    fromValue _ = ()

------------------------------------------------------------

preludePrims :: Map Ident Value
preludePrims = Map.fromList
  [ ("Prelude.Succ"    , toValue (succ :: Prim.Nat -> Prim.Nat))
  , ("Prelude.addNat"  , toValue ((+) :: Prim.Nat -> Prim.Nat -> Prim.Nat))
  , ("Prelude.subNat"  , toValue ((-) :: Prim.Nat -> Prim.Nat -> Prim.Nat))
  , ("Prelude.mulNat"  , toValue ((*) :: Prim.Nat -> Prim.Nat -> Prim.Nat))
  , ("Prelude.minNat"  , toValue (min :: Prim.Nat -> Prim.Nat -> Prim.Nat))
  , ("Prelude.maxNat"  , toValue (max :: Prim.Nat -> Prim.Nat -> Prim.Nat))
  , ("Prelude.widthNat", toValue Prim.widthNat)
  , ("Prelude.finDivMod", toValue Prim.finDivMod)
  , ("Prelude.finOfNat", toValue (flip Prim.finFromBound))
  , ("Prelude.bvToNat" , toValue Prim.bvToNat)
  , ("Prelude.bvNat"   , toValue Prim.bvNat)
  , ("Prelude.bvAdd"   , toValue Prim.bvAdd)
  , ("Prelude.bvSub"   , toValue Prim.bvSub)
  , ("Prelude.bvMul"   , toValue Prim.bvMul)
  , ("Prelude.bvAnd"   , toValue Prim.bvAnd)
  , ("Prelude.bvOr"    , toValue Prim.bvOr )
  , ("Prelude.bvXor"   , toValue Prim.bvXor)
  , ("Prelude.bvNot"   , toValue Prim.bvNot)
  , ("Prelude.bvEq"    , toValue Prim.bvEq )
  , ("Prelude.bvShl"   , toValue Prim.bvShl)
  , ("Prelude.bvShr"   , toValue Prim.bvShr)
  , ("Prelude.bvult"   , toValue Prim.bvult)
  , ("Prelude.bvule"   , toValue Prim.bvule)
  , ("Prelude.get"     , toValue get')
  , ("Prelude.append"  , toValue append')
  , ("Prelude.rotateL" , toValue rotateL')
  , ("Prelude.rotateR" , toValue rotateR')
  , ("Prelude.vZip"    , toValue vZip')
  , ("Prelude.and"     , toValue (&&))
  , ("Prelude.not"     , toValue not)
  , ("Prelude.eq"      , toValue (const (==) :: () -> Value -> Value -> Bool))
  , ("Prelude.ite"     ,
     toValue (Prim.ite :: () -> Bool -> Value -> Value -> Value))
  , ("Prelude.generate",
     toValue (Prim.generate :: Prim.Nat -> () -> (Prim.Fin -> Value) -> Vector Value))
  , ("Prelude.coerce"  ,
     toValue (Prim.coerce :: () -> () -> () -> Value -> Value))
  ]

get' :: Int -> () -> Value -> Prim.Fin -> Value
get' _ _ (VVector xs) i = (V.!) xs (fromEnum i)
get' _ _ (VWord n x) i = toValue (Prim.get_bv n () (Prim.BV n x) i)
get' _ _ _ _ = error "get'"

append' :: Int -> Int -> () -> Value -> Value -> Value
append' _ _ _ (VVector xs) (VVector ys) = VVector ((V.++) xs ys)
append' _ _ _ (VWord m x) (VWord n y) = toValue (Prim.append_bv m n () (Prim.BV m x) (Prim.BV n y))
append' _ _ _ (VVector xs) y@(VWord _ _) = VVector ((V.++) xs (fromValue y))
append' _ _ _ x@(VWord _ _) (VVector ys) = VVector ((V.++) (fromValue x) ys)
append' _ _ _ _ _ = error "append'"

--rotateL :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;

rotateL' :: () -> () -> Value -> Int -> Value
rotateL' _ _ (VWord n x) i = VWord n ((shiftL x j .|. shiftR x (n - j)) .&. (bit n - 1))
  where j = i `mod` n
rotateL' _ _ (VVector xs) i = VVector ((V.++) (V.drop j xs) (V.take j xs))
  where j = i `mod` V.length xs
rotateL' _ _ _ _ = error "rotateL'"

rotateR' :: () -> () -> Value -> Int -> Value
rotateR' _ _ (VWord n x) i = VWord n ((shiftL x (n - j) .|. shiftR x j) .&. (bit n - 1))
  where j = i `mod` n
rotateR' _ _ (VVector xs) i = VVector ((V.++) (V.drop j xs) (V.take j xs))
  where j = V.length xs - (i `mod` V.length xs)
rotateR' _ _ _ _ = error "rotateR'"

vZip' :: () -> () -> Int -> Int -> Vector Value -> Vector Value -> Vector (Value, Value)
vZip' _ _ _ _ xs ys = V.zip xs ys

preludeGlobal :: Ident -> Value
preludeGlobal = evalGlobal preludeModule preludePrims
