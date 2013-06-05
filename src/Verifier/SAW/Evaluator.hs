{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Evaluator where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State.Strict as State
import Data.Bits
import Data.List ( intersperse )
import Data.Map (Map)
import qualified Data.Map as Map
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
    | VTuple !(Vector Value)
    | VRecord !(Map FieldName Value)
    | VCtorApp String !(Vector Value)
    | VVector !(Vector Value)
    | VFloat !Float
    | VDouble !Double
    | VType
    | VIO !(IO Value)
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
            | V.null vv -> showString s
            | otherwise -> showString s . showList (V.toList vv)
        VVector vv -> showList (V.toList vv)
        VFloat float -> shows float
        VDouble double -> shows double
        VString s -> shows s
        VType -> showString "_"

------------------------------------------------------------
-- Basic operations on values

valTupleSelect :: Int -> Value -> Value
valTupleSelect i (VTuple v) = (V.!) v (i - 1)
valTupleSelect i v = VCtorApp (show i) (V.singleton v)
--valTupleSelect _ _ = error "valTupleSelect"

valRecordSelect :: FieldName -> Value -> Value
valRecordSelect k (VRecord vm) | Just v <- Map.lookup k vm = v
valRecordSelect k v = VCtorApp k (V.singleton v)
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
                       VCtorApp s xv | show i == s -> matchValues ps (V.toList xv)
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
    Lambda (PVar _ 0 _) _ t -> pure $ VFun (\x -> lam (x : env) t)
    Lambda _ _ _            -> error "evalTermF Lambda (non-var) unimplemented"
    Pi {}                   -> pure $ VType
    Let ds t                -> pure $ lam env' t
                                 where
                                   env' = reverse vs ++ env
                                   vs = map (evalDef (\xs -> lam (xs ++ env'))) ds
    LocalVar i _            -> pure $ (env !! i)
    FTermF ftf              ->
      case ftf of
        GlobalDef ident     -> pure $ global ident
        App t1 t2           -> apply <$> rec t1 <*> rec t2
        TupleValue ts       -> VTuple <$> traverse rec (V.fromList ts)
        TupleType {}        -> pure VType
        TupleSelector t j   -> valTupleSelect j <$> rec t
        RecordValue tm      -> VRecord <$> traverse rec tm
        RecordSelector t k  -> valRecordSelect k <$> rec t
        RecordType {}       -> pure VType
        CtorApp ident ts    -> VCtorApp (show ident) <$> traverse rec (V.fromList ts)
        DataTypeApp {}      -> pure VType
        Sort {}             -> pure VType
        NatLit n            -> pure $ VNat n
        ArrayValue _ tv     -> VVector <$> traverse rec tv
        FloatLit x          -> pure $ VFloat x
        DoubleLit x         -> pure $ VDouble x
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
mkMemoClosed :: forall s. (Ident -> Value) -> SharedTerm s -> Map TermIndex Value
mkMemoClosed global t = memoClosed
  where
    memoClosed = fst (State.execState (go t) (Map.empty, Map.empty))
    go :: SharedTerm s -> State.State (Map TermIndex Value, Map TermIndex BitSet) BitSet
    go (STApp i tf) = do
      (_, bmemo) <- State.get
      case Map.lookup i bmemo of
        Just b -> return b
        Nothing -> do
          b <- freesTermF <$> traverse go tf
          let v = evalClosedTermF global memoClosed tf
          State.modify (\(vm, bm) ->
            (if b == 0 then Map.insert i v vm else vm, Map.insert i b bm))
          return b

-- | Evaluator for closed terms, used to populate @memoClosed@.
evalClosedTermF :: (Ident -> Value) -> Map TermIndex Value -> TermF (SharedTerm s) -> Value
evalClosedTermF global memoClosed tf = runIdentity (evalTermF global lam rec [] tf)
  where
    lam = evalOpen global memoClosed
    rec (STApp i _) =
      case Map.lookup i memoClosed of
        Just v -> pure v
        Nothing -> error "evalClosedTermF: internal error"

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall s. (Ident -> Value) -> Map TermIndex Value -> [Value] -> SharedTerm s -> Value
evalOpen global memoClosed env t = State.evalState (go t) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex Value) Value
    go (STApp i tf) =
      case Map.lookup i memoClosed of
        Just v -> return v
        Nothing -> do
          memoLocal <- State.get
          case Map.lookup i memoLocal of
            Just v -> return v
            Nothing -> do
              v <- evalF tf
              State.modify (Map.insert i v)
              return v
    evalF :: TermF (SharedTerm s) -> State.State (Map TermIndex Value) Value
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
    fromValue _        = error "fromValue Integer"

instance IsValue Integer where
    toValue n = VNat n
    fromValue (VNat n) = n
    fromValue _        = error "fromValue Integer"

instance IsValue Int where
    toValue n = VNat (toInteger n)
    fromValue (VNat n) | 0 <= n && n <= toInteger (maxBound :: Int) = fromInteger n
    fromValue _ = error "fromValue Int"

instance IsValue String where
    toValue n = VString n
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

instance IsValue Float where
    toValue n = VFloat n
    fromValue (VFloat n) = n
    fromValue _        = error "fromValue Float"

instance IsValue Double where
    toValue n = VDouble n
    fromValue (VDouble n) = n
    fromValue _        = error "fromValue Double"

bvToInteger :: Vector Bool -> Integer
bvToInteger = V.foldr' (\b x -> if b then 2*x+1 else 2*x) 0
-- ^ Assuming little-endian order

instance IsValue a => IsValue (Vector a) where
    toValue av =
        case traverse toBool vv of
          Nothing -> VVector vv
          Just bv -> VWord (V.length bv) (bvToInteger bv)
        where
          vv = fmap toValue av
          toBool VTrue  = Just True
          toBool VFalse = Just False
          toBool _      = Nothing
    fromValue (VVector v) = fmap fromValue v
    fromValue (VWord w x) = V.generate w (fromValue . toValue . testBit x)
    fromValue _           = error "fromValue Vector"

instance (IsValue a, IsValue b) => IsValue (a, b) where
    toValue (x, y) = VTuple (V.fromList [toValue x, toValue y])
    fromValue (VTuple (V.toList -> [x, y])) = (fromValue x, fromValue y)
    fromValue _                             = error "fromValue (,)"

instance IsValue Prim.BitVector where
    toValue (Prim.BV w x) = VWord w x
    fromValue (VWord w x) = Prim.BV w x
    fromValue _           = error "fromValue BitVector"

instance IsValue Prim.Fin where
    toValue (Prim.FinVal i j) =
        VCtorApp "Prelude.FinVal" (V.fromList [VNat (toInteger i), VNat (toInteger j)])
    fromValue (VCtorApp "Prelude.FinVal" (V.toList -> [VNat i, VNat j])) =
        Prim.FinVal (fromInteger i) (fromInteger j)
    fromValue _ = error "fromValue Fin"

instance IsValue () where
    toValue _ = VType
    fromValue _ = ()

instance IsValue a => IsValue (IO a) where
    toValue io = VIO (fmap toValue io)
    fromValue (VIO io) = fmap fromValue io
    fromValue _        = error "fromValue IO"

------------------------------------------------------------

preludePrims :: Map Ident Value
preludePrims = Map.fromList
  [ ("Prelude.Succ"    , toValue (succ :: Integer -> Integer))
  , ("Prelude.addNat"  , toValue ((+) :: Integer -> Integer -> Integer))
  , ("Prelude.mulNat"  , toValue ((*) :: Integer -> Integer -> Integer))
  , ("Prelude.bvNat"   , toValue Prim.bvNat)
  , ("Prelude.bvAdd"   , toValue Prim.bvAdd)
  , ("Prelude.bvSub"   , toValue Prim.bvSub)
  , ("Prelude.bvMul"   , toValue Prim.bvMul)
  , ("Prelude.bvAnd"   , toValue Prim.bvAnd)
  , ("Prelude.bvOr"    , toValue Prim.bvOr )
  , ("Prelude.bvXor"   , toValue Prim.bvXor)
  , ("Prelude.bvNot"   , toValue Prim.bvNot)
  , ("Prelude.bvEq"    , toValue Prim.bvEq )
  , ("Prelude.bvult"   , toValue Prim.bvult)
  , ("Prelude.bvule"   , toValue Prim.bvule)
  , ("Prelude.get"     , toValue Prim.get_bv)
  , ("Prelude.ite"     , toValue (Prim.ite :: () -> Bool -> Value -> Value -> Value))
  , ("Prelude.generate", toValue (Prim.generate :: Prim.Nat -> () -> (Prim.Fin -> Value) -> Vector Value))
  , ("Prelude.coerce"  , toValue (Prim.coerce :: () -> () -> () -> Value -> Value))
  ]

preludeGlobal :: Ident -> Value
preludeGlobal = evalGlobal preludeModule preludePrims
