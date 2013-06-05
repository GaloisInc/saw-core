{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Data.Maybe (fromMaybe)
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.Prelude (preludeModule)
import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

data Value s
    = VFun !(Value s -> Value s)
    | VTrue
    | VFalse
    | VNat !Integer
    | VWord !Int !Integer
    | VString !String
    -- TODO: Use strict, packed string datatype
    | VTuple !(Vector (Value s))
    | VRecord !(Map FieldName (Value s))
    | VCtorApp !String !(Vector (Value s))
    -- TODO: Use strict, packed string datatype
    | VVector !(Vector (Value s))
    | VFloat !Float
    | VDouble !Double
    | VType
    | VIO !(IO (Value s))
    | VTerm !(SharedTerm s)
    | VSC !(SC s (Value s))

newtype SC s a = SC (ReaderT (SharedContext s) IO a)
    deriving ( Functor, Applicative, Monad )

mkSC :: (SharedContext s -> IO a) -> SC s a
mkSC = SC . ReaderT

runSC :: SC s a -> SharedContext s -> IO a
runSC (SC r) sc = runReaderT r sc

instance Show (Value s) where
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
        VIO {} -> showString "<<IO>>"
        VTerm t -> showsPrec p t
        VSC {} -> showString "<<SC>>"

------------------------------------------------------------
-- Basic operations on values

valTupleSelect :: Int -> Value s -> Value s
valTupleSelect i (VTuple v) = (V.!) v (i - 1)
valTupleSelect i v = VCtorApp (show i) (V.singleton v)
--valTupleSelect _ _ = error "valTupleSelect"

valRecordSelect :: FieldName -> Value s -> Value s
valRecordSelect k (VRecord vm) | Just v <- Map.lookup k vm = v
valRecordSelect k v = VCtorApp k (V.singleton v)
--valRecordSelect _ _ = error "valRecordSelect"

apply :: Value s -> Value s -> Value s
apply (VFun f) v = f v
apply _ _ = error "apply"

applyAll :: Value s -> [Value s] -> Value s
applyAll = foldl apply

------------------------------------------------------------

-- | Pattern matching for values.
matchValue :: Pat e -> Value s -> Maybe (Map Int (Value s))
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
matchValues :: [Pat e] -> [Value s] -> Maybe (Map Int (Value s))
matchValues [] [] = Just Map.empty
matchValues [] (_ : _) = Nothing
matchValues (_ : _) [] = Nothing
matchValues (p : ps) (x : xs) = Map.union <$> matchValue p x <*> matchValues ps xs

-- | Evaluator for pattern-matching function definitions,
-- parameterized by an evaluator for right-hand sides.
evalDef :: forall n s e. Show n => ([Value s] -> e -> Value s) -> GenericDef n e -> Value s
evalDef rec (Def ident _ eqns) = vFuns arity (tryEqns eqns)
  where
    arity :: Int
    arity = lengthDefEqn (head eqns)
    lengthDefEqn :: DefEqn e -> Int
    lengthDefEqn (DefEqn ps _) = length ps
    vFuns :: Int -> ([Value s] -> Value s) -> Value s
    vFuns 0 f = f []
    vFuns n f = VFun (\x -> vFuns (n - 1) (\xs -> f (x : xs)))
    tryEqns :: [DefEqn e] -> [Value s] -> Value s
    tryEqns (eqn : eqns') xs = fromMaybe (tryEqns eqns' xs) (tryEqn eqn xs)
    tryEqns [] _ = error $ "Pattern match failure: " ++ show ident
    tryEqn :: DefEqn e -> [Value s] -> Maybe (Value s)
    tryEqn (DefEqn ps e) xs =
        do inst <- matchValues ps xs
           let env = reverse (Map.elems inst)
           return (rec env e)

------------------------------------------------------------

-- | Generic applicative evaluator for TermFs.
evalTermF :: (Show t, Applicative f) => (Ident -> Value s) -> ([Value s] -> t -> Value s)
              -> (t -> f (Value s)) -> [Value s] -> TermF t -> f (Value s)
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
evalTerm :: (Ident -> Value s) -> [Value s] -> Term -> Value s
evalTerm global env (Term tf) = runIdentity (evalTermF global lam rec env tf)
  where
    lam = evalTerm global
    rec t = pure (evalTerm global env t)

evalTypedDef :: (Ident -> Value s) -> TypedDef -> Value s
evalTypedDef global = evalDef (evalTerm global)

evalGlobal :: Module -> Map Ident (Value s) -> Ident -> Value s
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
evalSharedTerm :: (Ident -> Value s) -> SharedTerm s -> Value s
evalSharedTerm global t = evalOpen global (mkMemoClosed global t) [] t

-- | Precomputing the memo table for closed subterms.
mkMemoClosed :: forall s. (Ident -> Value s) -> SharedTerm s -> Map TermIndex (Value s)
mkMemoClosed global t = memoClosed
  where
    memoClosed = fst (State.execState (go t) (Map.empty, Map.empty))
    go :: SharedTerm s -> State.State (Map TermIndex (Value s), Map TermIndex BitSet) BitSet
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
evalClosedTermF :: (Ident -> Value s) -> Map TermIndex (Value s) -> TermF (SharedTerm s) -> Value s
evalClosedTermF global memoClosed tf = runIdentity (evalTermF global lam rec [] tf)
  where
    lam = evalOpen global memoClosed
    rec (STApp i _) =
      case Map.lookup i memoClosed of
        Just v -> pure v
        Nothing -> error "evalClosedTermF: internal error"

-- | Evaluator for open terms; parameterized by a precomputed table @memoClosed@.
evalOpen :: forall s. (Ident -> Value s) -> Map TermIndex (Value s)
         -> [Value s] -> SharedTerm s -> Value s
evalOpen global memoClosed env t = State.evalState (go t) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex (Value s)) (Value s)
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
    evalF :: TermF (SharedTerm s) -> State.State (Map TermIndex (Value s)) (Value s)
    evalF tf = evalTermF global (evalOpen global memoClosed) go env tf

------------------------------------------------------------
-- Representing primitives as Values

class IsValue s a where
    toValue   :: a -> Value s
    fromValue :: Value s -> a

instance IsValue s (Value s) where
    toValue x = x
    fromValue x = x

instance (IsValue s a, IsValue s b) => IsValue s (a -> b) where
    toValue f = VFun (\v -> toValue (f (fromValue v)))
    fromValue (VFun g) = \x -> fromValue (g (toValue x))
    fromValue _        = error "fromValue (->)"

instance IsValue s Bool where
    toValue True  = VTrue
    toValue False = VFalse
    fromValue VTrue  = True
    fromValue VFalse = False
    fromValue _      = error "fromValue Bool"

instance IsValue s Prim.Nat where
    toValue n = VNat (toInteger n)
    fromValue (VNat n) = (fromInteger n)
    fromValue _        = error "fromValue Integer"

instance IsValue s Integer where
    toValue n = VNat n
    fromValue (VNat n) = n
    fromValue _        = error "fromValue Integer"

instance IsValue s Int where
    toValue n = VNat (toInteger n)
    fromValue (VNat n) | 0 <= n && n <= toInteger (maxBound :: Int) = fromInteger n
    fromValue _ = error "fromValue Int"

--instance IsValue String where
instance IsValue s String where
    toValue n = VString n
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

--instance IsValue Float where
instance IsValue s Float where
    toValue n = VFloat n
    fromValue (VFloat n) = n
    fromValue _        = error "fromValue Float"

instance IsValue s Double where
    toValue n = VDouble n
    fromValue (VDouble n) = n
    fromValue _        = error "fromValue Double"

bvToInteger :: Vector Bool -> Integer
bvToInteger = V.foldr' (\b x -> if b then 2*x+1 else 2*x) 0
-- ^ Assuming little-endian order

instance IsValue s a => IsValue s (Vector a) where
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
    fromValue (VWord w x) = V.generate w (fromValue . (toValue :: Bool -> Value s) . testBit x)
    fromValue _           = error "fromValue Vector"

instance (IsValue s a, IsValue s b) => IsValue s (a, b) where
    toValue (x, y) = VTuple (V.fromList [toValue x, toValue y])
    fromValue (VTuple (V.toList -> [x, y])) = (fromValue x, fromValue y)
    fromValue _                             = error "fromValue (,)"

instance IsValue s Prim.BitVector where
    toValue (Prim.BV w x) = VWord w x
    fromValue (VWord w x) = Prim.BV w x
    fromValue _           = error "fromValue BitVector"

instance IsValue s Prim.Fin where
    toValue (Prim.FinVal i j) =
        VCtorApp "Prelude.FinVal" (V.fromList [VNat (toInteger i), VNat (toInteger j)])
    fromValue (VCtorApp "Prelude.FinVal" (V.toList -> [VNat i, VNat j])) =
        Prim.FinVal (fromInteger i) (fromInteger j)
    fromValue _ = error "fromValue Fin"

instance IsValue s () where
    toValue _ = VType
    fromValue _ = ()

instance IsValue s a => IsValue s (IO a) where
    toValue io = VIO (fmap toValue io)
    fromValue (VIO io) = fmap fromValue io
    fromValue _        = error "fromValue IO"

instance IsValue s a => IsValue s (SC s a) where
    toValue m = VSC (fmap toValue m)
    fromValue (VSC m) = fmap fromValue m
    fromValue _       = error "fromValue SC"

instance IsValue s (SharedTerm s) where
    toValue t = VTerm t
    fromValue (VTerm t) = t
    fromValue _         = error "fromValue SharedTerm"

------------------------------------------------------------

preludePrims :: forall s. Map Ident (Value s)
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
  , ("Prelude.ite"     ,
     toValue (Prim.ite :: () -> Bool -> Value s -> Value s -> Value s))
  , ("Prelude.generate",
     toValue (Prim.generate :: Prim.Nat -> () -> (Prim.Fin -> Value s) -> Vector (Value s)))
  , ("Prelude.coerce"  ,
     toValue (Prim.coerce :: () -> () -> () -> Value s -> Value s))
  ]

preludeGlobal :: Ident -> Value s
preludeGlobal = evalGlobal preludeModule preludePrims
