{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.SharedTerm
  ( TermF(..)
  , Ident, mkIdent
  , SharedTerm(..)
  , SharedContext(..)
  , TermIndex
  , instantiateVarList
  , unwrapSharedTerm
  , mkSharedContext
    -- ** Implicit versions of functions.
  , scFreshGlobal
  , scModule
  , scApply
  , scApplyAll
  , scMkRecord
  , scRecordSelect
  , scApplyCtor
  , scFun
  , scFunAll
  , scLiteral
  , scTuple
  , scTupleType
  , scTypeOf
  , scPrettyTerm
  , scViewAsBool
  , scViewAsNum
    -- ** Utilities
--  , scTrue
--  , scFalse
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Concurrent.MVar
import qualified Control.Monad.State as State
import Control.Monad.Trans (lift)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Word
import Data.Foldable hiding (sum)
import Data.Traversable
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.HughesPJ

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.TypedAST hiding (instantiateVarList)

type TermIndex = Word64
type VarIndex = Word64

data SharedTerm s
  = STVar !VarIndex !Ident !(SharedTerm s)
  | STApp !TermIndex !(TermF (SharedTerm s))

instance Eq (SharedTerm s) where
  STVar x _ _ == STVar y _ _ = x == y
  STApp x _ == STApp y _ = x == y
  _ == _ = False

instance Ord (SharedTerm s) where
  compare (STVar x _ _) (STVar y _ _) = compare x y
  compare STVar{} _ = LT
  compare _ STVar{} = GT
  compare (STApp x _) (STApp y _) = compare x y

unwrapSharedTerm :: SharedTerm s -> TermF (SharedTerm s)
unwrapSharedTerm (STApp _ tf) = tf

-- | Operations that are defined, but not 
data SharedContext s = SharedContext
  { -- | Returns the current module for the underlying global theory.
    scModuleFn :: IO Module
     -- Returns the globals in the current scope as a record of functions.
  , scFreshGlobalFn   :: Ident -> SharedTerm s -> IO (SharedTerm s)
     -- | @scApplyFn f x@ returns the result of applying @x@ to a lambda function @x@.
  , scDefTermFn       :: TypedDef -> IO (SharedTerm s)
  , scApplyFn         :: SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
  , scMkRecordFn      :: Map FieldName (SharedTerm s) -> IO (SharedTerm s)
  , scRecordSelectFn  :: SharedTerm s -> FieldName -> IO (SharedTerm s)
  , scApplyCtorFn     :: TypedCtor -> [SharedTerm s] -> IO (SharedTerm s)
  , scFunFn           :: SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
  , scLiteralFn       :: Integer -> IO (SharedTerm s)
  , scTupleFn         :: [SharedTerm s] -> IO (SharedTerm s)
  , scTupleTypeFn     :: [SharedTerm s] -> IO (SharedTerm s)
  , scTypeOfFn        :: SharedTerm s -> IO (SharedTerm s)
  , scPrettyTermDocFn :: SharedTerm s -> Doc
  , scViewAsBoolFn    :: SharedTerm s -> Maybe Bool
  , scViewAsNumFn     :: SharedTerm s -> Maybe Integer
  , scInstVarListFn   :: DeBruijnIndex -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
  }

scModule :: (?sc :: SharedContext s) => IO Module
scModule = scModuleFn ?sc

scApply :: (?sc :: SharedContext s) => SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scApply = scApplyFn ?sc

scApplyAll :: (?sc :: SharedContext s) => SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scApplyAll = foldlM scApply

scMkRecord :: (?sc :: SharedContext s) => Map String (SharedTerm s) -> IO (SharedTerm s)
scMkRecord = scMkRecordFn ?sc

scRecordSelect :: (?sc :: SharedContext s) => SharedTerm s -> FieldName -> IO (SharedTerm s)
scRecordSelect = scRecordSelectFn ?sc

scApplyCtor :: (?sc :: SharedContext s) => TypedCtor -> [SharedTerm s] -> IO (SharedTerm s)
scApplyCtor = scApplyCtorFn ?sc

scLiteral :: (?sc :: SharedContext s) => Integer -> IO (SharedTerm s)
scLiteral = scLiteralFn ?sc

scTuple :: (?sc :: SharedContext s) => [SharedTerm s] -> IO (SharedTerm s)
scTuple = scTupleFn ?sc

scTupleType :: (?sc :: SharedContext s) => [SharedTerm s] -> IO (SharedTerm s)
scTupleType = scTupleTypeFn ?sc

scTypeOf :: (?sc :: SharedContext s) => SharedTerm s -> IO (SharedTerm s)
scTypeOf = scTypeOfFn ?sc

-- | Create a global variable with the given identifier (which may be "_") and type.
scFreshGlobal :: (?sc :: SharedContext s)
              => Ident -> SharedTerm s 
              -> IO (SharedTerm s)
scFreshGlobal = scFreshGlobalFn ?sc

{-
scTrue :: (?sc :: SharedContext s) => IO (SharedTerm s)
scTrue = scApplyCtor preludeTrue []

scFalse :: (?sc :: SharedContext s) => IO (SharedTerm s)
scFalse = scApplyCtor preludeFalse []
-}

-- | Returns term as a constant Boolean if it can be evaluated as one.
scViewAsBool :: (?sc :: SharedContext s) => SharedTerm s -> Maybe Bool
scViewAsBool = scViewAsBoolFn ?sc

-- | Returns term as an integer if it is an integer, signed bitvector, or unsigned
-- bitvector.
scViewAsNum :: (?sc :: SharedContext s) => SharedTerm s -> Maybe Integer
scViewAsNum = scViewAsNumFn ?sc

scPrettyTerm :: (?sc :: SharedContext s) => SharedTerm s -> String
scPrettyTerm t = show (scPrettyTermDocFn ?sc t)

scFun :: (?sc :: SharedContext s) => SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scFun = scFunFn ?sc

scFunAll :: (?sc :: SharedContext s) => [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
scFunAll argTypes resultType = foldrM scFun resultType argTypes

-- 
data AppCache s = AC { acBindings :: !(Map (TermF (SharedTerm s)) (SharedTerm s))
                     , acNextIdx :: !Word64
                     }

emptyAppCache :: AppCache s
emptyAppCache = AC Map.empty 0

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: MVar (AppCache s) -> TermF (SharedTerm s) -> IO (SharedTerm s)
getTerm r a =
  modifyMVar r $ \s -> do
    case Map.lookup a (acBindings s) of
      Just t -> return (s,t)
      Nothing -> seq s' $ return (s',t)
        where t = STApp (acNextIdx s) a
              s' = s { acBindings = Map.insert a t (acBindings s)
                     , acNextIdx = acNextIdx s + 1
                     }

asIntLit :: SharedTerm s -> Maybe Integer
asIntLit (STApp _ (IntLit i)) = Just i
asIntLit _ = Nothing

asApp :: SharedTerm s -> Maybe (SharedTerm s, SharedTerm s)
asApp (STApp _ (App t u)) = Just (t,u)
asApp _ = Nothing

asApp3Of :: SharedTerm s -> SharedTerm s -> Maybe (SharedTerm s, SharedTerm s, SharedTerm s)
asApp3Of op s3 = do
  (s2,a3) <- asApp s3
  (s1,a2) <- asApp s2
  (s0,a1) <- asApp s1
  if s0 == op then return (a1,a2,a3) else fail ""

{-
data LocalVarTypeMap s = LVTM { lvtmMap :: Map Integer (SharedTerm s) }

consLocalVarType :: LocalVarTypeMap s -> Ident -> SharedTerm s -> LocalVarTypeMap s
consLocalVarType = undefined

localVarType :: DeBruijnIndex -> LocalVarTypeMap s -> SharedTerm s
localVarType = undefined
-}

data IOCache k v = IOCache !(MVar (Map k v)) (k -> IO v)

newIOCache :: (k -> IO v) -> IO (IOCache k v)
newIOCache fn = do
  mv <- newMVar Map.empty
  return (IOCache mv fn)  

getCacheValue :: Ord k => IOCache k v -> k -> IO v
getCacheValue (IOCache mv f) k = 
  modifyMVar mv $ \m ->
    case Map.lookup k m of
      Just v -> return (m,v)
      Nothing -> fn <$> f k
        where fn v = (Map.insert k v m, v)        

data AppFns s = AppFns { defTypeCache :: IOCache (Def (SharedTerm s)) (SharedTerm s) }

mkApp :: (?af :: AppFns s) => TermF (SharedTerm s) -> IO (SharedTerm s)
mkApp = undefined

sharedDefType :: (?af :: AppFns s) => Def (SharedTerm s) -> IO (SharedTerm s)
sharedDefType = getCacheValue (defTypeCache ?af)

-- | Substitute var 0 in first term for second term, and shift all variable
-- references down.
subst0 :: (?af :: AppFns s) => SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
subst0 = undefined

sortOfTerm :: (?af :: AppFns s) => SharedTerm s -> IO Sort
sortOfTerm t = do
  STApp _ (Sort s) <- typeOf t
  return s

mkSharedSort :: (?af :: AppFns s) => Sort -> IO (SharedTerm s)
mkSharedSort s = mkApp (Sort s)

typeOf :: (?af :: AppFns s)
       => SharedTerm s
       -> IO (SharedTerm s)
typeOf (STVar _ _ tp) = return tp
typeOf (STApp _ tf) =
  case tf of
    LocalVar _ tp -> return tp
    GlobalDef d -> sharedDefType d
    Lambda (PVar i _ _) tp rhs -> do
      rtp <- typeOf rhs
      mkApp (Pi i tp rtp)
    App x y -> do
      STApp _ (Pi _i _ rhs) <- typeOf x
      subst0 rhs y
    Pi _ tp rhs -> do
      ltp <- sortOfTerm tp
      rtp <- sortOfTerm rhs
      mkSharedSort (max ltp rtp)
    TupleValue l  -> mkApp . TupleType =<< mapM typeOf l
    TupleType l  -> mkSharedSort . maximum =<< mapM sortOfTerm l
    RecordValue m -> mkApp . RecordType =<< mapM typeOf m
    RecordSelector t f -> do
      STApp _ (RecordType m) <- typeOf t
      let Just tp = Map.lookup f m
      return tp
    RecordType m -> mkSharedSort . maximum =<< mapM sortOfTerm m
    CtorValue c args -> undefined c args
    CtorType dt args -> undefined dt args
    Sort s -> mkSharedSort (sortOf s)
    Let defs rhs -> undefined defs rhs
    IntLit i -> undefined i
    ArrayValue tp _ -> undefined tp
    EqType{} -> undefined 
    Oracle{} -> undefined

mkSharedContext :: Module -> IO (SharedContext s)
mkSharedContext m = do
  vr <- newMVar  0 -- ^ Reference for getting variables.
  cr <- newMVar emptyAppCache
  let getDef sym =
        case findDef m (mkIdent (moduleName m) sym) of
          Nothing -> fail $ "Failed to find " ++ show sym ++ " in module."
          Just d -> sharedTerm cr (Term (GlobalDef d))
  let freshGlobal sym tp = do
        i <- modifyMVar vr (\i -> return (i,i+1))
        return (STVar i sym tp)
  integerToSignedOp   <- getDef "integerToSigned"
  integerToUnsignedOp <- getDef "integerToUnsigned"
  let viewAsNum (asIntLit -> Just i) = Just i
      viewAsNum (asApp3Of integerToSignedOp -> Just (_,_,asIntLit -> Just i)) = Just i
      viewAsNum (asApp3Of integerToUnsignedOp -> Just (_,_,asIntLit -> Just i)) = Just i
      viewAsNum _ = Nothing
  tpCache <- newIOCache undefined
  let ?af = AppFns { defTypeCache = tpCache
                   }
  return SharedContext {
             scModuleFn = return m
           , scFreshGlobalFn = freshGlobal
           , scDefTermFn = undefined
           , scApplyFn = \f x -> getTerm cr (App f x)
           , scMkRecordFn = undefined
           , scRecordSelectFn = undefined
           , scApplyCtorFn = undefined
           , scFunFn = \a b -> do b' <- Verifier.SAW.SharedTerm.incVars cr 0 1 b
                                  getTerm cr (Pi "_" a b')
           , scLiteralFn = getTerm cr . IntLit
           , scTupleFn = getTerm cr . TupleValue
           , scTupleTypeFn = getTerm cr . TupleType
           , scTypeOfFn = typeOf
           , scPrettyTermDocFn = undefined
           , scViewAsBoolFn = undefined
           , scViewAsNumFn = viewAsNum
           , scInstVarListFn = \k ts t -> commitChangeT (instantiateVarListChangeT cr k ts t)
           }

{-
-- | Monadic fold with memoization
foldSharedTermM :: forall s b m . Monad m 
                => (VarIndex -> Ident -> SharedTerm s -> m b)
                -> (TermF b -> m b) -> SharedTerm s -> m b
foldSharedTermM g f = \t -> State.evalStateT (go t) Map.empty
  where
    go :: SharedTerm s -> State.StateT (Map TermIndex b) m b
    go (STVar i sym tp) = lift $ g i sym tp
    go (STApp i t) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          t' <- Traversable.mapM go t
          x <- lift (f t')
          State.modify (Map.insert i x)
          return x
-}

-- | The inverse function to @sharedTerm@.
unshare :: forall s. SharedTerm s -> Term
unshare t = State.evalState (go t) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex Term) Term
    go (STVar i sym tp) = error "unshare STVar"
    go (STApp i t) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          x <- Term <$> traverse go t
          State.modify (Map.insert i x)
          return x

sharedTerm :: MVar (AppCache s) -> Term -> IO (SharedTerm s)
sharedTerm mvar = go
    where go (Term termf) = getTerm mvar =<< traverse go termf

instantiateVars :: forall s. MVar (AppCache s)
                -> (DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
                                  -> ChangeT IO (IO (SharedTerm s)))
                -> DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
instantiateVars ac f initialLevel t =
    do cache <- newCache
       let ?cache = cache in go initialLevel t
  where
    goList :: (?cache :: Cache (ChangeT IO) (TermIndex, DeBruijnIndex) (SharedTerm s)) =>
              DeBruijnIndex -> [SharedTerm s] -> ChangeT IO [SharedTerm s]
    goList l xs = preserve xs $
      case xs of
        [] -> pure []
        e:r -> (:) <$> go l e <*> goList (l+1) r

    go :: (?cache :: Cache (ChangeT IO) (TermIndex, DeBruijnIndex) (SharedTerm s)) =>
          DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
    go l t@(STVar {}) = pure t
    go l t@(STApp tidx tf) =
        useCache ?cache (tidx, l) (preserveChangeT t $ go' l tf)
    go' :: (?cache :: Cache (ChangeT IO) (TermIndex, DeBruijnIndex) (SharedTerm s)) =>
           DeBruijnIndex -> TermF (SharedTerm s) -> ChangeT IO (IO (SharedTerm s))
    go' l tf =
      case tf of
        LocalVar i tp
          | i < l            -> getTerm ac <$> (LocalVar i <$> go (l-(i+1)) tp)
          | otherwise        -> f l i (go (l-(i+1)) tp)
        Lambda i tp rhs      -> getTerm ac <$> (Lambda i <$> go l tp <*> go (l+1) rhs)
        App x y              -> getTerm ac <$> (App <$> go l x <*> go l y)
        Pi i lhs rhs         -> getTerm ac <$> (Pi i <$> go l lhs <*> go (l+1) rhs)
        TupleValue ll        -> getTerm ac <$> (TupleValue <$> changeList (go l) ll)
        TupleType ll         -> getTerm ac <$> (TupleType <$> changeList (go l) ll)
        RecordValue m        -> getTerm ac <$> (RecordValue <$> traverse (go l) m)
        RecordSelector x fld -> getTerm ac <$> (RecordSelector <$> go l x <*> pure fld)
        RecordType m         -> getTerm ac <$> (RecordType <$> traverse (go l) m)
        CtorValue c ll       -> getTerm ac <$> (CtorValue c <$> goList l ll)
        CtorType dt ll       -> getTerm ac <$> (CtorType dt <$> goList l ll)
        Let defs r           -> getTerm ac <$> (Let <$> changeList procDef defs <*> go l' r)
          where l' = l + length defs
                procDef :: LocalDef String (SharedTerm s) -> ChangeT IO (LocalDef String (SharedTerm s))
                procDef (LocalFnDef sym tp eqs) =
                    LocalFnDef sym <$> go l tp <*> changeList procEq eqs
                procEq :: DefEqn (SharedTerm s) -> ChangeT IO (DefEqn (SharedTerm s))
                procEq (DefEqn pats rhs) = DefEqn pats <$> go eql rhs
                  where eql = l' + sum (patBoundVarCount <$> pats)
        EqType lhs rhs       -> getTerm ac <$> (EqType <$> go l lhs <*> go l rhs)
        Oracle s prop        -> getTerm ac <$> (Oracle s <$> go l prop)
        _ -> return <$> pure t

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVarsChangeT :: MVar (AppCache s)
               -> DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
incVarsChangeT ac initialLevel j
    | j == 0 = return
    | j >  0 = instantiateVars ac fn initialLevel
    where
      fn _ i t = taint $ getTerm ac <$> (LocalVar (i+j) <$> t)

incVars :: MVar (AppCache s)
        -> DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> IO (SharedTerm s)
incVars ac i j t = commitChangeT (incVarsChangeT ac i j t)

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVarChangeT :: forall s. MVar (AppCache s)
                      -> DeBruijnIndex -> SharedTerm s -> SharedTerm s
                      -> ChangeT IO (SharedTerm s)
instantiateVarChangeT ac k t0 t =
    do cache <- newCache
       let ?cache = cache in instantiateVars ac fn 0 t
  where -- Use map reference to memoize instantiated versions of t.
        term :: (?cache :: Cache (ChangeT IO) DeBruijnIndex (SharedTerm s)) =>
                DeBruijnIndex -> ChangeT IO (SharedTerm s)
        term i = useCache ?cache i (incVarsChangeT ac 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache (ChangeT IO) DeBruijnIndex (SharedTerm s)) =>
              DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
                            -> ChangeT IO (IO (SharedTerm s))
        fn i j t | j  > i + k = taint $ getTerm ac <$> (LocalVar (j - 1) <$> t)
                 | j == i + k = taint $ return <$> term i
                 | otherwise  = getTerm ac <$> (LocalVar j <$> t)

instantiateVar :: MVar (AppCache s)
               -> DeBruijnIndex -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
instantiateVar ac k t0 t = commitChangeT (instantiateVarChangeT ac k t0 t)

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and
-- decrement all higher loose variables by @length ts@.
instantiateVarListChangeT :: forall s. MVar (AppCache s)
                          -> DeBruijnIndex -> [SharedTerm s]
                          -> SharedTerm s -> ChangeT IO (SharedTerm s)
instantiateVarListChangeT _ _ [] t = return t
instantiateVarListChangeT ac k ts t =
    do caches <- mapM (const newCache) ts
       instantiateVars ac (fn (zip caches ts)) 0 t
  where
    l = length ts
    -- Memoize instantiated versions of ts.
    term :: (Cache (ChangeT IO) DeBruijnIndex (SharedTerm s), SharedTerm s)
         -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
    term (cache, t) i = useCache cache i (incVarsChangeT ac 0 i t)
    -- Instantiate variables [k .. k+l-1].
    fn :: [(Cache (ChangeT IO) DeBruijnIndex (SharedTerm s), SharedTerm s)]
       -> DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
       -> ChangeT IO (IO (SharedTerm s))
    fn rs i j t | j >= i + k + l = taint $ getTerm ac <$> (LocalVar (j - l) <$> t)
                | j >= i + k     = taint $ return <$> term (rs !! (j - i - k)) i
                | otherwise      = getTerm ac <$> (LocalVar j <$> t)

instantiateVarList :: (?sc :: SharedContext s) =>
                      DeBruijnIndex -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
instantiateVarList = scInstVarListFn ?sc
