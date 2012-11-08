module Simple where

import Control.Applicative ((<$>))
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

type Name = String
type Sort = Integer
type DeBrujinIndex = Int

data Term = Var DeBrujinIndex -- ^ Variable using deBrujin index
          | Set Sort

          | Pi Term Term
          | Lambda Term
          | App Term Term

          | Sigma Term Term
          | Pair Term Term
          | Proj1 Term
          | Proj2 Term

          | UnitValue
          | UnitType
  deriving (Show)

data Telescope
    = EmptyTelescope
    | Nest Telescope Term

-- | Find variable type, lifting free variables in term so they refer to the
-- proper variables in the telescope.
findVarType :: Telescope -> DeBrujinIndex -> Maybe Term
findVarType te lvl = go te lvl
  where go EmptyTelescope _ = Nothing
        go (Nest g t) 0 = Just (incVarBy (lvl + 1) t)
        go (Nest g t) i = findVarType g (i-1)

-- | @changeFreeVar f t@ substitutes each free variable @Var j@ with the
-- term @f i j@ where @i@ is the number of bound variables around @Var j@.
changeFreeVar :: (DeBrujinIndex -> DeBrujinIndex -> Term) ->  Term -> Term
-- Increment all variable with debrujin indices at or above the limit.
changeFreeVar f = go 0
  where go i (Var j)     | j >= i = f i j
        go i (Pi a b)    = Pi     (go i a) (go (i+1) b)
        go i (Lambda a)  = Lambda (go (i+1) a)
        go i (App a b)   = App    (go i a) (go i b)
        go i (Sigma a b) = Sigma  (go i a) (go (i+1) b)
        go i (Pair a b)  = Pair   (go i a) (go (i+1) b)
        go i (Proj1 a)   = Proj1  (go i a)
        go i (Proj2 a)   = Proj2  (go i a)
        go _ s           = s

-- Increment all free variables by the given count.
incVarBy :: DeBrujinIndex -> Term -> Term
incVarBy c = changeFreeVar (\_ j -> Var (j+c))

-- | Substitute term with var index 0 and shift all remaining free variables.
betaReduce :: Term -> Term -> Term
betaReduce s t = changeFreeVar fn s
  where fn i j | j == i = incVarBy i t
               | otherwise = Var (j-1)

-- | Convert term to weak-head normal form. 
whnf :: Term -> Term
whnf (App s t) =
  case whnf s of
    Lambda u -> whnf (betaReduce u t)
    u -> App u t
whnf (Proj1 s) =
  case whnf s of
    Pair t _ -> whnf t
    t -> t
whnf (Proj2 s) =
  case whnf s of
    Pair _ t -> whnf t
    t -> t
whnf t = t

conversion :: Telescope -> Term -> Term -> Term -> Maybe ()
conversion g s t a = conversion' g (whnf s) (whnf t) a

-- Conversion for terms in weak head normal form.
conversion' :: Telescope -> Term -> Term -> Term -> Maybe ()
conversion' g s t (Set _) = conversionSet' g s t
conversion' _ _ _ UnitType = return ()
conversion' g s t (Pi a b) = conversion (Nest g a) (eta s) (eta t) b
  where eta u = App (incVarBy 1 u) (Var 0)
conversion' g s t (Sigma a b) = do
  conversion g (Proj1 s) (Proj1 t) a
  conversion g (Proj2 s) (Proj2 t) (betaReduce b (Proj1 s))
conversion' g s t _ = do
  neutralEquality g s t >> return ()

conversionSet :: Telescope -> Term -> Term -> Maybe ()
conversionSet g s t = conversionSet' g (whnf s) (whnf t)

conversionSet' :: Telescope -> Term -> Term -> Maybe ()
conversionSet' _ (Set i) (Set j) | i == j = return ()
conversionSet' g (Pi a1 b1) (Pi a2 b2) = do
  conversionSet g a1 a2
  conversionSet (Nest g a1) b1 b2
conversionSet' g (Sigma a1 b1) (Sigma a2 b2) = do
  conversionSet g a1 a2
  conversionSet (Nest g a1) b1 b2
conversionSet' g s t = do
  neutralEquality g s t >> return ()

-- | Checks two neutral terms are equal, and returns their type if they are.
neutralEquality :: Telescope -> Term -> Term -> Maybe Term
neutralEquality g (Var i) (Var j) | i == j = findVarType g i
neutralEquality g (App s1 t1) (App s2 t2) = do
  Pi b c <- whnf <$> neutralEquality g s1 s2
  conversion g t1 t2 b
  return (betaReduce c t1)
neutralEquality g (Proj1 s) (Proj1 t) = do
  Sigma b _ <- whnf <$> neutralEquality g s t
  return b
neutralEquality g (Proj2 s) (Proj2 t) = do
  Sigma b c <- whnf <$> neutralEquality g s t
  return (betaReduce c (Proj1 s))
neutralEquality _ _ _ = Nothing

isSubtype :: Telescope -> Term -> Term -> Maybe ()
isSubtype g a b = isSubtype' g (whnf a) (whnf b)

-- | Subtyping for weak head normal forms.
isSubtype' :: Telescope -> Term -> Term -> Maybe ()
isSubtype' _ (Set i) (Set j) | i <= j = return ()
isSubtype' g (Pi  a1 b1) (Pi a2 b2) = do
  conversionSet g a1 a2
  isSubtype (Nest g a1) b1 b2
isSubtype' g (Sigma  a1 b1) (Sigma a2 b2) = do
  conversionSet g  a1 a2
  isSubtype (Nest g a1) b1 b2
isSubtype' g a b = conversionSet g a b

-- 
checkType :: Telescope -> Term -> Term -> Maybe Term
checkType g (Lambda e) a = do
  Pi b c <- return (whnf a)
  Lambda <$> checkType (Nest g b) e c
checkType g (Pair e1 e2) a = do
  Sigma b c <- return (whnf a)
  s <- checkType g e1 b
  t <- checkType g e2 (betaReduce c s)
  return (Pair s t)
checkType g e a = do
  (b,t) <- inferType g e
  isSubtype g b a
  return t

-- Returns type and evaluated term.
inferType :: Telescope -> Term -> Maybe (Term,Term)
inferType g (Var x) = fmap (\t -> (t,Var x)) (findVarType g x)
inferType _ (Set s) = return (Set (s+1), Set s)
inferType g (Pi e1 e2) = do
  (c1,a) <- inferType g e1
  Set i <- return (whnf c1)
  (c2,b) <- inferType (Nest g a) e2
  Set j <- return (whnf c2)
  return (Set (max i j), Pi a b)
inferType g Lambda{} =
  error "We cannot perform type inference on lambda expressions"
inferType g (App e1 e2) = do
  (a,s) <- inferType g e1
  Pi b c <- return (whnf a)
  t <- checkType g e2 b
  return (betaReduce c t, App s t) 
inferType g (Sigma e1 e2) = do
  (c1,a) <- inferType g e1
  Set i <- return (whnf c1)
  (c2,b) <- inferType (Nest g a) e2
  Set j <- return (whnf c2)
  return (Set (max i j), Sigma a b)
inferType g Pair{} = error "Cannnot infer types of pair expressions"
inferType g (Proj1 e) = do
  (a,t) <- inferType g e
  case whnf a of
    Sigma b c -> return (b, Proj1 t)
    _ -> Nothing
inferType g (Proj2 e) = do
  (a,t) <- inferType g e
  case whnf a of
    Sigma b c -> return (betaReduce c t, Proj2 t)
    _ -> Nothing
inferType _ UnitValue = return (UnitType,UnitValue)
inferType _ UnitType = return (Set 0, UnitType)

test = do
  let emp = EmptyTelescope
  let idType = Pi (Set 0) (Pi (Var 0) (Var 1))
  print $ inferType emp idType
  let idFn = Lambda (Lambda (Var 0))
  print $ checkType emp idFn idType