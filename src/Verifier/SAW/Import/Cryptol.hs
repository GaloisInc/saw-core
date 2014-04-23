{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}

module Verifier.SAW.Import.Cryptol where

import Control.Applicative
import Control.Monad (join)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Traversable

import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Prims.Syntax as P
import Cryptol.TypeCheck.TypeOf (fastTypeOf, fastSchemaOf)

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST (mkSort)

unimplemented :: Monad m => String -> m a
unimplemented name = fail ("unimplemented: " ++ name)

--------------------------------------------------------------------------------
-- Type Environments

data Env s = Env
  { envT :: Map Int (SharedTerm s)     -- ^ Type variables are referenced by unique id
  , envE :: Map C.QName (SharedTerm s) -- ^ Term variables are referenced by name
  , envP :: Map C.Prop (SharedTerm s)  -- ^ Bound propositions are referenced implicitly by their types
  , envC :: Map C.QName C.Schema       -- ^ Cryptol type environment
  }

emptyEnv :: Env s
emptyEnv = Env Map.empty Map.empty Map.empty Map.empty

liftTerm :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
liftTerm sc = incVars sc 0 1

-- | Increment dangling bound variables of all types in environment.
liftEnv :: SharedContext s -> Env s -> IO (Env s)
liftEnv sc env =
  Env <$> traverse (liftTerm sc) (envT env)
      <*> traverse (liftTerm sc) (envE env)
      <*> traverse (liftTerm sc) (envP env)
      <*> pure (envC env)

bindTParam :: SharedContext s -> C.TParam -> SharedTerm s -> Env s -> IO (Env s)
bindTParam sc tp k env = do
  env' <- liftEnv sc env
  v <- scLocalVar sc 0 k
  return $ env' { envT = Map.insert (C.tpUnique tp) v (envT env') }

bindQName :: SharedContext s -> C.QName -> C.Schema -> SharedTerm s -> Env s -> IO (Env s)
bindQName sc qname schema t env = do
  env' <- liftEnv sc env
  v <- scLocalVar sc 0 t
  return $ env' { envE = Map.insert qname v (envE env'), envC = Map.insert qname schema (envC env') }

bindProp :: SharedContext s -> C.Prop -> SharedTerm s -> Env s -> IO (Env s)
bindProp sc prop t env = do
  env' <- liftEnv sc env
  v <- scLocalVar sc 0 t
  return $ env' { envP = Map.insert prop v (envP env') }

--------------------------------------------------------------------------------

importKind :: SharedContext s -> C.Kind -> IO (SharedTerm s)
importKind sc kind =
  case kind of
    C.KType       -> scSort sc (mkSort 0)
    C.KNum        -> scDataTypeApp sc "Prelude.ENat" []
    C.KProp       -> scSort sc (mkSort 0)
    (C.:->) k1 k2 -> join $ scFun sc <$> importKind sc k1 <*> importKind sc k2

importType :: SharedContext s -> Env s -> C.Type -> IO (SharedTerm s)
importType sc env ty =
  case ty of
    C.TVar tvar ->
      case tvar of
        C.TVFree{} {- Int Kind (Set TVar) Doc -} -> unimplemented "TVFree"
        C.TVBound i _k   -> case Map.lookup i (envT env) of
                              Just t -> return t
                              Nothing -> fail "internal error: importType TVBound"
    C.TUser _ _ t  -> go t
    C.TRec fs      -> scRecordType sc =<< traverse go (Map.fromList [ (nameToString n, t) | (n, t) <- fs ])
    C.TCon tcon tyargs ->
      case tcon of
        C.TC tc ->
          case tc of
            C.TCNum n    -> do n' <- scNat sc (fromInteger n)
                               scCtorApp sc "Prelude.Finite" [n']
            C.TCInf      -> scCtorApp sc "Prelude.Infinity" []
            C.TCBit      -> scBoolType sc -- null tyargs
            C.TCSeq      -> join $ scGlobalApply sc "Prelude.Seq" <$> traverse go tyargs -- ^ @[_] _@
            C.TCFun      -> join $ scFun sc <$> go (tyargs !! 0) <*> go (tyargs !! 1) -- ^ @_ -> _@
            C.TCTuple _n -> join $ scTupleType sc <$> traverse go tyargs -- ^ @(_, _, _)@
            C.TCNewtype (C.UserTC _qn _k) -> unimplemented "TCNewtype" -- ^ user-defined, @T@
        C.PC pc ->
          case pc of
            C.PEqual         -> unimplemented "PEqual" -- ^ @_ == _@
            C.PNeq           -> unimplemented "PNeq"   -- ^ @_ /= _@
            C.PGeq           -> unimplemented "PGeq"   -- ^ @_ >= _@
            C.PFin           -> unimplemented "PFin"   -- ^ @fin _@
            C.PHas _selector -> unimplemented "PHas"   -- ^ @Has sel type field@ does not appear in schemas
            C.PArith         -> unimplemented "PArith" -- ^ @Arith _@
            C.PCmp           -> unimplemented "PCmp"   -- ^ @Cmp _@
        C.TF tf ->
          case tf of
            C.TCWidth  -> unimplemented "TCWidth" -- KNum :-> KNum
            C.TCLg2    -> unimplemented "TCLg2" -- KNum :-> KNum
            C.TCAdd    -> join $ scGlobalApply sc "Prelude.addENat" <$> traverse go tyargs
            C.TCSub    -> unimplemented "TCSub" -- KNum :-> KNum :-> KNum
            C.TCMul    -> join $ scGlobalApply sc "Prelude.mulENat" <$> traverse go tyargs
            C.TCDiv    -> unimplemented "TCDiv" -- KNum :-> KNum :-> KNum
            C.TCMod    -> unimplemented "TCMod" -- KNum :-> KNum :-> KNum
            C.TCExp    -> unimplemented "TCExp" -- KNum :-> KNum :-> KNum
            C.TCMin    -> join $ scGlobalApply sc "Prelude.minENat" <$> traverse go tyargs
            C.TCMax    -> unimplemented "TCMax" -- KNum :-> KNum :-> KNum
            C.TCLenFromThen   -> unimplemented "TCLenFromThen" -- KNum :-> KNum :-> KNum :-> KNum
            --C.TCLenFromTo     -> unimplemented "TCLenFromTo" -- KNum :-> KNum :-> KNum
            C.TCLenFromThenTo -> unimplemented "TCLenFromThenTo" -- KNum :-> KNum :-> KNum :-> KNum
  where
    go = importType sc env

nameToString :: C.Name -> String
nameToString (C.Name s) = s
nameToString (C.NewName p i) = show p ++ show i

qnameToString :: C.QName -> String
qnameToString (C.QName _ name) = nameToString name

tparamToString :: C.TParam -> String
--tparamToString tp = maybe "_" qnameToString (C.tpName tp)
tparamToString tp = maybe ("u" ++ show (C.tpUnique tp)) qnameToString (C.tpName tp)

importPropsType :: SharedContext s -> Env s -> [C.Prop] -> C.Type -> IO (SharedTerm s)
importPropsType sc env [] ty = importType sc env ty
importPropsType sc env (prop : props) ty = do
  p <- importType sc env prop
  t <- importPropsType sc env props ty
  scFun sc p t

importPolyType :: SharedContext s -> Env s -> [C.TParam] -> [C.Prop] -> C.Type -> IO (SharedTerm s)
importPolyType sc env [] props ty = importPropsType sc env props ty
importPolyType sc env (tp : tps) props ty = do
  k <- importKind sc (C.tpKind tp)
  env' <- bindTParam sc tp k env
  t <- importPolyType sc env' tps props ty
  scPi sc (tparamToString tp) k t

importSchema :: SharedContext s -> Env s -> C.Schema -> IO (SharedTerm s)
importSchema sc env (C.Forall tparams props ty) = importPolyType sc env tparams props ty

-- | Convert built-in constants to SAWCore.
importECon :: SharedContext s -> P.ECon -> IO (SharedTerm s)
importECon sc econ =
  case econ of
    P.ECTrue        -> scBool sc True
    P.ECFalse       -> scBool sc False
    P.ECDemote      -> scGlobalDef sc "EC.Demote"      -- ^ Converts a numeric type into its corresponding value.
                                                     -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
    P.ECPlus        -> scGlobalDef sc "EC.Plus"        -- {a} (Arith a) => a -> a -> a
    P.ECMinus       -> scGlobalDef sc "EC.Minus"       -- {a} (Arith a) => a -> a -> a
    P.ECMul         -> scGlobalDef sc "EC.Mul"         -- {a} (Arith a) => a -> a -> a
    P.ECDiv         -> scGlobalDef sc "EC.Div"         -- {a} (Arith a) => a -> a -> a
    P.ECMod         -> scGlobalDef sc "EC.Mod"         -- {a} (Arith a) => a -> a -> a
    P.ECExp         -> scGlobalDef sc "EC.Exp"         -- {a} (Arith a) => a -> a -> a
    P.ECLg2         -> scGlobalDef sc "EC.Lg2"         -- {a} (Arith a) => a -> a
    P.ECNeg         -> scGlobalDef sc "EC.Neg"         -- {a} (Arith a) => a -> a
    P.ECLt          -> scGlobalDef sc "EC.Lt"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECGt          -> scGlobalDef sc "EC.Gt"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECLtEq        -> scGlobalDef sc "EC.LtEq"        -- {a} (Cmp a) => a -> a -> Bit
    P.ECGtEq        -> scGlobalDef sc "EC.GtEq"        -- {a} (Cmp a) => a -> a -> Bit
    P.ECEq          -> scGlobalDef sc "EC.Eq"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECNotEq       -> scGlobalDef sc "EC.NotEq"       -- {a} (Cmp a) => a -> a -> Bit
    P.ECFunEq       -> scGlobalDef sc "EC.FunEq"       -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
    P.ECFunNotEq    -> scGlobalDef sc "EC.FunNotEq"    -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
    P.ECMin         -> scGlobalDef sc "EC.Min"         -- {a} (Cmp a) => a -> a -> a
    P.ECMax         -> scGlobalDef sc "EC.Max"         -- {a} (Cmp a) => a -> a -> a
    P.ECAnd         -> scGlobalDef sc "EC.And"         -- {a} a -> a -> a        -- Bits a
    P.ECOr          -> scGlobalDef sc "EC.Or"          -- {a} a -> a -> a        -- Bits a
    P.ECXor         -> scGlobalDef sc "EC.Xor"         -- {a} a -> a -> a        -- Bits a
    P.ECCompl       -> scGlobalDef sc "EC.Compl"       -- {a} a -> a             -- Bits a
    P.ECZero        -> scGlobalDef sc "EC.Zero"        -- {a} a                  -- Bits a
    P.ECShiftL      -> scGlobalDef sc "EC.ShiftL"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECShiftR      -> scGlobalDef sc "EC.ShiftR"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECRotL        -> scGlobalDef sc "EC.RotL"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECRotR        -> scGlobalDef sc "EC.RotR"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECCat         -> scGlobalDef sc "EC.Cat"         -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
    P.ECSplitAt     -> scGlobalDef sc "EC.SplitAt"     -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
    P.ECJoin        -> scGlobalDef sc "EC.Join"        -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
    P.ECSplit       -> scGlobalDef sc "EC.Split"       -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
    P.ECReverse     -> scGlobalDef sc "EC.Reverse"     -- {a,b} (fin a) => [a] b -> [a] b
    P.ECTranspose   -> scGlobalDef sc "EC.Transpose"   -- {a,b,c} [a][b]c -> [b][a]c
    P.ECAt          -> scGlobalDef sc "EC.At"          -- {n,a,m} [n]a -> [m] -> a
    P.ECAtRange     -> scGlobalDef sc "EC.AtRange"     -- {n,a,m,i} [n]a -> [m][i] -> [m]a
    P.ECAtBack      -> scGlobalDef sc "EC.AtBack"      -- {n,a,m} (fin n) => [n]a -> [m] -> a
    P.ECAtRangeBack -> scGlobalDef sc "EC.AtRangeBack" -- {front,back,a} (fin front) => [front + back]a -> ([front]a, [back]a)
    P.ECFromThen    -> scGlobalDef sc "EC.FromThen"
                               -- fromThen : {first,next,bits}
                               --             ( fin first, fin next, fin bits
                               --             , bits >= width first, bits >= width next
                               --             , lengthFromThen first next bits == len
                               --             )
                               --          => [len] [bits]
    P.ECFromTo      -> scGlobalDef sc "EC.FromTo"
    P.ECFromThenTo  -> scGlobalDef sc "EC.FromThenTo"
    P.ECInfFrom     -> scGlobalDef sc "EC.InfFrom"     -- {a} (fin a) => [a] -> [inf][a]
    P.ECInfFromThen -> scGlobalDef sc "EC.InfFromThen" -- {a} (fin a) => [a] -> [a] -> [inf][a]
    P.ECError       -> scGlobalDef sc "EC.Error"       -- {at,len} (fin len) => [len][8] -> at -- Run-time error
    P.ECPMul        -> scGlobalDef sc "EC.PMul"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
    P.ECPDiv        -> scGlobalDef sc "EC.PDiv"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
    P.ECPMod        -> scGlobalDef sc "EC.PMod"        -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
    P.ECRandom      -> scGlobalDef sc "EC.Random"      -- {a} => [32] -> a -- Random values

importExpr :: SharedContext s -> Env s -> C.Expr -> IO (SharedTerm s)
importExpr sc env expr =
  case expr of
    C.ECon econ                 -> importECon sc econ -- ^ Built-in constant
    C.EList _es _t              -> unimplemented "EList" -- ^ List value (with type of elements)
    C.ETuple es                 -> scTuple sc =<< traverse go es
    C.ERec _ {-[(Name,Expr)]-}  -> unimplemented "ERec" -- ^ Record value
    C.ESel e sel                ->           -- ^ Elimination for tuple/record/list
      case sel of
        C.TupleSel i _          -> join $ scTupleSelector sc <$> go e <*> pure i
        C.RecordSel name _      -> join $ scRecordSelect sc <$> go e <*> pure (nameToString name)
        C.ListSel _i _maybeLen      -> unimplemented "ListSel" -- ^ List selection. pos (Maybe length)
    C.EIf e1 e2 e3              -> join $ scIte sc <$> ty t <*> go e1 <*> go e2 <*> go e3
                                     where t = fastTypeOf (envC env) e2
    C.EComp _ e mss             -> importComp sc env e mss
    C.EVar qname                    ->
      case Map.lookup qname (envE env) of
        Just e'                     -> return e'
        Nothing                     -> fail "internal error: unknown variable"
    C.ETAbs tp e                    -> do k <- importKind sc (C.tpKind tp)
                                          env' <- bindTParam sc tp k env
                                          e' <- importExpr sc env' e
                                          scLambda sc (tparamToString tp) k e'
    C.ETApp e t                     -> join $ scApply sc <$> go e <*> ty t
    C.EApp e1 e2                    -> join $ scApply sc <$> go e1 <*> go e2
    C.EAbs x t e                    -> do t' <- ty t
                                          env' <- bindQName sc x (C.Forall [] [] t) t' env
                                          e' <- importExpr sc env' e
                                          scLambda sc (qnameToString x) t' e'
    C.EProofAbs prop e1             -> do p <- importType sc env prop
                                          env' <- bindProp sc prop p env
                                          e <- importExpr sc env' e1
                                          scLambda sc "_" p e
    C.EProofApp e1                  -> case fastSchemaOf (envC env) e1 of
                                         C.Forall [] (p1 : _) _ ->
                                           do e <- importExpr sc env e1
                                              -- TODO: Build a proof of the Prop if possible and apply it.
                                              p <- importType sc env p1
                                              prf <- scGlobalApply sc "Prelude.ProofApp" [p]
                                              scApply sc e prf
                                         s -> fail $ "EProofApp: invalid type: " ++ show (e1, s)
    C.ECast _expr _type             -> unimplemented "ECast"
    C.EWhere{} {-Expr [DeclGroup]-} -> unimplemented "EWhere"
  where
    go = importExpr sc env
    ty = importType sc env

-- TODO: move to Cryptol/TypeCheck/AST.hs
tIsSeq :: C.Type -> Maybe (C.Type, C.Type)
tIsSeq ty = case C.tNoUser ty of
              C.TCon (C.TC C.TCSeq) [n, a] -> Just (n, a)
              _                            -> Nothing

importMatches :: SharedContext s -> Env s -> [C.Match]
              -> IO (SharedTerm s, SharedTerm s, SharedTerm s, [(C.QName, C.Type)])
importMatches sc _env [] = do
  result <- scGlobalApply sc "Prelude.done" []
  n <- scNat sc 1
  a <- scDataTypeApp sc "Prelude.TUnit" []
  return (result, n, a, [])

importMatches sc env (C.From qname _ty expr : matches) = do
  let (len, ty) = fromJust (tIsSeq (fastTypeOf (envC env) expr))
  m <- importType sc env len
  a <- importType sc env ty
  xs <- importExpr sc env expr
  env' <- bindQName sc qname (C.Forall [] [] ty) a env
  (body, n, b, args) <- importMatches sc env' matches
  f <- scLambda sc (qnameToString qname) a body
  result <- scGlobalApply sc "Prelude.from" [a, b, m, n, xs, f]
  mn <- scGlobalApply sc "Prelude.mulENat" [m, n]
  ab <- scTupleType sc [a, b]
  return (result, mn, ab, (qname, ty) : args)

importMatches _sc _env (C.Let {} : _matches) = unimplemented "Let"

importComp :: SharedContext s -> Env s -> C.Expr -> [[C.Match]] -> IO (SharedTerm s)
importComp sc env _expr mss =
  do branches <- traverse (importMatches sc env) mss
     let zipAll [] = fail "zero-branch list comprehension"
         zipAll [(xs, m, a, _)] = return (xs, m, a)
         zipAll ((xs, m, a, _) : bs) =
           do (ys, n, b) <- zipAll bs
              zs <- scGlobalApply sc "Prelude.zipSeq" [a, b, m, n, xs, ys]
              mn <- scGlobalApply sc "Prelude.minENat" [m, n]
              ab <- scTupleType sc [a, b]
              return (zs, mn, ab)
     (zipped, _len, _ty) <- zipAll branches
     return zipped -- FIXME: need to map function over this
