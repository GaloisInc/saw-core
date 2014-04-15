{-# OPTIONS_GHC -Wall -Werror #-}
{-# LANGUAGE OverloadedStrings #-}

module Verifier.SAW.Import.Cryptol where

import Control.Applicative
import Control.Monad (join)
import qualified Data.Map as Map
import Data.Traversable

import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Prims.Syntax as P

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST (mkSort)

{-
data Kind   = KType
            | KNum
            | KProp
            | Kind :-> Kind
-}

unimplemented :: Monad m => String -> m a
unimplemented name = fail ("unimplemented: " ++ name)

importKind :: SharedContext s -> C.Kind -> IO (SharedTerm s)
importKind sc kind =
  case kind of
    C.KType       -> scSort sc (mkSort 0)
    C.KNum        -> scDataTypeApp sc "Prelude.ENat" []
    C.KProp       -> scSort sc (mkSort 0)
    (C.:->) k1 k2 -> join $ scFun sc <$> importKind sc k1 <*> importKind sc k2

type TypeEnv s = Map.Map C.QName (SharedTerm s)

importType :: SharedContext s -> TypeEnv s -> C.Type -> IO (SharedTerm s)
importType sc env ty =
  case ty of
    C.TVar tvar ->
      case tvar of
        C.TVFree{} {- Int Kind (Set TVar) Doc -} -> unimplemented "TVFree"
        C.TVBound{} {- Int Kind -} -> unimplemented "TVBound"
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
            C.TCMin    -> unimplemented "TCMin" -- KNum :-> KNum :-> KNum
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

-- | Convert built-in constants to SAWCore.
importECon :: SharedContext s -> P.ECon -> IO (SharedTerm s)
importECon sc econ =
  case econ of
    P.ECTrue        -> scBool sc True
    P.ECFalse       -> scBool sc False
    P.ECDemote      -> unimplemented "ECDemote"      -- ^ Converts a numeric type into its corresponding value.
                                                     -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
    P.ECPlus        -> unimplemented "ECPlus"        -- {a} (Arith a) => a -> a -> a
    P.ECMinus       -> unimplemented "ECMinus"       -- {a} (Arith a) => a -> a -> a
    P.ECMul         -> unimplemented "ECMul"         -- {a} (Arith a) => a -> a -> a
    P.ECDiv         -> unimplemented "ECDiv"         -- {a} (Arith a) => a -> a -> a
    P.ECMod         -> unimplemented "ECMod"         -- {a} (Arith a) => a -> a -> a
    P.ECExp         -> unimplemented "ECExp"         -- {a} (Arith a) => a -> a -> a
    P.ECLg2         -> unimplemented "ECLg2"         -- {a} (Arith a) => a -> a
    P.ECNeg         -> unimplemented "ECNeg"         -- {a} (Arith a) => a -> a
    P.ECLt          -> unimplemented "ECLt"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECGt          -> unimplemented "ECGt"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECLtEq        -> unimplemented "ECLtEq"        -- {a} (Cmp a) => a -> a -> Bit
    P.ECGtEq        -> unimplemented "ECGtEq"        -- {a} (Cmp a) => a -> a -> Bit
    P.ECEq          -> unimplemented "ECEq"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECNotEq       -> unimplemented "ECNotEq"       -- {a} (Cmp a) => a -> a -> Bit
    P.ECFunEq       -> unimplemented "ECFunEq"       -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
    P.ECFunNotEq    -> unimplemented "ECFunNotEq"    -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
    P.ECMin         -> unimplemented "ECMin"         -- {a} (Cmp a) => a -> a -> a
    P.ECMax         -> unimplemented "ECMax"         -- {a} (Cmp a) => a -> a -> a
    P.ECAnd         -> unimplemented "ECAnd"         -- {a} a -> a -> a        -- Bits a
    P.ECOr          -> unimplemented "ECOr"          -- {a} a -> a -> a        -- Bits a
    P.ECXor         -> unimplemented "ECXor"         -- {a} a -> a -> a        -- Bits a
    P.ECCompl       -> unimplemented "ECCompl"       -- {a} a -> a             -- Bits a
    P.ECZero        -> unimplemented "ECZero"        -- {a} a                  -- Bits a
    P.ECShiftL      -> unimplemented "ECShiftL"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECShiftR      -> unimplemented "ECShiftR"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECRotL        -> unimplemented "ECRotL"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECRotR        -> unimplemented "ECRotR"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECCat         -> unimplemented "ECCat"         -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
    P.ECSplitAt     -> unimplemented "ECSplitAt"     -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
    P.ECJoin        -> unimplemented "ECJoin"        -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
    P.ECSplit       -> unimplemented "ECSplit"       -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
    P.ECReverse     -> unimplemented "ECReverse"     -- {a,b} (fin a) => [a] b -> [a] b
    P.ECTranspose   -> unimplemented "ECTranspose"   -- {a,b,c} [a][b]c -> [b][a]c
    P.ECAt          -> unimplemented "ECAt"          -- {n,a,m} [n]a -> [m] -> a
    P.ECAtRange     -> unimplemented "ECAtRange"     -- {n,a,m,i} [n]a -> [m][i] -> [m]a
    P.ECAtBack      -> unimplemented "ECAtBack"      -- {n,a,m} (fin n) => [n]a -> [m] -> a
    P.ECAtRangeBack -> unimplemented "ECAtRangeBack" -- {front,back,a} (fin front) => [front + back]a -> ([front]a, [back]a)
    P.ECFromThen    -> unimplemented "ECFromThen"
                               -- fromThen : {first,next,bits}
                               --             ( fin first, fin next, fin bits
                               --             , bits >= width first, bits >= width next
                               --             , lengthFromThen first next bits == len
                               --             )
                               --          => [len] [bits]
    P.ECFromTo      -> unimplemented "ECFromTo"
    P.ECFromThenTo  -> unimplemented "ECFromThenTo"
    P.ECInfFrom     -> unimplemented "ECInfFrom"     -- {a} (fin a) => [a] -> [inf][a]
    P.ECInfFromThen -> unimplemented "ECInfFromThen" -- {a} (fin a) => [a] -> [a] -> [inf][a]
    P.ECError       -> unimplemented "ECError"       -- {at,len} (fin len) => [len][8] -> at -- Run-time error
    P.ECPMul        -> unimplemented "ECPMul"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
    P.ECPDiv        -> unimplemented "ECPDiv"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
    P.ECPMod        -> unimplemented "ECPMod"        -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
    P.ECRandom      -> unimplemented "ECRandom"      -- {a} => [32] -> a -- Random values

type ExprEnv s = Map.Map C.QName (SharedTerm s)
type Env s = (TypeEnv s, ExprEnv s)

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
    C.EIf _e1 _e2 _e3               -> unimplemented "EIf" -- join $ scIte sc <$> go e1 <*> go e2 <*> go e3
    C.EComp{} {-Type Expr [[Match]]-} -> unimplemented "EComp" -- ^ List comprehensions The type caches the type of the expr.
    C.EVar _qName                   -> unimplemented "EVar" -- ^ Use of a bound variable
    C.ETAbs _tParam _expr           -> unimplemented "ETAbs" -- ^ Function Value
    C.ETApp e t                     -> join $ scApply sc <$> go e <*> ty t
    C.EApp e1 e2                    -> join $ scApply sc <$> go e1 <*> go e2
    C.EAbs qname t e                -> join $ scLambda sc (qnameToString qname) <$> ty t <*> go e
    C.EProofAbs {- x -} _prop _expr -> unimplemented "EProofAbs"
    C.EProofApp _expr {- proof -}   -> unimplemented "EProofApp"
    C.ECast _expr _type             -> unimplemented "ECast"
    C.EWhere{} {-Expr [DeclGroup]-} -> unimplemented "EWhere"
  where
    go = importExpr sc env
    ty = importType sc (fst env)
