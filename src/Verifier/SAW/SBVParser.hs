{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.SBVParser
  ( loadSBV
  , parseSBVPgm
  ) where

import Control.Monad (liftM, foldM, replicateM, unless)
import Control.Monad.State
import Control.Applicative
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map

import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm
import qualified Verinf.SBV.Model as SBV

type NodeCache s = Map SBV.NodeId (SharedTerm s)

parseSBV :: SharedContext s -> NodeCache s -> SBV.SBV -> IO (SBV.Size, SharedTerm s)
parseSBV sc nodes (SBV.SBV size (Left num)) =
    do x <- scNat sc size
       y <- scNat sc num
       t <- scBvNat sc x y
       return (size, t)
parseSBV sc nodes (SBV.SBV size (Right nodeid)) =
    case Map.lookup nodeid nodes of
      Just t -> return (size, t)
      Nothing -> fail "parseSBV"

parseSBVExpr :: SharedContext s -> NodeCache s -> SBV.Size -> SBV.SBVExpr -> IO (SharedTerm s)
parseSBVExpr sc nodes size (SBV.SBVAtom sbv) =
    liftM snd $ parseSBV sc nodes sbv
parseSBVExpr sc nodes size (SBV.SBVApp operator sbvs) =
    case operator of
      SBV.BVAdd -> binop scBvAdd sbvs
      SBV.BVSub -> binop scBvSub sbvs
      SBV.BVMul -> binop scBvMul sbvs
      SBV.BVDiv _loc -> binop (error "bvDiv") sbvs
      SBV.BVMod _loc -> binop (error "bvMod") sbvs
      SBV.BVPow -> binop (error "bvPow") sbvs
      SBV.BVIte ->
          case sbvs of
            [sbv1, sbv2, sbv3] ->
                do (size1, arg1) <- parseSBV sc nodes sbv1
                   (size2, arg2) <- parseSBV sc nodes sbv2
                   (size3, arg3) <- parseSBV sc nodes sbv3
                   -- assert size1 == 1 && size2 == size && size3 == size
                   s <- scBitvector sc size
                   cond <- scBv1ToBool sc arg1
                   scIte sc s cond arg2 arg3
            _ -> fail "parseSBVExpr: wrong number of arguments for if-then-else"
      SBV.BVShl -> shiftop scBvShl sbvs
      SBV.BVShr -> shiftop scBvShr sbvs
      SBV.BVRol -> shiftop (error "bvRol") sbvs
      SBV.BVRor -> shiftop (error "bvRor") sbvs
      SBV.BVExt hi lo ->
          case sbvs of
            [sbv1] ->
                do (size1, arg1) <- parseSBV sc nodes sbv1
                   unless (size == hi - lo + 1) (fail $ "parseSBVExpr BVExt: size mismatch " ++ show (size, hi, lo))
                   b <- scBoolType sc
                   s1 <- scNat sc lo
                   s2 <- scNat sc size
                   s3 <- scNat sc (size1 - 1 - hi)
                   scSlice sc b s1 s2 s3 arg1
            _ -> fail "parseSBVExpr: wrong number of arguments for extract"
      SBV.BVAnd -> binop scBvAnd sbvs
      SBV.BVOr  -> binop scBvOr  sbvs
      SBV.BVXor -> binop scBvXor sbvs
      SBV.BVNot ->
          case sbvs of
            [sbv1] ->
                do (size1, arg1) <- parseSBV sc nodes sbv1
                   s1 <- scNat sc size1
                   unless (size == size1) (fail $ "parseSBVExpr BVNot: size mismatch " ++ show (size, size1))
                   scBvNot sc s1 arg1
            _ -> fail "parseSBVExpr: wrong number of arguments for Not"
      SBV.BVEq  -> binrel scBvEq  sbvs
      SBV.BVGeq -> binrel scBvUGe sbvs
      SBV.BVLeq -> binrel scBvULe sbvs
      SBV.BVGt  -> binrel scBvUGt sbvs
      SBV.BVLt  -> binrel scBvULt sbvs
      SBV.BVApp ->
          case sbvs of
            [sbv1, sbv2] ->
                do (size1, arg1) <- parseSBV sc nodes sbv1
                   (size2, arg2) <- parseSBV sc nodes sbv2
                   s1 <- scNat sc size1
                   s2 <- scNat sc size2
                   unless (size == size1 + size2) (fail $ "parseSBVExpr BVApp: size mismatch " ++ show (size, size1, size2))
                   b <- scBoolType sc
                   scAppend sc b s1 s2 arg1 arg2
            _ -> fail "parseSBVExpr: wrong number of arguments for append"
      SBV.BVLkUp indexSize resultSize ->
          do (size1 : inSizes, arg1 : args) <- liftM unzip $ mapM (parseSBV sc nodes) sbvs
             unless (size1 == indexSize && all (== resultSize) inSizes)
                        (fail $ "parseSBVExpr BVLkUp: size mismatch")
             n <- scNat sc (toInteger (length args))
             e <- scBitvector sc resultSize
             vec <- scVector sc e args
             fin <- return arg1 -- FIXME: cast arg1 to type Fin n
             scGet sc n e vec fin
      SBV.BVUnint _loc _codegen (name, typ) -> error ("BNUnint: " ++ show (name, parseIRType typ))
    where
      -- | scMkOp :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
      binop scMkOp [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV sc nodes sbv1
             (size2, arg2) <- parseSBV sc nodes sbv2
             unless (size1 == size && size2 == size) (fail $ "parseSBVExpr binop: size mismatch " ++ show (size, size1, size2))
             s <- scNat sc size
             scMkOp sc s arg1 arg2
      binop scMkOp sbvs = fail "parseSBVExpr: wrong number of arguments for binop"
      -- | scMkRel :: (x :: Nat) -> bitvector x -> bitvector x -> Bool;
      binrel scMkRel [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV sc nodes sbv1
             (size2, arg2) <- parseSBV sc nodes sbv2
             unless (size == 1 && size1 == size2) (fail $ "parseSBVExpr binrel: size mismatch " ++ show (size, size1, size2))
             s <- scNat sc size1
             t <- scMkRel sc s arg1 arg2
             scBoolToBv1 sc t
      binrel scMkRel sbvs = fail "parseSBVExpr: wrong number of arguments for binrel"
      -- | scMkOp :: (x :: Nat) -> bitvector x -> Nat -> bitvector x;
      shiftop scMkOp [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV sc nodes sbv1
             (size2, arg2) <- parseSBV sc nodes sbv2
             unless (size1 == size) (fail "parseSBVExpr shiftop: size mismatch")
             s1 <- scNat sc size1
             s2 <- scNat sc size2
             amt <- scGlobalApply sc (mkIdent preludeName "bvToNat") [s2, arg2]
             scMkOp sc s1 arg1 amt
      shiftop scMkOp sbvs = fail "parseSBVExpr: wrong number of arguments for binop"

----------------------------------------------------------------------

data SBVAssign = SBVAssign SBV.Size SBV.NodeId SBV.SBVExpr
  deriving Show
data SBVInput = SBVInput SBV.Size SBV.NodeId
  deriving Show
type SBVOutput = SBV.SBV

partitionSBVCommands :: [SBV.SBVCommand] -> ([SBVAssign], [SBVInput], [SBVOutput])
partitionSBVCommands = foldr select ([], [], [])
    where
      select cmd (assigns, inputs, outputs) =
          case cmd of
            SBV.Decl _ (SBV.SBV _ (Left _)) _ ->
                error "invalid SBV command: ground value on lhs"
            SBV.Decl _ (SBV.SBV size (Right nodeid)) Nothing ->
                (assigns, SBVInput size nodeid : inputs, outputs)
            SBV.Decl _ (SBV.SBV size (Right nodeid)) (Just expr) ->
                (SBVAssign size nodeid expr : assigns, inputs, outputs)
            SBV.Output sbv ->
                (assigns, inputs, sbv : outputs)

-- TODO: Should I use a state monad transformer?
parseSBVAssign :: SharedContext s -> NodeCache s -> SBVAssign -> IO (NodeCache s)
parseSBVAssign sc nodes arg@(SBVAssign size nodeid expr) =
    do --print arg --debug
       term <- parseSBVExpr sc nodes size expr
       return (Map.insert nodeid term nodes)

----------------------------------------------------------------------

data Typ
  = TBool
  | TFun Typ Typ
  | TVec SBV.Size Typ
  | TTuple [Typ]
  | TRecord [(String, Typ)]

instance Show Typ where
  show TBool = "."
  show (TFun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TVec size t) = "[" ++ show size ++ "]" ++ show t
  show (TTuple ts) = "(" ++ intercalate "," (map show ts) ++ ")"
  show (TRecord fields) = "{" ++ intercalate "," (map showField fields) ++ "}"
    where showField (s, t) = s ++ ":" ++ show t

parseIRType :: SBV.IRType -> Typ
parseIRType (SBV.TApp "." []) = TBool
parseIRType (SBV.TApp "->" [a, b]) = TFun (parseIRType a) (parseIRType b)
parseIRType (SBV.TApp ":" [SBV.TInt n, a]) = TVec n (parseIRType a)
parseIRType (SBV.TApp c ts)
  | c == "(" ++ replicate (length ts - 1) ',' ++ ")" = TTuple (map parseIRType ts)
parseIRType (SBV.TRecord fields) =
    TRecord [ (name, parseIRType t) | (name, SBV.Scheme [] [] [] t) <- fields ]
parseIRType t = error ("parseIRType: " ++ show t)

typSizes :: Typ -> [SBV.Size]
typSizes TBool = [1]
typSizes (TTuple ts) = concatMap typSizes ts
typSizes (TVec n TBool) = [n]
typSizes (TVec n t) = concat (replicate (fromIntegral n) (typSizes t))
typSizes (TRecord fields) = concatMap (typSizes . snd) fields
typSizes (TFun t t') = error "typSizes: not a first-order type"

scTyp :: SharedContext s -> Typ -> IO (SharedTerm s)
scTyp sc TBool = scBoolType sc
scTyp sc (TFun a b) =
    do s <- scTyp sc a
       t <- scTyp sc b
       scFun sc s t
scTyp sc (TVec n TBool) =
    do scBitvector sc n
scTyp sc (TTuple as) =
    do ts <- mapM (scTyp sc) as
       scTupleType sc ts
scTyp sc (TRecord fields) =
    do let (names, as) = unzip fields
       ts <-mapM (scTyp sc) as
       scRecordType sc (Map.fromList (zip names ts))

-- | projects all the components out of the input term
-- TODO: rename to splitInput?
splitInputs :: SharedContext s -> Typ -> SharedTerm s -> IO [SharedTerm s]
splitInputs sc TBool x =
    do t <- error "Bool -> bitvector 1" x
       return [t]
splitInputs sc (TTuple ts) x =
    do xs <- mapM (scTupleSelector sc x) [1 .. length ts]
       yss <- sequence (zipWith (splitInputs sc) ts xs)
       return (concat yss)
splitInputs sc (TVec n TBool) x = return [x]
splitInputs sc (TVec n t) x = error "splitInputs TVec: unimplemented"
splitInputs sc (TFun _ _) _ = error "splitInputs TFun: not a first-order type"
splitInputs sc (TRecord fields) x =
    do let (names, ts) = unzip fields
       xs <- mapM (scRecordSelect sc x) names
       yss <- sequence (zipWith (splitInputs sc) ts xs)
       return (concat yss)

----------------------------------------------------------------------

-- | Combines outputs into a data structure according to Typ
combineOutputs :: forall s. SharedContext s -> Typ -> [SharedTerm s] -> IO (SharedTerm s)
combineOutputs sc ty xs =
    do (z, ys) <- runStateT (go ty) xs
       unless (null ys) (fail "combineOutputs: too many outputs")
       return z
    where
      pop :: StateT [SharedTerm s] IO (SharedTerm s)
      pop = do xs <- get
               case xs of
                 [] -> fail "combineOutputs: too few outputs"
                 y : ys -> put ys >> return y
      go :: Typ -> StateT [SharedTerm s] IO (SharedTerm s)
      go TBool =
          do x <- pop
             lift (scBv1ToBool sc x)
      go (TTuple ts) =
          do xs <- mapM go ts
             lift (scTuple sc xs)
      go (TVec n TBool) = pop
      go (TVec n t) =
          do xs <- replicateM (fromIntegral n) (go t)
             error "scArrayValue" xs
      go (TRecord fields) =
          do let (names, ts) = unzip fields
             xs <- mapM go ts
             lift (scMkRecord sc (Map.fromList (zip names xs)))
      go (TFun _ _) =
          fail "combineOutputs: not a first-order type"

----------------------------------------------------------------------

irtypeOf (SBV.SBVPgm (_, irtype, _, _, _, _)) = irtype
cmdsOf (SBV.SBVPgm (_, _, revcmds, _, _, _)) = reverse revcmds

parseSBVPgm :: SharedContext s -> SBV.SBVPgm -> IO (SharedTerm s)
parseSBVPgm sc (SBV.SBVPgm (_version, irtype, revcmds, _vcs, _warnings, _uninterps)) =
    do let (TFun inTyp outTyp) = parseIRType irtype
       let cmds = reverse revcmds
       let (assigns, inputs, outputs) = partitionSBVCommands cmds
       let inSizes = [ size | SBVInput size _ <- inputs ]
       let inNodes = [ node | SBVInput _ node <- inputs ]
       putStrLn ("inTyp: " ++ show inTyp)
       putStrLn ("outTyp: " ++ show outTyp)
       putStrLn ("inSizes: " ++ show inSizes)
       unless (typSizes inTyp == inSizes) (fail "parseSBVPgm: input size mismatch")
       inputType <- scTyp sc inTyp
       inputVar <- scLocalVar sc 0 inputType
       inputTerms <- splitInputs sc inTyp inputVar
       putStrLn "processing..."
       let nodes0 = Map.fromList (zip inNodes inputTerms)
       nodes <- foldM (parseSBVAssign sc) nodes0 assigns
       putStrLn "collecting output..."
       outputTerms <- mapM (liftM snd . parseSBV sc nodes) outputs
       outputTerm <- combineOutputs sc outTyp outputTerms
       scLambda sc "x" inputType outputTerm

----------------------------------------------------------------------
-- New SharedContext operations; should eventually move to SharedTerm.hs.

preludeName :: ModuleName
preludeName = mkModuleName ["Prelude"]

-- | bv1ToBool :: bitvector 1 -> Bool
-- bv1ToBool x = get 1 Bool x (FinVal 0 0)
scBv1ToBool :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
--scBv1ToBool sc x = scGlobalApply sc (mkIdent preludeName "bv1ToBool") [x]
scBv1ToBool sc x =
    do n0 <- scNat sc 0
       n1 <- scNat sc 1
       b <- scBoolType sc
       f0 <- scFlatTermF sc (CtorApp (mkIdent preludeName "FinVal") [n0, n0])
       scGlobalApply sc (mkIdent preludeName "get") [n1, b, x, f0]

-- | boolToBv1 :: Bool -> bitvector 1
scBoolToBv1 :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scBoolToBv1 sc x = scGlobalApply sc (mkIdent preludeName "boolToBv1") [x]

scAppendAll :: SharedContext s -> [(SharedTerm s, Integer)] -> IO (SharedTerm s)
scAppendAll sc [(x, _)] = return x
scAppendAll sc ((x, size1) : xs) =
    do let size2 = sum (map snd xs)
       b <- scBoolType sc
       s1 <- scNat sc size1
       s2 <- scNat sc size2
       y <- scAppendAll sc xs
       scAppend sc b s1 s2 x y

-- | get :: (n :: Nat) -> (e :: sort 1) -> Vec n e -> Fin n -> e;
scGet :: SharedContext s -> SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scGet sc n e v i = scGlobalApply sc (mkIdent preludeName "get") [n, e, v, i]

-- | single :: (e :: sort 1) -> e -> Vec 1 e;
-- single e x = generate 1 e (\(i :: Fin 1) -> x);
scSingle :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scSingle sc e x = scGlobalApply sc (mkIdent preludeName "single") [e, x]

scVector :: SharedContext s -> SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scVector sc e xs =
  do n <- scNat sc (toInteger (length xs))
     singles <- mapM (scSingle sc e) xs
     scAppendAll sc [ (x, 1) | x <- singles ]

loadSBV :: FilePath -> IO SBV.SBVPgm
loadSBV = SBV.loadSBV
