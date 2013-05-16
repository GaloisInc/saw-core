{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.SBVParser
  ( loadSBV
  , parseSBVPgm
  , UnintMap
  , Typ(..)
  ) where

import Control.Monad.State
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map

import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm
import qualified Verinf.SBV.Model as SBV

type NodeCache s = Map SBV.NodeId (SharedTerm s)

parseSBV :: NodeCache s -> SBV.SBV -> SC s (SBV.Size, SharedTerm s)
parseSBV _ (SBV.SBV size (Left num)) =
    do x <- scNat size
       y <- scNat num
       t <- scBvNat x y
       return (size, t)
parseSBV nodes (SBV.SBV size (Right nodeid)) =
    case Map.lookup nodeid nodes of
      Just t -> return (size, t)
      Nothing -> fail "parseSBV"

type UnintMap s = String -> Typ -> Maybe (SharedTerm s)

parseSBVExpr :: UnintMap s -> NodeCache s ->
                SBV.Size -> SBV.SBVExpr -> SC s (SharedTerm s)
parseSBVExpr _unint nodes _size (SBV.SBVAtom sbv) =
    liftM snd $ parseSBV nodes sbv
parseSBVExpr unint nodes size (SBV.SBVApp operator sbvs) =
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
                do (_size1, arg1) <- parseSBV nodes sbv1
                   (_size2, arg2) <- parseSBV nodes sbv2
                   (_size3, arg3) <- parseSBV nodes sbv3
                   -- assert size1 == 1 && size2 == size && size3 == size
                   s <- scBitvector size
                   cond <- scBv1ToBool arg1
                   scIte s cond arg2 arg3
            _ -> fail "parseSBVExpr: wrong number of arguments for if-then-else"
      SBV.BVShl -> shiftop scBvShl sbvs
      SBV.BVShr -> shiftop scBvShr sbvs
      SBV.BVRol -> shiftop (error "bvRol") sbvs
      SBV.BVRor -> shiftop (error "bvRor") sbvs
      SBV.BVExt hi lo ->
          case sbvs of
            [sbv1] ->
                do (size1, arg1) <- parseSBV nodes sbv1
                   unless (size == hi - lo + 1) (fail $ "parseSBVExpr BVExt: size mismatch " ++ show (size, hi, lo))
                   b <- scBoolType
                   s1 <- scNat lo
                   s2 <- scNat size
                   s3 <- scNat (size1 - 1 - hi)
                   -- SBV indexes bits starting with 0 = lsb.
                   scSlice b s1 s2 s3 arg1
            _ -> fail "parseSBVExpr: wrong number of arguments for extract"
      SBV.BVAnd -> binop scBvAnd sbvs
      SBV.BVOr  -> binop scBvOr  sbvs
      SBV.BVXor -> binop scBvXor sbvs
      SBV.BVNot ->
          case sbvs of
            [sbv1] ->
                do (size1, arg1) <- parseSBV nodes sbv1
                   s1 <- scNat size1
                   unless (size == size1) (fail $ "parseSBVExpr BVNot: size mismatch " ++ show (size, size1))
                   scBvNot s1 arg1
            _ -> fail "parseSBVExpr: wrong number of arguments for Not"
      SBV.BVEq  -> binrel scBvEq  sbvs
      SBV.BVGeq -> binrel scBvUGe sbvs
      SBV.BVLeq -> binrel scBvULe sbvs
      SBV.BVGt  -> binrel scBvUGt sbvs
      SBV.BVLt  -> binrel scBvULt sbvs
      SBV.BVApp ->
          case sbvs of
            [sbv1, sbv2] ->
                do (size1, arg1) <- parseSBV nodes sbv1
                   (size2, arg2) <- parseSBV nodes sbv2
                   s1 <- scNat size1
                   s2 <- scNat size2
                   unless (size == size1 + size2) (fail $ "parseSBVExpr BVApp: size mismatch " ++ show (size, size1, size2))
                   b <- scBoolType
                   -- SBV append takes the most-significant argument
                   -- first. This is in contrast to SAWCore, which
                   -- appends bitvectors in lsb-order; thus we have to
                   -- swap the arguments.
                   scAppend b s2 s1 arg2 arg1
            _ -> fail "parseSBVExpr: wrong number of arguments for append"
      SBV.BVLkUp indexSize resultSize ->
          do (size1 : inSizes, arg1 : args) <- liftM unzip $ mapM (parseSBV nodes) sbvs
             unless (size1 == indexSize && all (== resultSize) inSizes)
                        (fail $ "parseSBVExpr BVLkUp: size mismatch")
             n <- scNat (toInteger (length args))
             e <- scBitvector resultSize
             vec <- scVector e args
             fin <- return arg1 -- FIXME: cast arg1 to type Fin n
             scGet n e vec fin
      SBV.BVUnint _loc _codegen (name, irtyp) ->
          do let typ = parseIRType irtyp
             t <- case unint name typ of
               Just t -> return t
               Nothing ->
                   do -- putStrLn ("WARNING: unknown uninterpreted function " ++ show (name, typ, size))
                      scGlobalDef (mkIdent preludeName name)
             (inSizes, args) <- liftM unzip $ mapM (parseSBV nodes) sbvs
             let (TFun inTyp outTyp) = typ
             -- unless (typSizes inTyp == inSizes) (putStrLn ("ERROR parseSBVPgm: input size mismatch in " ++ name) >> print inTyp >> print inSizes)
             argument <- combineOutputs inTyp args
             result <- scApply t argument
             results <- splitInputs outTyp result
             let outSizes = typSizes outTyp
             scAppendAll (zip results outSizes)
    where
      -- | scMkOp :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
      binop scMkOp [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV nodes sbv1
             (size2, arg2) <- parseSBV nodes sbv2
             unless (size1 == size && size2 == size) (fail $ "parseSBVExpr binop: size mismatch " ++ show (size, size1, size2))
             s <- scNat size
             scMkOp s arg1 arg2
      binop _ _ = fail "parseSBVExpr: wrong number of arguments for binop"
      -- | scMkRel :: (x :: Nat) -> bitvector x -> bitvector x -> Bool;
      binrel scMkRel [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV nodes sbv1
             (size2, arg2) <- parseSBV nodes sbv2
             unless (size == 1 && size1 == size2) (fail $ "parseSBVExpr binrel: size mismatch " ++ show (size, size1, size2))
             s <- scNat size1
             t <- scMkRel s arg1 arg2
             scBoolToBv1 t
      binrel _ _ = fail "parseSBVExpr: wrong number of arguments for binrel"
      -- | scMkOp :: (x :: Nat) -> bitvector x -> Nat -> bitvector x;
      shiftop scMkOp [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV nodes sbv1
             (size2, arg2) <- parseSBV nodes sbv2
             unless (size1 == size) (fail "parseSBVExpr shiftop: size mismatch")
             s1 <- scNat size1
             s2 <- scNat size2
             amt <- scGlobalApply (mkIdent preludeName "bvToNat") [s2, arg2]
             scMkOp s1 arg1 amt
      shiftop _ _ = fail "parseSBVExpr: wrong number of arguments for binop"

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
parseSBVAssign :: UnintMap s -> NodeCache s -> SBVAssign -> SC s (NodeCache s)
parseSBVAssign unint nodes (SBVAssign size nodeid expr) =
    do term <- parseSBVExpr unint nodes size expr
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
typSizes (TFun _ _) = error "typSizes: not a first-order type"

scTyp :: Typ -> SC s (SharedTerm s)
scTyp TBool = scBoolType
scTyp (TFun a b) =
    do s <- scTyp a
       t <- scTyp b
       scFun s t
scTyp (TVec n TBool) =
    do scBitvector n
scTyp (TVec _ _) =
    error "scTyp: unimplemented"
scTyp (TTuple as) =
    do ts <- mapM scTyp as
       scTupleType ts
scTyp (TRecord fields) =
    do let (names, as) = unzip fields
       ts <-mapM scTyp as
       scRecordType (Map.fromList (zip names ts))

-- | projects all the components out of the input term
-- TODO: rename to splitInput?
splitInputs :: Typ -> SharedTerm s -> SC s [SharedTerm s]
splitInputs TBool x =
    do t <- error "Bool -> bitvector 1" x
       return [t]
splitInputs (TTuple ts) x =
    do xs <- mapM (scTupleSelector x) [1 .. length ts]
       yss <- sequence (zipWith splitInputs ts xs)
       return (concat yss)
splitInputs (TVec _ TBool) x = return [x]
splitInputs (TVec _ _) _ = error "splitInputs TVec: unimplemented"
splitInputs (TFun _ _) _ = error "splitInputs TFun: not a first-order type"
splitInputs (TRecord fields) x =
    do let (names, ts) = unzip fields
       xs <- mapM (scRecordSelect x) names
       yss <- sequence (zipWith splitInputs ts xs)
       return (concat yss)

----------------------------------------------------------------------

-- | Combines outputs into a data structure according to Typ
combineOutputs :: forall s. Typ -> [SharedTerm s] -> SC s (SharedTerm s)
combineOutputs ty xs0 =
    do (z, ys) <- runStateT (go ty) xs0
       unless (null ys) (fail "combineOutputs: too many outputs")
       return z
    where
      pop :: StateT [SharedTerm s] (SC s) (SharedTerm s)
      pop = do xs <- get
               case xs of
                 [] -> fail "combineOutputs: too few outputs"
                 y : ys -> put ys >> return y
      go :: Typ -> StateT [SharedTerm s] (SC s) (SharedTerm s)
      go TBool =
          do x <- pop
             lift (scBv1ToBool x)
      go (TTuple ts) =
          do xs <- mapM go ts
             lift (scTuple xs)
      go (TVec _ TBool) = pop
      go (TVec n t) =
          do xs <- replicateM (fromIntegral n) (go t)
             error "scArrayValue" xs
      go (TRecord fields) =
          do let (names, ts) = unzip fields
             xs <- mapM go ts
             lift (scMkRecord (Map.fromList (zip names xs)))
      go (TFun _ _) =
          fail "combineOutputs: not a first-order type"

----------------------------------------------------------------------

parseSBVPgm :: UnintMap s -> SBV.SBVPgm -> SC s (SharedTerm s)
parseSBVPgm unint (SBV.SBVPgm (_version, irtype, revcmds, _vcs, _warnings, _uninterps)) =
    do let (TFun inTyp outTyp) = parseIRType irtype
       let cmds = reverse revcmds
       let (assigns, inputs, outputs) = partitionSBVCommands cmds
       let inSizes = [ size | SBVInput size _ <- inputs ]
       let inNodes = [ node | SBVInput _ node <- inputs ]
       -- putStrLn ("inTyp: " ++ show inTyp)
       --putStrLn ("outTyp: " ++ show outTyp)
       --putStrLn ("inSizes: " ++ show inSizes)
       unless (typSizes inTyp == inSizes) (fail "parseSBVPgm: input size mismatch")
       inputType <- scTyp inTyp
       inputVar <- scLocalVar 0 inputType
       inputTerms <- splitInputs inTyp inputVar
       --putStrLn "processing..."
       let nodes0 = Map.fromList (zip inNodes inputTerms)
       nodes <- foldM (parseSBVAssign unint) nodes0 assigns
       --putStrLn "collecting output..."
       outputTerms <- mapM (liftM snd . parseSBV nodes) outputs
       outputTerm <- combineOutputs outTyp outputTerms
       scLambda "x" inputType outputTerm

----------------------------------------------------------------------
-- New SharedContext operations; should eventually move to SharedTerm.hs.

-- | bv1ToBool :: bitvector 1 -> Bool
-- bv1ToBool x = get 1 Bool x (FinVal 0 0)
scBv1ToBool :: SharedTerm s -> SC s (SharedTerm s)
scBv1ToBool x =
    do n0 <- scNat 0
       n1 <- scNat 1
       b <- scBoolType
       f0 <- scFlatTermF (CtorApp (mkIdent preludeName "FinVal") [n0, n0])
       scGet n1 b x f0

-- | boolToBv1 :: Bool -> bitvector 1
scBoolToBv1 :: SharedTerm s -> SC s (SharedTerm s)
scBoolToBv1 x =
    do b <- scBoolType
       scSingle b x

scAppendAll :: [(SharedTerm s, Integer)] -> SC s (SharedTerm s)
scAppendAll [] = error "scAppendAll: unimplemented"
scAppendAll [(x, _)] = return x
scAppendAll ((x, size1) : xs) =
    do let size2 = sum (map snd xs)
       b <- scBoolType
       s1 <- scNat size1
       s2 <- scNat size2
       y <- scAppendAll xs
       scAppend b s1 s2 x y

-- | get :: (n :: Nat) -> (e :: sort 1) -> Vec n e -> Fin n -> e;
scGet :: SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scGet n e v i = scGlobalApply (mkIdent preludeName "get") [n, e, v, i]

-- | single :: (e :: sort 1) -> e -> Vec 1 e;
-- single e x = generate 1 e (\(i :: Fin 1) -> x);
scSingle :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scSingle e x = scGlobalApply (mkIdent preludeName "single") [e, x]

scVector :: SharedTerm s -> [SharedTerm s] -> SC s (SharedTerm s)
scVector e xs =
  do singles <- mapM (scSingle e) xs
     scAppendAll [ (x, 1) | x <- singles ]

loadSBV :: FilePath -> IO SBV.SBVPgm
loadSBV = SBV.loadSBV
