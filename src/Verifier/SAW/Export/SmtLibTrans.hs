{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Export.SmtLibTrans
  ( translate
  , TransParams(..)
  , MetaData(..)
  ) where

import GHC.Exts(IsString(fromString))
import SMTLib1.QF_AUFBV as BV
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Prelude hiding (concat)
import Text.PrettyPrint

import qualified Verifier.SAW.SharedTerm as T
import qualified Verifier.SAW.TypedAST as T

data TransParams s = TransParams
  { transName     :: String
  , transInputs   :: [T.SharedTerm s] -- Input types
  , transAssume   :: T.SharedTerm s
  , transCheck    :: [T.SharedTerm s]
  , transEnabled  :: S.Set Ident -- Enabled operators
  , transExtArr   :: Bool
  , transContext  :: T.SharedContext s
  }

data MetaData = MetaData
  { trAsmp     :: Formula
  , trGoals    :: [Formula]
  , trInputs   :: [Ident]
  , trUninterp :: [(Ident, String)]
  , trDefined  :: M.Map String [ (V.Vector (BV.Term), BV.Term) ]
  , trArrays   :: M.Map Ident [Ident]
  }

translate :: TransParams s -> IO (Script, MetaData)
translate ps =
  toScript ps (transName ps) (transExtArr ps) $
  do (xs,ts) <- unzip `fmap` mapM mkInp (transInputs ps)
     let eval = translateTerm (transEnabled ps) ts
     as <- toForm =<< eval (transAssume ps)
     addAssumpt as
     gs <- mapM (toForm <=< eval) (transCheck ps)
     ops <- getExtraOps
     dops <- getDefinedOps
     arrs <- getArrayUpdates
     return ( Conn Not [ Conn And gs ]
            , MetaData
                { trAsmp = as
                , trGoals = gs
                , trInputs = xs
                , trUninterp = IM.elems ops
                , trDefined = M.fromList
                            [ (f, map fixupTerm $ M.toList m) |
                                                    (f,m) <- IM.elems dops ]
                , trArrays = arrs
                }
            )

  where
  fixupTerm (as,b) = (V.map asTerm as, asTerm b)

  toForm x = case asForm x of
               Nothing -> bug "translate" "Type error---not a formula"
               Just f  -> return f

  mkInp ty = do t    <- cvtType ty
                term <- newConst t
                x    <- toVar term
                addNote $ text "input:" <+> pp term <+> text "::" <+> text (show t)
                return (x, fromTerm t term)


type X = String

toScript :: TransParams s -> String -> Bool -> M s (Formula, a) -> IO (Script, a)
toScript ps n extArr (M m) =
  do res <- runErrorT $ runStateT (runReaderT m r0) s0
     case res of
       Left xx -> fail xx -- XXX: Throw a custom exception.
       Right ((a,other),s) -> return (Script
         { scrName     = fromString n
         , scrCommands =
           [ CmdLogic (fromString "QF_AUFBV")
           , CmdNotes $ show $ notes s
           , CmdExtraSorts (globalSorts s)
           , CmdExtraFuns
               [ FunDecl { funName = i
                         , funArgs = map toSort as
                         , funRes  = toSort b
                         , funAnnots = [] }
               | (i,as,b) <- globalDefs s
               ]
           , CmdExtraPreds
               [ PredDecl { predName = p
                          , predArgs = map toSort as
                          , predAnnots = [] }
               | (p,as) <- globalPreds s
               ]
           ] ++
           [ CmdAssumption f | f <- globalAsmps s
           ] ++
           [ CmdFormula a
           ]
         }
         , other
         )

    where s0 = S { names        = 0
                 , globalSorts  = []
                 , globalDefs   = []
                 , globalPreds  = []
                 , globalAsmps  = []
                 , extraAbs     = IM.empty
                 , extraDef     = IM.empty
                 , notes        = text "Detail about variables:"
                 , arrayUpdates = M.empty
                 , recTys       = M.empty
                 , seenTerms    = M.empty
                 , transParams  = ps
                 }
          r0 = R { useExtArr = extArr }

bug :: String -> String -> M s a
bug f x = M $ throwError $ unlines [ "Internal error."
                                   , "*** detected in: module SAWScript.SmtLib"
                                   , "*** function: " ++ f
                                   , "*** " ++ x
                                   ]


err :: String -> M s a
err x = M $ throwError $ unlines [ "Error while translating to SMTLIB:"
                                 , "*** " ++ x
                                 ]

toVar :: BV.Term -> M s Ident
toVar (App x [])  = return x
toVar _           = bug "translate.toVar" "Argument is not a variable"

--------------------------------------------------------------------------------
-- The Monad

newtype M s a = M (ReaderT R (StateT (S s) (ErrorT X IO)) a)
              deriving (Functor, Monad)

data R = R { useExtArr :: Bool }

data S s = S { names        :: !Int
             , globalSorts  :: [Sort]
             , globalDefs   :: [(Ident,[SmtType],SmtType)]
             , globalPreds  :: [(Ident,[SmtType])]
             , globalAsmps  :: [Formula]
             , extraAbs     :: IM.IntMap (Ident, String)  -- ^ uninterpreted ops
             , extraDef     :: IM.IntMap
                                (String, M.Map (V.Vector FTerm) FTerm)
                                                        -- ^ defined ops
             , arrayUpdates :: M.Map Ident [Ident]
             , recTys       :: M.Map String SmtType
             , seenTerms    :: M.Map T.TermIndex BV.Term
             , notes        :: Doc
             , transParams  :: TransParams s
             }

useExtArrays :: M s Bool
useExtArrays = M (useExtArr `fmap` ask)

state_ :: (MonadState s m) => (s -> s) -> m ()
state_ f = state (\s -> ((), f s))

addNote :: Doc -> M s ()
addNote d = M $ state_ $ \s -> s { notes = notes s $$ d }

addAssumpt :: Formula -> M s ()
addAssumpt f = M $ state_ $ \s -> s { globalAsmps = f : globalAsmps s }

addArrayUpdate :: Ident -> Ident -> M s ()
addArrayUpdate old new =
  M $ state_ $ \s -> s { arrayUpdates = M.insertWith (++) old [new]
                                                          (arrayUpdates s) }

getArrayUpdates :: M s (M.Map Ident [Ident])
getArrayUpdates = M $ arrayUpdates `fmap` get

getTransParams :: M s (TransParams s)
getTransParams = M $ transParams `fmap` get

getDefinedOps :: M s (IM.IntMap (String, M.Map (V.Vector FTerm) FTerm))
getDefinedOps = M $ extraDef `fmap` get

lkpDefinedOp :: Int -> V.Vector FTerm -> M s (Maybe FTerm)
lkpDefinedOp x ts =
  do mp <- getDefinedOps
     return (M.lookup ts . snd =<< IM.lookup x mp)

addDefinedOp :: Int -> String -> V.Vector FTerm -> FTerm -> M s ()
addDefinedOp x name ts t = M $ state_ $
  \s -> s { extraDef = IM.alter upd x (extraDef s) }
  where upd val = Just (case val of
                          Nothing -> (name,M.singleton ts t)
                          Just (n,mp) -> (n,M.insert ts t mp))

padArray :: SmtType -> BV.Term -> M s BV.Term
padArray ty@(TArray n w) t =
  do ext <- useExtArrays
     if ext
       then do let ixW = needBits n
               arr <- saveT ty t
               forM_ [ n .. 2^ixW - 1 ] $ \i ->
                 addAssumpt (select arr (bv i ixW) === bv 0 w)
               return arr
       else return t -- No need to pad, because we only compare
                     -- meaningful elements

padArray _ t = return t

getExtraOps :: M s (IM.IntMap (Ident, String))
getExtraOps = M $ extraAbs `fmap` get

-- Note: does not do any padding on arrays.
-- This happens where the fun is used.
newFun :: [SmtType] -> SmtType -> M s Ident
newFun ts t = M $ state $ \s -> let n = names s
                                    i = fromString ("x" ++ show n)
                                in ( i
                                   , s { names = n + 1
                                       , globalDefs = (i,ts,t) : globalDefs s
                                       }
                                   )

newPred :: [SmtType] -> M s Ident
newPred ts = M $ state $ \s -> let n = names s
                                   p = fromString ("p" ++ show n)
                               in ( p
                                  , s { names = n + 1
                                      , globalPreds = (p,ts) : globalPreds s
                                      }
                                  )

newConst :: SmtType -> M s BV.Term
newConst ty =
  do f <- newFun [] ty
     padArray ty (App f [])

-- Give an explicit name to a term.
-- This is useful so that we can share term representations.
-- Note that this assumes that we don't use "lets" in formulas,
-- (which we don't) because otherwise lifting things to the top-level
-- might result in undefined local variables.
saveT :: SmtType -> BV.Term -> M s BV.Term
saveT ty t =
  do ext <- useExtArrays
     let saveArr = case ty of
                     TArray {} -> ext
                     _ -> True
     case t of
       App _ (_ : _) | saveArr -> doSave
       ITE _ _ _     | saveArr -> doSave
       _ -> return t

  where doSave = do x <- newConst ty
                    addAssumpt (x === t)
                    addNote $ pp x <> char ':' <+> pp t
                    return x

saveF :: Formula -> M s Formula
saveF f =
  case f of
    FPred {}  -> return f
    FTrue     -> return f
    FFalse    -> return f

    FVar {}   -> bad "formula variables"
    Let {}    -> bad "term let"
    FLet {}   -> bad "formula let"

    _         -> do p <- newPred []
                    let f1 = FPred p []
                    addAssumpt (Conn Iff [f1,f])
                    addNote $ pp f1 <> char ':' <+> pp f
                    return f1

  where bad x = bug "saveF" ("We do not support " ++ x)

save :: FTerm -> M s FTerm
save t = do t1 <- saveT (smtType t) (asTerm t)
            f1 <- case asForm t of
                    Nothing -> return Nothing
                    Just f  -> Just `fmap` saveF f
            return t { asTerm = t1, asForm = f1 }

--------------------------------------------------------------------------------
-- Converting from SAWCore types into SMTLIB types.

-- | The array type contains the number of elements, not the
-- the number of bits, as in SMTLIB!
data SmtType = TBool
             | TArray Integer Integer
             | TBitVec Integer
             | TRecord [FldInfo]
               deriving (Eq,Ord,Show)

type Offset = Integer
type Width  = Integer

data FldInfo = FldInfo { fiName  :: String
                       , fiOff   :: Offset
                       , fiWidth :: Width
                       , _fiType :: SmtType
                       }
               deriving (Eq,Ord,Show)

preludeMod :: T.ModuleName
preludeMod = T.mkModuleName ["Prelude"]

preludeDef :: T.SharedTerm t -> Maybe String
preludeDef (T.STApp _ (T.FTermF (T.GlobalDef i)))
  | T.identModule i == preludeMod = Just (T.identName i)
  | otherwise = Nothing
preludeDef _ = Nothing

preludeIdent :: T.Ident -> Maybe String
preludeIdent i
  | T.identModule i == preludeMod = Just (T.identName i)
  | otherwise = Nothing

natValue :: T.SharedTerm t -> Maybe Integer
natValue (T.STApp _ (T.FTermF (T.NatLit n))) = Just n
natValue _ = Nothing

cvtType :: T.SharedTerm s -> M s SmtType
cvtType t@(T.STApp _ (T.FTermF ty)) =
  case ty of
    (T.App (preludeDef -> Just "Bitvector") (natValue -> Just n)) ->
      return $ TBitVec n
    (T.DataTypeApp (preludeIdent -> Just "Bool") []) -> return TBool
    (T.DataTypeApp (preludeIdent -> Just "Vec") [natValue -> Just n,
                                                 preludeDef -> Just "Bool"]) ->
      return $ TBitVec n
    (T.DataTypeApp (preludeIdent -> Just "Vec") [natValue -> Just n, e]) -> do
      et <- cvtType e
      case et of
        TBitVec m -> return $ TArray n m
        _ -> err "Complex nested array"
    (T.RecordType fs) -> do
      fts <- mapM cvtType (M.elems fs)
      let fields = zip (M.keys fs) fts
      return . TRecord . reverse . fst . foldl mkFldInfo ([], 0) $ fields
    -- We convert tuples like degenerate records.
    (T.TupleType fs) -> do
      fts <- mapM cvtType fs
      let fields = zip (map show [(1::Integer)..]) fts
      return . TRecord . reverse . fst . foldl mkFldInfo ([], 0) $ fields
    _ -> do
      tparams <- getTransParams
      err $ "Can't convert type to SMT-LIB: " ++
            T.scPrettyTerm (transContext tparams) t
cvtType t = do
  tparams <- getTransParams
  err $ "Can't convert type to SMT-LIB: " ++
        T.scPrettyTerm (transContext tparams) t

mkFldInfo :: ([FldInfo], Offset) -> (String, SmtType) -> ([FldInfo], Offset)
mkFldInfo (acc, accOff) (fldNm, fldTy) = (fi : acc, accOff + fiWidth fi)
  where
    w        = width fldTy
    fi       = FldInfo fldNm accOff w fldTy
    width ty = case ty of
                 TBool      -> 1
                 TArray x y -> x * y
                 TBitVec x  -> x
                 TRecord{}  -> width (flattenRecTy ty)

flattenRecTy :: SmtType -> SmtType
flattenRecTy (TRecord fis) = TBitVec $ sum (map fiWidth fis)
flattenRecTy ty            = ty

toSort :: SmtType -> Sort
toSort ty =
  case ty of
    TBool        -> tBitVec 1
    TArray x y   -> tArray (needBits x) y
    TBitVec n    -> tBitVec n
    x@TRecord{}  -> toSort $ flattenRecTy x

-- How many bits do we need to represent the given number.
needBits :: Integer -> Integer
needBits n | n <= 0     = 0
needBits n | odd n      = 1 + needBits (div n 2)
           | otherwise  = needBits (n + 1)



--------------------------------------------------------------------------------
{- We have two ways of translating boolean expressions: as a formula, or
as a term.  The type 'FTerm' allows us to do both.  Values of this type
should satisfy the following invariant:

fterm_prop f = case asForm f of
                 Just _  -> smtType f == TBool
                 Nothing -> smtType f /= TBool
-}

data FTerm = FTerm { asForm   :: Maybe Formula
                   , asTerm   :: BV.Term
                   , smtType  :: SmtType      -- Type of the term
                   } deriving (Show)

instance Eq FTerm  where x == y = asTerm x == asTerm y
instance Ord FTerm where compare x y = compare (asTerm x) (asTerm y)

-- This is useful for expressions that are naturally expressed as formulas.
toTerm :: Formula -> FTerm
toTerm f = FTerm { asForm = Just f
                 , asTerm = ITE f bit1 bit0
                 , smtType = TBool
                 }

fromTerm :: SmtType -> BV.Term -> FTerm
fromTerm ty t = FTerm { asForm = case ty of
                                   TBool -> Just (t === bit1)
                                   _     -> Nothing
                      , asTerm = t
                      , smtType = ty
                      }

--------------------------------------------------------------------------------

isConst :: T.SharedTerm s -> Bool
isConst (T.STApp _ (T.FTermF t)) =
  case t of
    T.ArrayValue _ _ -> True
    T.RecordValue _ -> True
    T.TupleValue _ -> True
    T.NatLit _ -> True
    T.CtorApp _ _ -> True
    _ -> False
isConst _ = False

unfoldApp :: T.SharedTerm s -> Maybe (T.SharedTerm s, [T.SharedTerm s])
unfoldApp (T.STApp _ (T.FTermF (T.App a b))) = do
  (f, xs) <- unfoldApp a
  return (f, xs ++ [b])
unfoldApp (T.STApp _ (T.FTermF (T.App f b))) = return (f, [b])
unfoldApp t@(T.STApp _ _) = return (t, [])
unfoldApp _ = Nothing

translateTerm :: S.Set Ident -> [FTerm] -> T.SharedTerm s -> M s FTerm
translateTerm _ inps (T.STVar n _ tp) = return (inps !! fromIntegral n)
translateTerm _ _ t | isConst t = mkConst t
translateTerm enabled inps t@(unfoldApp -> Just (f, xs)) = do
  tparams <- getTransParams
  case (preludeDef f, xs) of
    (Just "not", [_, a])       -> lift1 bNotOp a
    --(Just "bvNat", [_, a])     -> lift1 natToBVOp a
    (Just "bvEq", [_, a, b])   -> lift2 eqOp a b
    (Just "bvNe", [_, a, b])   -> lift2 neqOp a b
    (Just "and", [_, a, b])    -> lift2 bAndOp a b
    (Just "or", [_, a, b])     -> lift2 bOrOp a b
    (Just "xor", [_, a, b])    -> lift2 bXorOp a b
    (Just "bvAnd", [_, a, b])  -> lift2 iAndOp a b
    (Just "bvOr", [_, a, b])   -> lift2 iOrOp a b
    (Just "bvXor", [_, a, b])  -> lift2 iXorOp a b
    (Just "bvShl", [_, a, b])  -> lift2 shlOp a b
    (Just "bvSShr", [_, a, b]) -> lift2 shrOp a b
    (Just "bvShr", [_, a, b])  -> lift2 ushrOp a b
    (Just "append", [_, a, b]) -> lift2 appendOp a b
    (Just "bvAdd", [_, a, b])  -> lift2 addOp a b
    (Just "bvMul", [_, a, b])  -> lift2 mulOp a b
    (Just "bvSub", [_, a, b])  -> lift2 subOp a b
    (Just "bvSdiv", [_, a, b]) -> lift2 signedDivOp a b
    (Just "bvSrem", [_, a, b]) -> lift2 signedRemOp a b
    (Just "bvUdiv", [_, a, b]) -> lift2 unsignedDivOp a b
    (Just "bvUrem", [_, a, b]) -> lift2 unsignedRemOp a b
    (Just "bvsle", [_, a, b])  -> lift2 signedLeqOp a b
    (Just "bvslt", [_, a, b])  -> lift2 signedLtOp a b
    (Just "bvule", [_, a, b])  -> lift2 unsignedLeqOp a b
    (Just "bvult", [_, a, b])  -> lift2 unsignedLtOp a b
    (Just "get", [_, a, b])    -> lift2 getArrayValueOp a b
    (Just "ite", [_, a, b, c]) -> lift3 iteOp a b c
    (Just "set", [_, a, b, c]) -> lift3 setArrayValueOp a b c
    _                   ->
      err $ "Malformed application: " ++ T.scPrettyTerm sc t
        where sc = transContext tparams
  where
  liftTerm = save <=< translateTerm enabled inps
  lift1 op a = op =<< liftTerm a
  lift2 op a b = do
    [a', b'] <- mapM liftTerm [a, b]
    op a' b'
  lift3 op a b c = do
    [a', b', c'] <- mapM liftTerm [a, b, c]
    op a' b' c'
translateTerm _ inps (T.STApp _ (T.FTermF (T.RecordSelector e n))) =
  err $ "Record selector not yet implemented (TODO)"
translateTerm _ _ _ = err $ "Unhandled term in translation"

-- TODO: some cases from Verinf not currently handled
{-
translateOps :: S.Set OpIndex -> TermSemantics M s FTerm
translateOps enabled = termSem

        do as  <- mapM cvtType (V.toList (opArgTypes op))
           rty <- cvtType (opResultType op)

           let name       = opDefName op
               rslt t     = fromTerm rty `fmap` padArray rty t
               args'      = map asTerm (V.toList args)
               isCtor nms = name == "{ " ++ L.intercalate ", " nms ++ " }"
               isSel fis  = length args' == 1 && name `elem` map fiName fis

           case (rty, as) of
             -- Record constructor
             (TRecord fis, _) | isCtor (map fiName fis) ->
               rslt (foldr1 concat (reverse args'))

             -- Record selector
             (_, [TRecord fis]) | isSel fis ->
                 case L.find (\FldInfo{ fiName = n } -> n == name) fis of
                   Nothing -> bug "dynOp" "Failed to find FldInfo as expected"
                   Just fi -> case args' of
                     [t] -> rslt $ extract (fiOff fi + fiWidth fi - 1)
                                     (fiOff fi) t
                     _   -> bug "dynOp" "Expected single op arg"

             -- Uninterpreted ops
             _ ->
               do known <- getExtraOps
                  f     <- case IM.lookup x known of
                    Just (f,_) -> return f -- Already generated?
                    Nothing    -> -- Generate a function for this op
                      do f <- newFun as rty
                         M $ state $ \s ->
                           (f, s{ extraAbs = IM.insert x (f,name)
                                               (extraAbs s) })
                  rslt $ App f (map asTerm (V.toList args))
-}
--------------------------------------------------------------------------------
-- Operations

-- TODO: this doesn't preserve sharing within constants.
mkConst :: T.SharedTerm s -> M s FTerm
mkConst (T.STVar _ _ _) = bug "mkConst" "mkConst applied to variable"
mkConst (T.STApp _ (T.FTermF v)) =
  case v of
    T.ArrayValue ety vs -> do
      es <- mapM mkConst (V.toList vs)
      ty <- cvtType ety
      case ty of
        TBool -> err "can't create bit vector constants yet"
        TBitVec n -> mkArray (TArray (fromIntegral (V.length vs)) n) es
        _ -> err "invalid array element type"

    T.RecordValue vs -> err "record values not yet implemented (TODO)"
{-
      do let ts = map (TBitVec . fiWidth) (M.keys vs)
         xs <- mapM mkConst (M.elems vs)
         let ty = ArrayType TODO
         return FTerm { asForm = Nothing
                      , asTerm = foldr1 concat (reverse $ map asTerm xs)
                      , smtType = ty
                      }
-}

    -- We convert tuples like degenerate records.
    T.TupleValue vs -> err "tuple values not yet implemented (TODO)"
{-
      do let ts = map (TBitVec . fiWidth) (map show [1..])
         xs <- mapM (uncurry mkConst) (zip vs ts)
         let ty = RecordType TODO
         return FTerm { asForm = Nothing
                      , asTerm = foldr1 concat (reverse $ map asTerm xs)
                      , smtType = ty
                      }
-}
    T.NatLit i -> err $ "literal naturals not yet supported: " ++ show i
    _ -> bug "mkConst" "Internal---unhandled case shouldn't be possible."
mkConst (T.STApp _ _) = bug "mkConst" "applied to non-flat term"

-- NOTE: Arrays whose size is not a power of 2 are padded with 0s.
-- This is needed because otherwise  we can detect fake differences
-- between arrays, that are equal on their proper range, but differ
-- in the padding.
mkArray :: SmtType -> [FTerm] -> M s FTerm
mkArray t xs =
  case t of
    TArray n _ ->
      do a  <- newConst t
         let ixW = needBits n
         zipWithM_ (\i x -> addAssumpt (select a (bv i ixW) === x))
                   [ 0 .. ] (map asTerm xs)
         return FTerm { asForm = Nothing
                      , asTerm = a
                      , smtType = t
                      }

    _ -> bug "mkArray" "Type error---the type of mkArray is not an array."

{-
natToBVOp :: Int -> Int -> M s FTerm
natToBVOp w v =
  return FTerm { asForm = Nothing
               , asTerm = App ("nat2bv[" ++ show w ++ "]") [v]
               , smtType = TBitVec w
               }
-}

neqOp :: FTerm -> FTerm -> M s FTerm
neqOp t1 t2 = bNotOp =<< eqOp t1 t2

eqOp :: FTerm -> FTerm -> M s FTerm
eqOp t1 t2 =
  do ext <- useExtArrays
     if ext
       then return $ toTerm (asTerm t1 === asTerm t2)

       -- If we are aiming for a theory that does not support array
       -- extensionality (i.e. arrays are equal if their elems are equal),
       -- then we simulate the behavior by comparing each array element
       -- separately.  For large arrays, this can become big, of course.
       else case smtType t1 of
              TArray n v
                | n == 0  -> return FTerm { asForm  = Just FTrue
                                          , asTerm  = bit1
                                          , smtType = TBool
                                          }
                | otherwise ->
                    do a <- asTerm `fmap` save t1
                       b <- asTerm `fmap` save t2
                       let w        = needBits n
                           el arr i = fromTerm (TBitVec v) (select arr (bv i w))
                           rng      = [ 0 .. n - 1 ]
                           conj m1 m2 = do f1 <- m1
                                           f2 <- m2
                                           bAndOp f1 f2
                       foldr1 conj (zipWith eqOp [ el a i | i <- rng ]
                                                 [ el b i | i <- rng ])

              _ -> return $ toTerm (asTerm t1 === asTerm t2)

iteOp :: FTerm -> FTerm -> FTerm -> M s FTerm
iteOp t1 t2 t3 =
  case asForm t1 of
    Just b ->
      return FTerm { asForm = do s2 <- asForm t2
                                 s3 <- asForm t3
                                 return (Conn IfThenElse [b,s2,s3])
                   , asTerm = ITE b (asTerm t2) (asTerm t3)
                   , smtType = smtType t2   -- or t3
                   }
    Nothing -> bug "iteOpt"
                   "Type error---discriminator of ITE is not a formula."

truncOp :: Integer -> FTerm -> M s FTerm
truncOp n t =
  return FTerm { asForm = Nothing
               , asTerm = if n == 0 then bv 0 0
                                    else extract (n-1) 0 (asTerm t)
               , smtType = TBitVec n
               }

signedExtOp :: Integer -> FTerm -> M s FTerm
signedExtOp n t =
  case smtType t of
    TBitVec m | m < n  -> return FTerm { asForm = Nothing
                                       , asTerm = sign_extend (n - m) (asTerm t)
                                       , smtType = TBitVec n
                                       }
              | m == n -> return t
    _ -> bug "signedExtOp"
             "Sign extending to a smaller value, or type error."

bNotOp :: FTerm -> M s FTerm
bNotOp t = return FTerm { asForm = do a <- asForm t
                                      return (Conn Not [a])
                        , asTerm = bvnot (asTerm t)
                        , smtType = TBool
                        }

bAndOp :: FTerm -> FTerm -> M s FTerm
bAndOp s t = return FTerm { asForm = do a <- asForm s
                                        b <- asForm t
                                        return (Conn And [a,b])

                          , asTerm = bvand (asTerm s) (asTerm t)
                          , smtType = TBool
                          }

bOrOp :: FTerm -> FTerm -> M s FTerm
bOrOp s t  = return FTerm { asForm = do a <- asForm s
                                        b <- asForm t
                                        return (Conn Or [a,b])

                          , asTerm = bvor (asTerm s) (asTerm t)
                          , smtType = TBool
                          }

bXorOp :: FTerm -> FTerm -> M s FTerm
bXorOp s t  = return FTerm { asForm = do a <- asForm s
                                         b <- asForm t
                                         return (Conn Xor [a,b])

                          , asTerm = bvxor (asTerm s) (asTerm t)
                          , smtType = TBool
                          }

bImpliesOp :: FTerm -> FTerm -> M s FTerm
bImpliesOp s t  =
  case asForm s of
    Just f -> return FTerm { asForm = do b <- asForm t
                                         return (Conn Implies [f,b])

                           , asTerm = ITE f (asTerm t) bit0
                           , smtType = TBool
                           }
    Nothing -> bug "bImpliesOp" "Missing formula translation."

iNotOp :: FTerm -> M s FTerm
iNotOp t = return FTerm { asForm  = Nothing
                        , asTerm  = bvnot (asTerm t)
                        , smtType = smtType t
                        }

iAndOp :: FTerm -> FTerm -> M s FTerm
iAndOp s t  = return FTerm { asForm  = Nothing
                           , asTerm  = bvand (asTerm s) (asTerm t)
                           , smtType = smtType s
                           }

iOrOp :: FTerm -> FTerm -> M s FTerm
iOrOp s t   = return FTerm { asForm  = Nothing
                           , asTerm  = bvor (asTerm s) (asTerm t)
                           , smtType = smtType s
                           }

iXorOp :: FTerm -> FTerm -> M s FTerm
iXorOp s t   = return FTerm { asForm  = Nothing
                            , asTerm  = bvxor (asTerm s) (asTerm t)
                            , smtType = smtType s
                            }

mkShiftOp :: (BV.Term -> BV.Term -> BV.Term) -> FTerm -> FTerm -> M s FTerm
mkShiftOp f s t =
  case smtType s of
    TBitVec n ->
      do t1 <- coerce n t
         return FTerm { asForm  = Nothing
                      , asTerm  = f (asTerm s) (asTerm t1)
                      , smtType = smtType s
                      }
    _ -> bug "mkShiftOp" "Type error---shifting a non-bit vector"

shlOp :: FTerm -> FTerm -> M s FTerm
shlOp = mkShiftOp bvshl

shrOp :: FTerm -> FTerm -> M s FTerm
shrOp = mkShiftOp bvashr

ushrOp :: FTerm -> FTerm -> M s FTerm
ushrOp = mkShiftOp bvlshr

appendOp :: FTerm -> FTerm -> M s FTerm
appendOp s t    =
  case (smtType s, smtType t) of
    (TBitVec m, TBitVec n) ->
      return FTerm { asForm  = Nothing
                   , asTerm  = concat (asTerm t) (asTerm s)
                   , smtType = TBitVec (m + n)
                   }
    _ -> bug "appendOp" "Type error---arguments are not bit vectors"

addOp :: FTerm -> FTerm -> M s FTerm
addOp s t = return FTerm { asForm  = Nothing
                         , asTerm  = bvadd (asTerm s) (asTerm t)
                         , smtType = smtType s
                         }

mulOp :: FTerm -> FTerm -> M s FTerm
mulOp s t = return FTerm { asForm  = Nothing
                         , asTerm  = bvmul (asTerm s) (asTerm t)
                         , smtType = smtType s
                         }

subOp :: FTerm -> FTerm -> M s FTerm
subOp s t = return FTerm { asForm  = Nothing
                         , asTerm  = bvsub (asTerm s) (asTerm t)
                         , smtType = smtType s
                         }

negOp :: FTerm -> M s FTerm
negOp s = return FTerm { asForm  = Nothing
                       , asTerm  = bvneg (asTerm s)
                       , smtType = smtType s
                       }

signedDivOp :: FTerm -> FTerm -> M s FTerm
signedDivOp s t = return FTerm { asForm  = Nothing
                               , asTerm  = bvsdiv (asTerm s) (asTerm t)
                               , smtType = smtType s
                               }

signedRemOp :: FTerm -> FTerm -> M s FTerm
signedRemOp s t = return FTerm { asForm  = Nothing
                               , asTerm  = bvsdiv (asTerm s) (asTerm t)
                               , smtType = smtType s
                               }

unsignedDivOp :: FTerm -> FTerm -> M s FTerm
unsignedDivOp s t = return FTerm { asForm  = Nothing
                                 , asTerm  = bvudiv (asTerm s) (asTerm t)
                                 , smtType = smtType s
                                 }

unsignedRemOp :: FTerm -> FTerm -> M s FTerm
unsignedRemOp s t = return FTerm { asForm  = Nothing
                                 , asTerm  = bvurem (asTerm s) (asTerm t)
                                 , smtType = smtType s
                                 }

signedLeqOp :: FTerm -> FTerm -> M s FTerm
signedLeqOp s t = return $ toTerm $ bvsle (asTerm s) (asTerm t)

signedLtOp :: FTerm -> FTerm -> M s FTerm
signedLtOp s t = return $ toTerm $ bvslt (asTerm s) (asTerm t)

unsignedLeqOp :: FTerm -> FTerm -> M s FTerm
unsignedLeqOp s t = return $ toTerm $ bvule (asTerm s) (asTerm t)

unsignedLtOp :: FTerm -> FTerm -> M s FTerm
unsignedLtOp s t = return $ toTerm $ bvugt (asTerm t) (asTerm s)

coerce :: Integer -> FTerm -> M s FTerm
coerce w t =
  case smtType t of
    TBitVec n | n == w    -> return t
              | n > w     -> truncOp w t
              | otherwise -> return t {asTerm = zero_extend (w - n) (asTerm t)}
    _ -> bug "coerce" "Type error---coercing a non-bit vector"

getArrayValueOp :: FTerm -> FTerm -> M s FTerm
getArrayValueOp a i =
  case smtType a of
    TArray w n ->
      do j <- coerce (needBits w) i
         return FTerm { asForm  = Nothing
                      , asTerm  = select (asTerm a) (asTerm j)
                      , smtType = TBitVec n
                      }
    _ -> bug "getArrayValueOp" "Type error---selecting from a non-array."

setArrayValueOp :: FTerm -> FTerm -> FTerm -> M s FTerm
setArrayValueOp a i v =
  case smtType a of
    ty@(TArray w _) ->
      do ext <- useExtArrays
         j <- coerce (needBits w) i
         new <- if ext then do old <- saveT ty (asTerm a)
                               new <- saveT ty (store old (asTerm j) (asTerm v))
                               oi  <- toVar old
                               ni  <- toVar new
                               addArrayUpdate oi ni
                               return new
                       -- we can't save things without assuming equality
                       -- between arrays.
                       else return (store (asTerm a) (asTerm j) (asTerm v))
         return FTerm { asForm  = Nothing
                      , asTerm  = new
                      , smtType = smtType a
                      }
    _ -> bug "setArrayValueOp" "Type error---updating a non-array."

splitOp :: Integer -> Integer -> FTerm -> M s FTerm
splitOp l w t0 =
  do  t <- save t0
      let vs = [ FTerm { asForm  = Nothing
                       , asTerm  = extract ((i+1) * w - 1) (i * w) (asTerm t)
                       , smtType = TBitVec w
                       } | i <- [ 0 .. l - 1 ] ]
      mkArray (TArray l w) vs

joinOp :: Integer -> Integer -> FTerm -> M s FTerm
joinOp 0 _ _ = return FTerm { asForm = Nothing
                            , asTerm = bv 0 0
                            , smtType = TBitVec 0
                            }
joinOp l w t0 =
  do t <- save t0
     let n = needBits l
     return FTerm
       { asForm = Nothing
       , asTerm = foldr1 (flip concat)
                     [ select (asTerm t) (bv i n) | i <- [ 0 .. l - 1 ] ]
       , smtType = TBitVec (l * w)
       }
