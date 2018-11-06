{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Export.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Export.Coq where

import Control.Monad.Except
import Control.Monad.State
import Data.List (intersperse)
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Language.Coq.AST as Coq
import qualified Language.Coq.Pretty as Coq
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor
--import Verifier.SAW.Term.Pretty
import qualified Data.Vector as Vector (toList)

import Debug.Trace

data TranslationError a
  = NotSupported a
  | NotExpr a
  | NotType a
  | LocalVarOutOfBounds a
  | BadTerm a

showError :: (a -> String) -> TranslationError a -> String
showError printer err = case err of
  NotSupported a -> "Not supported: " ++ printer a
  NotExpr a      -> "Expecting an expression term: " ++ printer a
  NotType a      -> "Expecting a type term: " ++ printer a
  LocalVarOutOfBounds a -> "Local variable reference is out of bounds: " ++ printer a
  BadTerm a -> "Malformed term: " ++ printer a

instance {-# OVERLAPPING #-} Show (TranslationError Term) where
  show = showError showTerm
  
instance {-# OVERLAPPABLE #-} Show a => Show (TranslationError a) where
  show = showError show 
  
newtype CoqTrans a =
  CoqTrans {
    runCoqTrans :: StateT
                  [Coq.Decl]
                  (Either (TranslationError Term))
                  a
  }
  deriving (Applicative, Functor, Monad, MonadState [Coq.Decl])

instance MonadError (TranslationError Term) CoqTrans where
    throwError e = CoqTrans $ lift $ throwError e
    catchError (CoqTrans a) h = CoqTrans $ catchError a $ runCoqTrans . h

zipFilter :: [Bool] -> [a] -> [a]
zipFilter bs = map snd . filter fst . zip bs

showFTermF :: FlatTermF Term -> String
showFTermF = show . Unshared . FTermF

-- arg order: outermost binding first
globalArgsMap :: Map.Map Ident [Bool]
globalArgsMap = Map.fromList
  [ ("Prelude.append", [False, False, False, True, True])
  , ("Prelude.take", [False, True, False, True])
  , ("Prelude.drop", [False, False, True, True])
  , ("Prelude.Vec", [False, True])
  , ("Prelude.uncurry", [False, False, False, True])
  , ("Prelude.map", [False, False, True, False, True])
  , ("Prelude.bvXor", [False, True, True])
  , ("Prelude.zipWith", [False, False, False, True, False, True, True])
  , ("Prelude.coerce", [False, False, False, True])
  , ("Prelude.unsafeCoerce", [False, False, True])
  , ("Prelude.eq", [False, True, True])
  , ("Cryptol.ecEq", [False, False, True, True])
  , ("Cryptol.ecDemote", [True, True])
  -- Assuming only finite Cryptol sequences
  , ("Cryptol.ecCat", [False, False, False, True, True])
  , ("Cryptol.seq", [False, True])
  , ("Cryptol.seqZip", [False, False, False, False, True, True])
  , ("Cryptol.seqMap", [False, False, False, True, True])
  , ("Cryptol.ecJoin", [False, False, False, True])
  , ("Cryptol.ecSplit", [False, True, False, True])
  , ("Cryptol.ecSplitAt", [True, True, False, True])
  , ("Cryptol.ecXor", [False, True, True, True])
  , ("Cryptol.ecZero", [True, False])
  , ("Cryptol.PLogicSeq", [False, False, True])
  , ("Cryptol.PLogicSeqBool", [False])
  , ("Cryptol.PLogicWord", [False])
  ]

cryptolPreludeMap :: Map.Map String String
cryptolPreludeMap = Map.fromList
  [ ("repeat", "cryptolRepeat")
  , ("take", "cryptolTake")
  , ("drop", "cryptolDrop")
  , ("/\\", "(/\\)")
  ]

identMap :: Map.Map Ident Coq.Ident
identMap = Map.fromList
  [ ("Prelude.Bool", "bool")
  , ("Prelude.False", "false")
  , ("Prelude.True", "true")
  , ("Prelude.Nat", "nat")
  , ("Prelude.Vec", "list")
  , ("Prelude.append", "(++)")
  , ("Cryptol.ecCat", "(++)")
  , ("Prelude.take", "take") -- TODO: define
  , ("Prelude.drop", "drop") -- TODO: define
  , ("Prelude.zip", "zip") -- TODO: define
  , ("Cryptol.seq", "list")
  , ("Cryptol.seqZip", "zip") -- TODO: define
  , ("Prelude.zipWith", "zipWith") -- TODO: define
  , ("Prelude.uncurry", "prod_uncurry")
  , ("Prelude.map", "map")
  , ("Prelude.coerce", "id")
  , ("Prelude.unsafeCoerce", "id")
  , ("Cryptol.seqMap", "map")
  , ("Prelude.bvXor", "BVXor")
  , ("Cryptol.ecDemote", "cryptolECDemote") -- TODO: define
  , ("Cryptol.ecJoin", "cryptolECJoin") -- TODO: define
  , ("Cryptol.ecSplit", "cryptolECSplit") -- TODO: define
  , ("Cryptol.ecSplitAt", "cryptolECSplitAt") -- TODO: define
  , ("Cryptol.Num", "nat")
  , ("Cryptol.TCNum", "id")
  , ("Cryptol.tcAdd", "(+)")
  , ("Cryptol.tcSub", "(-)")
  , ("Cryptol.tcMul", "( * )")
  , ("Cryptol.ecEq", "(=)")
  , ("Prelude.eq", "(=)")
  , ("Cryptol.ecXor", "cryptolECXor") -- TODO: define
  , ("Cryptol.PLogicSeq", "cryptolPLogicSeq") -- TODO: define
  , ("Cryptol.PLogicSeqBool", "cryptolPLogicSeq") -- TODO: define
  , ("Cryptol.PLogicWord", "cryptolPLogicWord") -- TODO: define
  ]

filterArgs :: Ident -> [a] -> [a]
filterArgs i = maybe id zipFilter (Map.lookup i globalArgsMap)

translateIdent :: Ident -> Coq.Ident
translateIdent i = Map.findWithDefault (show i) i identMap

traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)
  
traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a

flatTermFToExpr ::
  (Term -> CoqTrans Coq.Term) ->
  FlatTermF Term ->
  CoqTrans Coq.Term
flatTermFToExpr go tf = traceFTermF "flatTermFToExpr" tf $
  case tf of
    GlobalDef i   -> pure (Coq.Var (translateIdent i))
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      -> pure (Coq.Var "unit")
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse go [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse go [x, y]
    PairLeft t    -> Coq.App (Coq.Var "fst") <$> traverse go [t]
    PairRight t   -> Coq.App (Coq.Var "snd") <$> traverse go [t]
    -- TODO: maybe have more customizable translation of data types
    DataTypeApp n is as -> do
      Coq.App (Coq.Var (translateIdent n)) <$> traverse go (is ++ as)
    -- TODO: maybe have more customizable translation of data constructors
    CtorApp n is as -> do
      Coq.App (Coq.Var (translateIdent n)) <$> traverse go (is ++ as)
    -- TODO: support this next!
    RecursorApp _ _ _ _ _ _ -> notSupported
    Sort s -> pure (Coq.Sort (if s == propSort then Coq.Prop else Coq.Type))
    NatLit i -> pure (Coq.NatLit i)
    ArrayValue _ vec ->
      (Coq.List . Vector.toList) <$> traverse go vec  -- TODO: special case bit vectors?
    StringLit _    -> notSupported
    ExtCns (EC _ _ _) -> notSupported
    _ -> notSupported -- TODO: remove once obsolete constructors removed
  where
    notSupported = throwError $ NotSupported errorTerm
    --badTerm = throwError $ BadTerm errorTerm
    errorTerm = Unshared $ FTermF tf
    --asString (asFTermF -> Just (StringLit s)) = pure s
    --asString _ = badTerm

-- | Recognizes an $App (App "Cryptol.seq" n) x$ and returns ($n$, $x$).
asSeq :: Monad f => Recognizer f Term (Term, Term)
asSeq t = do (f, args) <- asApplyAllRecognizer t
             fid <- asGlobalDef f
             case (fid, args) of
               ("Cryptol.seq", [n, x]) -> return (n,x)
               _ -> fail "not a seq"
                            
asApplyAllRecognizer :: Monad f => Recognizer f Term (Term, [Term])
asApplyAllRecognizer t = do _ <- asApp t
                            return $ asApplyAll t

mkDecl :: Coq.Ident -> Coq.Term -> Coq.Decl
mkDecl name (Coq.Lambda bs t) = Coq.Definition name bs Nothing t
mkDecl name t = Coq.Definition name [] Nothing t

translateParams :: Bool -> [String] -> [(String, Term)] -> CoqTrans [Coq.Binder]
translateParams _ _ [] = return []
translateParams traverseConsts env ((n, ty):ps) = do
  ty' <- translateTerm traverseConsts env ty
  ps' <- translateParams traverseConsts (n : env) ps
  return (Coq.Binder n (Just ty') : ps')

-- env is innermost first order
translateTerm :: Bool -> [String] -> Term -> CoqTrans Coq.Term
translateTerm traverseConsts env t = traceTerm "translateTerm" t $
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (go env) tf
    (asPi -> Just _) -> do
      paramTerms <- translateParams traverseConsts env params
      Coq.Pi <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asPiList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
    (asLambda -> Just _) -> do
      paramTerms <- translateParams traverseConsts env params
      Coq.Lambda <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asLambdaList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
    (asApp -> Just _) ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in case f of
           (asGlobalDef -> Just i) ->
             case i of
                "Prelude.ite" -> case args of
                  [_ty, c, tt, ft] ->
                    Coq.If <$> go env c <*> go env tt <*> go env ft
                  _ -> badTerm
                "Prelude.fix" -> case args of
                  [resultType, lambda] -> 
                    case resultType of
                      -- TODO: check that 'n' is finite
                      (asSeq -> Just (n, _)) ->
                        case lambda of
                          (asLambda -> Just (x, ty, body)) | ty == resultType -> do
                              len <- go env n
                              -- let len = EC.App (EC.ModVar "size") [EC.ModVar x]
                              expr <- go (x:env) body
                              typ <- go env ty
                              return $ Coq.App (Coq.Var "iter") [len, Coq.Lambda [Coq.Binder x (Just typ)] expr, Coq.List []]
                          _ -> badTerm   
                      _ -> notSupported
                  _ -> badTerm
                _ -> Coq.App <$> go env f
                             <*> traverse (go env) (filterArgs i args)
                  
           _ -> Coq.App <$> go env f
                        <*> traverse (go env) args
    (asLocalVar -> Just n)
      | n < length env -> Coq.Var <$> pure (env !! n)
      | otherwise -> throwError $ LocalVarOutOfBounds t
    (unwrapTermF -> Constant n body _) -> do
      decls <- get
      if | n `Map.member` cryptolPreludeMap ->
             Coq.Var <$> pure (cryptolPreludeMap Map.! n)
         | not traverseConsts || any (matchDecl n) decls -> Coq.Var <$> pure n
         | otherwise -> do
             b <- go env body
             modify (mkDecl n b :)
             Coq.Var <$> pure n
    _ -> {- trace "translateTerm fallthrough" -} notSupported
  where
    notSupported = throwError $ NotSupported t
    badTerm = throwError $ BadTerm t
    --matchDecl n (EC.OpDecl n' _ _) = n == n'
    matchDecl _ _ = False
    go = translateTerm traverseConsts

translateTermDoc :: Bool -> Term -> Either (TranslationError Term) Doc
translateTermDoc traverseConsts t = do
  (term, decls) <- runStateT (runCoqTrans $ translateTerm traverseConsts [] t) []
  return $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls) <$$>
           (if null decls then empty else hardline) <$$>
           Coq.ppTerm term

translateDefDoc :: Bool -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
translateDefDoc traverseConsts name t = do
  (term, decls) <- runStateT (runCoqTrans $ translateTerm traverseConsts [] t) []
  return $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls) <$$>
           (if null decls then empty else hardline) <>
           Coq.ppDecl (mkDecl name term)
