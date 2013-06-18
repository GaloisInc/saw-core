{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module Verifier.SAW.Import.AIG 
  ( readAIG
  , parseVerinfViaAIG
  , translateNetwork
  , withReadAiger
  ) where

import Control.Applicative
import Control.Exception
import Control.Lens
import Control.Monad
import Control.Monad.Error
import Control.Monad.State.Strict
import Verinf.Symbolic.Lit.ABC_GIA
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.Leijen hiding ((<$>))

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm

import Verinf.Symbolic.Common (lMkLitResultForType)
import Verinf.Symbolic ( BitWidth(..)
                       , WidthExpr, widthConstant
                       , DagType(..)
                       , DagEngine
                       , deInputTerms
                       , DagTerm
                       , mkBitBlastTermSemantics
                       , flattenLitResult
                       , evalDagTermFn
                       , termType
                       )


sharedTermFromWidthExpr :: SharedContext s
                        -> WidthExpr
                        -> ErrorT String IO (SharedTerm s)
sharedTermFromWidthExpr sc (widthConstant -> Just (Wx w)) = do
  lift $ scNat sc (toInteger w)
sharedTermFromWidthExpr _ _ = fail "Cannot bitblast non-ground width expressions."

sharedTermFromDagType :: SharedContext s
                    -> DagType
                    -> ErrorT String IO (SharedTerm s)
sharedTermFromDagType sc tp =
  case tp of
    SymBool -> lift $ scPreludeBool sc
    SymInt w -> do
      wt <- sharedTermFromWidthExpr sc w
      lift $ ($ wt) =<< scApplyPreludeBitvector sc
    SymArray w etp -> do
      wt <- sharedTermFromWidthExpr sc w
      tpt <- sharedTermFromDagType sc etp
      lift $ do
        vecFn <- scPreludeVec sc
        vecFn wt tpt
    SymRec{} -> fail "Verinf records not yet supported."
    SymShapeVar{}  -> fail "Cannot bitblast polymorphic functions"

parseVerinfViaAIG :: SharedContext s
                  -> DagEngine
                  -> DagTerm
                  -> IO (Either String (SharedTerm s))
parseVerinfViaAIG sc de t = do
  inputTypes <- fmap termType <$> deInputTerms de
  bracket createEmptyNetwork freeNetwork $ \ntk -> do
  inputs <- V.mapM (lMkLitResultForType (appendNetworkInput ntk)) inputTypes
  -- Get output bits for term.
  let inputFn i _ = return (inputs V.! i)
  let ts = mkBitBlastTermSemantics (bitEngineForNetwork ntk)
  evalFn <- evalDagTermFn inputFn ts
  lv <- flattenLitResult <$> evalFn t
  runErrorT $ do
    argTypes <- mapM (sharedTermFromDagType sc) (V.toList inputTypes)
    resType <- sharedTermFromDagType sc (termType t)
    translateNetwork sc ntk lv (("_",) <$> argTypes) resType

type TypeParser s = StateT (V.Vector (SharedTerm s)) (ErrorT String IO)

runTypeParser :: V.Vector (SharedTerm s)
              -> TypeParser s a
              -> ErrorT String IO (a, V.Vector (SharedTerm s))
runTypeParser v m = runStateT m v

bitblastSharedTerm :: SharedContext s
                   -> SharedTerm s -- ^ Term for input variable
                   -> SharedTerm s -- ^ Term for type.
                   -> TypeParser s ()
bitblastSharedTerm _ v (asBoolType -> Just ()) = do
  modify (`V.snoc` v)
bitblastSharedTerm sc v (asBitvectorType -> Just w) = do
  inputs <- liftIO $ do
    getFn <- scApplyPreludeGet sc
    wt <- scNat sc w
    boolType <- scPreludeBool sc
    V.generateM (fromInteger w) $ \i -> do
      getFn wt boolType v =<< scFinConst sc (toInteger i) w
  modify (V.++ inputs)
bitblastSharedTerm _ _ tp = fail $ show $
  text "Could not parse AIG input type:" <$$>
  indent 2 (scPrettyTermDoc tp)

parseAIGResultType :: SharedContext s
                   -> SharedTerm s -- ^ Term for type
                   -> TypeParser s (SharedTerm s)
parseAIGResultType _ (asBoolType -> Just ()) = do
  outputs <- get
  when (V.length outputs == 0) $ do
    fail "Not enough output bits for Bool result."
  put (V.drop 1 outputs)
  -- Return remaining as a vector.
  return (outputs V.! 0)  
parseAIGResultType sc (asBitvectorType -> Just w) = do
  outputs <- get
  when (V.length outputs < fromInteger w) $ do
    fail "Not enough output bits for type."
  let (base,remaining) = V.splitAt (fromInteger w) outputs
  put remaining
  -- Return remaining as a vector.
  liftIO $ do
    boolType <- scPreludeBool sc
    scVector sc boolType (V.toList base)  
parseAIGResultType _ _ = fail "Could not parse AIG output type."


-- | 
networkAsSharedTerms
    :: Network
    -> SharedContext s
    -> V.Vector (SharedTerm s) -- ^ Input terms for AIG
    -> V.Vector Lit -- ^ Outputs 
    -> IO (V.Vector (SharedTerm s))
networkAsSharedTerms ntk sc inputTerms outputLits = do
  -- Get evaluator
  scNot <- scApplyPreludeNot sc
  scAnd <- scApplyPreludeAnd sc
  scFalse <- scApplyPreludeFalse sc
  let viewFn (AndLit x y) = do
        --putStrLn "AndLit"
        scAnd x y
      viewFn (NotLit x) = scNot x
      viewFn (InputLit i) = return $ inputTerms V.! i
      viewFn FalseLit = return scFalse
  evalFn <- litEvaluator ntk viewFn     
  traverse evalFn outputLits

-- | Create vector for each input literal from expected types.
bitblastVarsAsInputLits :: forall s
                       . SharedContext s
                      -> [SharedTerm s]
                      -> ErrorT String IO (V.Vector (SharedTerm s))
bitblastVarsAsInputLits sc args = do
  let n = length args
  let mkLocalVar :: Int -> SharedTerm s -> IO (SharedTerm s)
      mkLocalVar i tp = scLocalVar sc idx tp
          -- Earlier arguments have a higher deBruijn index.
          where idx = (n - i - 1)
  inputs <- liftIO $ zipWithM mkLocalVar [0..] args
  fmap snd $ runTypeParser V.empty $ do
    zipWithM_ (bitblastSharedTerm sc) inputs args

withReadAiger :: FilePath
              -> (Network -> IO (Either String a))
              -> IO (Either String a)
withReadAiger path action = do
  mntk <- readAiger path
  case mntk of
    Nothing -> return $ Left $ "Could not read AIG file " ++ show path ++ "."
    Just ntk -> finally (action ntk) (freeNetwork ntk)

translateNetwork :: SharedContext s -- ^ Context to build in term.
                 -> Network -- ^ Network to bitblast
                 -> SV.Vector Lit -- ^ Outputs for network.
                 -> [(String, SharedTerm s)] -- ^ Expected types
                 -> SharedTerm s -- ^ Expected output type.
                 -> ErrorT String IO (SharedTerm s)
translateNetwork sc ntk outputLits args resultType = do
  --lift $ putStrLn "inputTerms"
  inputTerms <- bitblastVarsAsInputLits sc (snd <$> args)
  -- Check number of inputs to network matches expected inputs.
  do let expectedInputCount = V.length inputTerms
     aigCount <- liftIO $ networkInputCount ntk
     unless (expectedInputCount == aigCount) $ do
       fail $ "AIG has " ++ show aigCount
                 ++ " inputs, while expected type has "
                 ++ show expectedInputCount ++ " inputs."
  --lift $ putStrLn "Output vars"
  -- Get outputs as SAWCore terms.
  outputVars <- liftIO $
    networkAsSharedTerms ntk sc inputTerms (V.fromList (SV.toList outputLits))
  --lift $ putStrLn "Type parser"
   -- Join output lits into result type.
  (res,rargs) <- runTypeParser outputVars $ parseAIGResultType sc resultType
  unless (V.null rargs) $
    fail "AIG contains more outputs than expected."      
  lift $ scLambdaList sc args res

readAIG :: forall s 
         . SharedContext s -- ^ Context to build in term.
        -> FilePath        -- ^ Path to AIG
        -> SharedTerm s    -- ^ Expected type of term.
        -> IO (Either String (SharedTerm s))
readAIG sc path aigType =
  withReadAiger path $ \ntk -> do
    --putStrLn "Network outputs"
    outputLits <- networkOutputs ntk
    let (args,resultType) = asPiList aigType
    runErrorT $
      translateNetwork sc ntk outputLits args resultType
