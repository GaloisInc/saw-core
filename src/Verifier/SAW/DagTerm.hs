module Verifier.SAW.DagTerm
  ( ParamType(..)
  , Builtin(..)
  , TermF(..)
  , DagTerm
  , DagEngine(..)
  , mkDagEngine
    -- ** Implicit versions of functions.
  , deApply
  , deApplyAll
  , deLambda
  , deGlobal
  , deFreshGlobal
  , deLocalVar
  , deBuiltin
  , deInteger
  , deProject
    -- ** Utilities.
  , deGroundSignedType
  , deGroundSignedValueFn
  , signedToSignedIdent
  ) where

import Control.Monad
import Data.Word

import Verifier.SAW.TypedAST

data DagTerm s = DagTerm Word64 (TermF (DagTerm s))

instance Eq (DagTerm s) where
  DagTerm i _ == DagTerm j _ = i == j

instance Ord (DagTerm s) where
  compare (DagTerm i _) (DagTerm j _) = compare i j

-- | Operations that are defined, but not 

signedToSignedIdent :: Ident
signedToSignedIdent = "signedToSigned"

data DagEngine s = DagEngine
  { deApplyFn :: DagTerm s -> DagTerm s -> IO (DagTerm s)
  , deLambdaFn :: ParamType -> Ident -> DagTerm s -> IO (DagTerm s) 
  , deGlobalFn :: Ident -> IO (Maybe (DagTerm s))
  , deFreshGlobalFn :: Ident -> DagTerm s -> IO (DagTerm s)
  , deLocalVarFn   :: Integer -> IO (DagTerm s)
  , deBuiltinFn    :: Builtin -> IO (DagTerm s)
  , deIntegerFn    :: Integer -> IO (DagTerm s)
    -- | Project term to an application.
  , deProjectFn  :: DagTerm s -> TermF (DagTerm s)
  }

deApply :: (?de :: DagEngine s) => DagTerm s -> DagTerm s -> IO (DagTerm s)
deApply = deApplyFn ?de

deApplyAll :: (?de :: DagEngine s) => DagTerm s -> [DagTerm s] -> IO (DagTerm s)
deApplyAll = foldM deApply

deLambda :: (?de :: DagEngine s) => ParamType -> Ident -> DagTerm s -> IO (DagTerm s) 
deLambda = deLambdaFn ?de

-- | Returns global function with given identifier.
deGlobal :: (?de :: DagEngine s) => Ident -> IO (Maybe (DagTerm s))
deGlobal = deGlobalFn ?de

deFreshGlobal :: (?de :: DagEngine s) => Ident -> DagTerm s -> IO (DagTerm s)
deFreshGlobal = deFreshGlobalFn ?de

deLocalVar :: (?de :: DagEngine s) => Integer -> IO (DagTerm s)
deLocalVar = deLocalVarFn ?de

deBuiltin :: (?de :: DagEngine s) => Builtin -> IO (DagTerm s)
deBuiltin = deBuiltinFn ?de

deInteger :: (?de :: DagEngine s) => Integer -> IO (DagTerm s)
deInteger = deIntegerFn ?de

deProject :: (?de :: DagEngine s) => DagTerm s -> TermF (DagTerm s)
deProject = deProjectFn ?de

deGroundSignedType :: (?de :: DagEngine s) => Integer -> IO (DagTerm s)
deGroundSignedType w = do
  s <- deBuiltin SignedType
  deApply s =<< deInteger w

deGroundSignedValueFn :: (?de :: DagEngine s) => Integer -> IO (Integer -> IO (DagTerm s))
deGroundSignedValueFn w = do
  f <- deBuiltin IntegerToSigned
  fw <- deApply f =<< deInteger w
  return $ deApply fw <=< deInteger

mkDagEngine :: IO (DagEngine s)
mkDagEngine = do
  return DagEngine {
       deApplyFn = undefined
     , deLambdaFn = undefined
     , deGlobalFn = undefined              
     , deFreshGlobalFn = undefined
     , deLocalVarFn = undefined
     , deBuiltinFn = undefined
     , deIntegerFn = undefined
     , deProjectFn = undefined
     }