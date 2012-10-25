module Verifier.SAW.DagTerm
  ( ParamType(..)
  , Builtin(..)
  , TermF(..)
  , DagTerm
  , DagEngine(..)
  , deFreshGlobal
  , deGroundSignedType
  , mkDagEngine
  ) where

import Verifier.SAW.AST (Ident, ParamType(..))



type DagTerm s = ()

data Builtin
  = IntegerToSigned
  | IntegerToUnsigned
  | OrdClass
  | NumClass
  | BitsClass
  | BoolType
  | TrueCtor
  | FalseCtor
  | IntegerType
  | SignedType
  | UnsignedType

data TermF e
  = BuiltinLit Builtin
  | IntegerLit Integer
  | App e e
  | TODO_DefinedTermF

data DagEngine s = DagEngine
  { deApply :: DagTerm s -> DagTerm s -> IO (DagTerm s)
  , deLambda :: ParamType -> Ident -> DagTerm s -> IO (DagTerm s) 
  , deFreshGlobalFn :: DagTerm s -> IO (DagTerm s)
  , deLocalVar   :: Integer -> IO (DagTerm s)
  , deBuiltin    :: Builtin -> IO (DagTerm s)
  , deInteger    :: Integer -> IO (DagTerm s)
    -- | Project application.
  , deProjectFn  :: DagTerm s -> IO (TermF (DagTerm s))
  }

deFreshGlobal :: (?de :: DagEngine s) => DagTerm s -> IO (DagTerm s)
deFreshGlobal = deFreshGlobalFn ?de

deGroundSignedType :: (?de :: DagEngine s) => Integer -> IO (DagTerm s)
deGroundSignedType w = do
  s <- deBuiltin ?de SignedType
  deApply ?de s =<< deInteger ?de w

mkDagEngine :: IO (DagEngine s)
mkDagEngine = do
  return DagEngine {
       deApply = undefined
     , deLambda = undefined
     , deFreshGlobalFn = undefined
     , deLocalVar = undefined
     , deBuiltin = undefined
     , deInteger = undefined
     , deProjectFn = undefined
     }