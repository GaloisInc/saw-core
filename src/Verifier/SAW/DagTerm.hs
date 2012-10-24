module Verifier.SAW.DagTerm
  where

type DagTerm = ()

data DagEngine = DagEngine {
    deApply :: DagTerm -> DagTerm -> IO DagTerm
  , deFreshInput :: DagTerm -> IO DagTerm
  , deLocalVar :: Integer -> IO DagTerm 
  }