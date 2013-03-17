module TestSmtLib where

import qualified Data.Set as Set
import Data.Traversable
import SMTLib1.PP

import Verifier.SAW.Export.SmtLibTrans
import Verifier.SAW.ParserUtils
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

exampleParams :: SharedContext s
              -> SharedTerm s
              -> SharedTerm s
              -> [SharedTerm s]
              -> TransParams s
exampleParams sc w8 assm chk =
  TransParams
  { transName     = "Example"
  , transInputs   = [w8, w8]
  , transAssume   = assm
  , transCheck    = chk
  , transEnabled  = Set.empty
  , transExtArr   = False
  , transContext  = sc
  }

testSmtLib :: IO ()
testSmtLib = do
  sc <- mkSharedContext preludeModule
  i8 <- scFlatTermF sc (NatLit 8)
  let bvIdent = mkIdent (moduleName preludeModule) "Bitvector"
      eqIdent = mkIdent (moduleName preludeModule) "bvEq"
      neIdent = mkIdent (moduleName preludeModule) "bvNe"
      addIdent = mkIdent (moduleName preludeModule) "bvAdd"
  bv <- scFlatTermF sc (GlobalDef bvIdent)
  bvEq <- scFlatTermF sc (GlobalDef eqIdent)
  bvNe <- scFlatTermF sc (GlobalDef neIdent)
  bvAdd <- scFlatTermF sc (GlobalDef addIdent)
  w8 <- scApply sc bv i8
  let m = mkModuleName ["Example"]
  x <- scFreshGlobal sc "x" w8
  y <- scFreshGlobal sc "y" w8
  x' <- scApplyAll sc bvAdd [i8, x, x]
  y' <- scApplyAll sc bvAdd [i8, y, y]
  assm <- scApplyAll sc bvNe [i8, x, y]
  chk <- scApplyAll sc bvNe [i8, x', y']
  (scr, _) <- translate (exampleParams sc w8 assm [chk])
  print (pp scr)

defTerm :: Maybe TypedDef -> Term
defTerm (Just (Def _ _ [DefEqn [] e])) = e

scSharedTerm :: SharedContext s -> Term -> IO (SharedTerm s)
scSharedTerm sc = go
    where go (Term termf) = scTermF sc =<< traverse go termf
  
testSmtLibFile :: IO ()
testSmtLibFile = do
  m <- readModuleFromFile [preludeModule] "SMTTest.sawcore"
  sc <- mkSharedContext m
  let get = defTerm . findDef m . mkIdent (moduleName m)
  assm <- scSharedTerm sc (get "assm")
  chk <- scSharedTerm sc (get "chk")
  x <- scLookupDef sc (mkIdent (moduleName m) "x")
  w8 <- scTypeOf sc x
  (scr, _) <- translate (exampleParams sc w8 assm [chk])
  print (pp scr)
