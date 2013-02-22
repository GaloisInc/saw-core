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
  bv <- scApplyPreludeBitvector sc
  {-
  i8 <- scFlatTermF sc (NatLit 8)
  i1 <- scFlatTermF sc (NatLit 1)
  w8 <- bv i8
  bvNe <- scApplyPreludeBvNe sc
  bvAdd <- scApplyPreludeBvAdd sc
  let m = mkModuleName ["Example"]
  x <- scFreshGlobal sc (mkIdent m "x") w8
  y <- scFreshGlobal sc (mkIdent m "y") w8
  x' <- bvAdd i8 x i1
  y' <- bvAdd i8 y i1
  assm <- bvNe i8 x y
  chk <- bvNe i8 x' y'
  (scr, _) <- translate (exampleParams sc w8 assm [chk])
  print (pp scr)
  -}
  return ()

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
