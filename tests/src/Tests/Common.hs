{- |
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Tests.Common 
  ( module Test.QuickCheck
  , module Test.QuickCheck.Monadic
  , module Tests.Common
  , unless, when
  ) where

import Control.Applicative
import Control.Monad
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.QuickCheck.Test

data TestCase = TestCase String Args Property

testCaseName :: TestCase -> String
testCaseName (TestCase nm _ _) = nm

mkTestCase :: Testable p => String -> p -> TestCase
mkTestCase nm p = TestCase nm stdArgs { maxSuccess = 1 } (property p)

runNamed :: String -> (a -> String) -> [a] -> (a -> IO b) -> IO [b]
runNamed prefix nfn l act = do
  let n = length l
  forM ([1..] `zip` l) $ \(i,a) -> do
    putStrLn $ prefix ++ " " ++ nfn a ++ "[" ++ show i ++ "/" ++ show n ++ "]..."
    act a

runTestCases :: [(String, [TestCase])] -> IO Bool
runTestCases tcl = do
  let n = length tcl
  results <- fmap concat $ runNamed "***" fst tcl $ \(_,gl) -> do
    runNamed "  " testCaseName gl $ \(TestCase nm a p) -> do
      quickCheckWithResult a p
  return $ all isSuccess results