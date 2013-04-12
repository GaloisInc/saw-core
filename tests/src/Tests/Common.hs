module Tests.Common 
  ( module Test.QuickCheck
  , module Tests.Common
  ) where

import Control.Monad
import Test.QuickCheck
import Test.QuickCheck.Test

data TestCase = TestCase String Args Property

mkTestCase :: Testable p => String -> p -> TestCase
mkTestCase nm p = TestCase nm stdArgs { maxSuccess = 1 } (property p)

runTestCases :: [TestCase] -> IO Bool
runTestCases tcl = do
  let n = length tcl
  results <- forM ([0..] `zip` tcl) $ \(i, TestCase nm a p) -> do
    putStrLn $ " " ++ nm ++ "[" ++ show i ++ "/" ++ show n ++ "]..."
    quickCheckWithResult a p
  return $ all isSuccess results
