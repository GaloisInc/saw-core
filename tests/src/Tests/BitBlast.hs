{-# LANGUAGE FlexibleInstances #-}
module Tests.BitBlast
  ( bitblastTests
  ) where

import Control.Exception
import Control.Monad
import qualified Data.Vector.Storable as SV

import Verinf.Symbolic
import qualified Verinf.Symbolic.Lit.ABC as ABC

import Verifier.SAW.BitBlast
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm

import Tests.Common

import Verifier.SAW.Conversion
import qualified Verifier.SAW.TermNet as Net

-- Add tests for different types of terms.
-- ExtConstant
-- Lambda
-- Tuple, Record
-- Boolean constants
-- And, or, xor.
-- Tuple Selector and record selctor.
-- Vector literal.

instance Eq (Matcher IO t b) where
  _ == _ = False

bitblastTestCase :: String
                 -> (SharedContext s -> IO (SharedTerm s))
                 -> (SV.Vector Bool -> Bool)
                 -> TestCase
bitblastTestCase nm mk_term is_valid =
  mkTestCase nm $ monadicIO $ run $ do
    bracket ABC.createBitEngine beFree $ \be -> do
      sc <- mkSharedContext preludeModule
      t <- mk_term sc
      Right (BBool l) <- bitBlast be t
      let Just satChecker = beCheckSat be
      Sat v <- satChecker l
      when (not (is_valid v)) $ fail "Unexpected SAT value."

bitblast_extcns :: TestCase
bitblast_extcns = bitblastTestCase "bitblast_extcns" mk_term is_valid
  where mk_term sc = do
          tp <- scPreludeBool sc
          scFreshGlobal sc "v" tp
        is_valid v = v == SV.singleton True

bitblast_bveq :: TestCase
bitblast_bveq = bitblastTestCase "bitblast_bveq" mk_term is_valid
  where mk_term sc = do
          w <- scNat sc 32
          vecType <- scPreludeVec sc
          i32 <- vecType w =<< scPreludeBool sc
          y <- scFreshGlobal sc "y" i32
          x <- scFreshGlobal sc "x" i32
          bvEq <- scApplyPreludeBvEq sc
          bvEq w x y
        is_valid v = SV.take 32 v == SV.drop 32 v
          

bitblastTests :: [TestCase]
bitblastTests =
  [ bitblast_extcns
  , bitblast_bveq
  ]