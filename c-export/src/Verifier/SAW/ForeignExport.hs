{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
-- Allow type signatures to be left out, because they must be
-- duplicated in the foreign export lines.

{- |
Module      : Verifier.SAW.ForeignExport
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.ForeignExport() where

import Foreign.C
import Foreign.StablePtr

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

expModule :: Module
expModule = emptyModule (mkModuleName ["Verifier", "SAW", "ForeignExport"])

saw_new_context = mkSharedContext expModule >>= newStablePtr

saw_free = freeStablePtr

with_context     f p = deRefStablePtr p >>= f >>= newStablePtr
--with_term        f p = deRefStablePtr p >>= f >>= newStablePtr
with_term_string f p = deRefStablePtr p >>= f >>= newCString

{-
bv_binop f scp ap bp = do
  sc <- derefStablePtr scp
  a <- derefStablePtr ap
  ty <- scTypeOf sc a
  b <- derefStablePtr bp
  newStablePtr =<< scApplyAll sc f [w, a, b]

bv_unop f scp ap = do
  sc <- derefStablePtr scp
  a <- derefStablePtr ap
  ty <- scTypeOf sc a
  newStablePtr =<< scApplyAll sc f [w, a]
-}

saw_bool_type   = with_context scBoolType
saw_nat_type    = with_context scNatType
saw_bv_type p w = with_context (\sc -> scBitvector sc (fromIntegral w)) p

saw_nat_const  p n = with_context (\sc -> scNat sc (fromIntegral n)) p
saw_bool_const p b = with_context (\sc -> scBool sc (b /= 0)) p

saw_pretty_print :: StablePtr (SharedTerm s) -> IO CString
saw_pretty_print = with_term_string (return . show)

-- To add:
--  * bitvector: +, -, *, /, >>, <<, fromNat, and, or, xor, negate, eq,
--               append, <, >
--  * boolean: and, or, xor, not
--  * nat: +, *, eq, <, >
--  * AIG: read_aig, write_aig
--  * SAWCore: read_sawcore_shared, write_sawcore_shared
--  * Proof: prove_abc

foreign export ccall saw_new_context :: IO (StablePtr (SharedContext s))
foreign export ccall saw_free :: StablePtr (SharedContext s) -> IO ()

foreign export ccall saw_bool_type :: StablePtr (SharedContext s)
                                   -> IO (StablePtr (SharedTerm s))

foreign export ccall saw_nat_type :: StablePtr (SharedContext s)
                                  -> IO (StablePtr (SharedTerm s))

foreign export ccall saw_bv_type :: StablePtr (SharedContext s)
                                 -> CInt
                                 -> IO (StablePtr (SharedTerm s))

foreign export ccall saw_bool_const :: StablePtr (SharedContext s)
                                    -> CInt
                                    -> IO (StablePtr (SharedTerm s))

foreign export ccall saw_nat_const :: StablePtr (SharedContext s)
                                   -> CInt
                                   -> IO (StablePtr (SharedTerm s))

foreign export ccall saw_pretty_print :: StablePtr (SharedTerm s)
                                      -> IO CString
