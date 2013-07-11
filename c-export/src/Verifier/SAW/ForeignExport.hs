module Verifier.SAW.ForeignExport where

import Control.Monad
import Foreign.C.String
import Foreign.StablePtr

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

expModule :: Module
expModule = emptyModule (mkModuleName ["SAW", "Export"])

saw_new_context :: IO (StablePtr (SharedContext s))
saw_new_context = mkSharedContext expModule >>= newStablePtr

saw_free :: StablePtr (SharedContext s) -> IO ()
saw_free = freeStablePtr

saw_bool_type :: StablePtr (SharedContext s) -> IO (StablePtr (SharedTerm s))
saw_bool_type = deRefStablePtr >=> scBoolType >=> newStablePtr

saw_pretty_print :: StablePtr (SharedTerm s) -> IO CString
saw_pretty_print = deRefStablePtr >=> (return . show) >=> newCString

foreign export ccall saw_new_context :: IO (StablePtr (SharedContext s))
foreign export ccall saw_free :: StablePtr (SharedContext s) -> IO ()

foreign export ccall saw_bool_type :: StablePtr (SharedContext s)
                                   -> IO (StablePtr (SharedTerm s))

foreign export ccall saw_pretty_print :: StablePtr (SharedTerm s)
                                      -> IO CString
