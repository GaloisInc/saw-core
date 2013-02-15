{-# LANGUAGE ImplicitParams #-}

module Verifier.SAW.SBVParser where

import Control.Monad (liftM, foldM)
import Data.Map (Map)
import qualified Data.Map as Map

import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm
import qualified Verinf.SBV.Model as SBV

parseSBV :: (?sc :: SharedContext s) => Map SBV.NodeId (SharedTerm s) -> SBV.SBV -> IO (SBV.Size, SharedTerm s)
parseSBV nodes (SBV.SBV size (Left num)) =
    do t <- scInteger num -- FIXME: what about the size?
       return (size, t)
parseSBV nodes (SBV.SBV size (Right nodeid)) =
    case Map.lookup nodeid nodes of
      Just t -> return (size, t)
      Nothing -> fail "parseSBV"

scBitVector :: SBV.Size -> IO (SharedTerm s)
scBitVector size = undefined

parseOperator :: (?sc :: SharedContext s) => SBV.Operator -> [SBV.Size] -> SBV.Size -> IO (SharedTerm s)
parseOperator operator argSizes resultSize =
    do resultType <- scBitVector resultSize
       argTypes <- mapM scBitVector argSizes
       operType <- foldM (flip scFun) resultType (reverse argTypes)
       -- TODO: implement function scFunAll for this
       undefined

type NodeCache s = Map SBV.NodeId (SharedTerm s)

parseSBVExpr :: (?sc :: SharedContext s) => NodeCache s -> SBV.Size -> SBV.SBVExpr -> IO (SharedTerm s)
parseSBVExpr nodes size (SBV.SBVAtom sbv) =
    liftM snd $ parseSBV nodes sbv
parseSBVExpr nodes size (SBV.SBVApp operator sbvs) =
    do (sizes, args) <- liftM unzip $ mapM (parseSBV nodes) sbvs
       op <- parseOperator operator sizes size
       scApplyAll op args

parseSBVCommand :: (?sc :: SharedContext s) => NodeCache s -> SBV.SBVCommand -> IO (SharedTerm s, NodeCache s)
parseSBVCommand nodes (SBV.Decl _ (SBV.SBV size (Right nodeid)) (Just expr)) =
    do term <- parseSBVExpr nodes size expr
       let nodes' = Map.insert nodeid term nodes
       return (term, nodes')
parseSBVCommand _ _ = error "parseSBVCommand: not an assignment"

-- TODO: Code for handling input and output nodes

-- TODO: Code for projecting inputs and combining outputs according to IRType
