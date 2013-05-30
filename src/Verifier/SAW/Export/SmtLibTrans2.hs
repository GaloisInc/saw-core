{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
module Verifier.SAW.Export.SmtLibTrans2(translate, SMT1.TransParams(..), MetaData(..)) where

import Verifier.SAW.Export.SmtLibTrans as SMT1 hiding (MetaData(..),translate)
import qualified Verifier.SAW.Export.SmtLibTrans as SMT1
import qualified SMTLib1 as SMT1
import SMTLib2
import SMTLib2.BitVector
import SMTLib2.Array
import SMTLib2.Compat1
import Control.Applicative
import qualified Data.Map as M
import qualified Data.Vector as V
import Data.Traversable(traverse)
import Text.PrettyPrint

data MetaData = MetaData
  { trAsmp     :: Expr
  , trGoals    :: [Expr]
  , trInputs   :: [Ident]
  , trUninterp :: [(Ident, String)]
  , trDefined  :: M.Map String [ (V.Vector Expr, Expr) ]
  , trArrays   :: M.Map Ident [Ident]
  }

translate :: SMT1.TransParams s -> IO (Script, MetaData)
translate ps =
  do (s1,m1) <- SMT1.translate ps
     case toEither (script s1) of
        Left e -> fail $ unlines [ "Internal error:"
                                 , "Failed to upgrade script to version 2"
                                 , show (nest 2 e)
                                 ]
        Right s ->
          case toEither (metaData m1) of
            Left e ->
              fail $ unlines [ "Internal error:"
                             , "Failed to upgrade metadata to version 2"
                             , show (nest 2 e)
                             ]
            Right m -> return (fixupScript s,m)


metaData :: SMT1.MetaData -> Trans MetaData
metaData m =
  MetaData <$> formula' (SMT1.trAsmp m)
           <*> traverse formula' (SMT1.trGoals m)
           <*> pure (map ident (SMT1.trInputs m))
           <*> pure [ (ident i, s) | (i,s) <- SMT1.trUninterp m ]
           <*> traverse (traverse defEntry) (SMT1.trDefined m)
           <*> pure (M.fromList $ map arrEntry $ M.toList $ SMT1.trArrays m)
  where
  defEntry (xs, x) = (,) <$> (V.fromList <$> traverse term' (V.toList xs))
                         <*> term' x
  arrEntry (x,xs)  = (ident x, map ident xs)

formula' :: SMT1.Formula -> Trans Expr
formula' = fmap fixupExpr . formula

term' :: SMT1.Term -> Trans Expr
term' = fmap fixupExpr . term

-- Additional adjustments to reflect differences between the theories.
fixupType :: Type -> Type
fixupType (TApp (I (N "Array") [x,y]) []) = tArray (tBitVec x) (tBitVec y)
fixupType t = t


-- Additional adjustments to reflect differences between the theories.
fixupExpr :: Expr -> Expr
fixupExpr expr =
  case expr of
    App i mb es
      | Just (a,m) <- bitLit i -> bv a m
      | i == "bit0"            -> bv 0 1
      | i == "bit1"            -> bv 1 1
      | otherwise              -> App i (fmap fixupType mb) (map fixupExpr es)

    Lit _        -> expr
    Quant a bs e -> Quant a (map fixBind bs) (fixupExpr e)
    Let ds e     -> Let (map fixD ds) (fixupExpr e)
      where fixD d = Defn { defVar = defVar d, defExpr = fixupExpr (defExpr d) }
    Annot e as   -> Annot (fixupExpr e) as    -- we don't fixup attrs...

fixBind :: Binder -> Binder
fixBind x = Bind { bindVar = bindVar x, bindType = fixupType (bindType x) }


bitLit :: Ident -> Maybe (Integer, Integer)
bitLit (I (N ('b' : 'v' : cs)) [m])
  | [(a,"")] <- reads cs    = return (a,m)
bitLit _ = Nothing



fixupCommand :: Command -> Command
fixupCommand cmd =
  case cmd of
    CmdDefineType x xs t  -> CmdDefineType x xs (fixupType t)
    CmdDeclareFun x ts t  -> CmdDeclareFun x (map fixupType ts) (fixupType t)
    CmdDefineFun n bs t e -> CmdDefineFun n (map fixBind bs) (fixupType t)
                                                             (fixupExpr e)
    CmdAssert e           -> CmdAssert (fixupExpr e)
    CmdGetValue es        -> CmdGetValue (map fixupExpr es)
    _                     -> cmd

fixupScript :: Script -> Script
fixupScript (Script cs) = Script (map fixupCommand cs ++ [CmdCheckSat,CmdExit])



