{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
module Verifier.SAW.Export.SMT.Common
  ( needBits
  , cache
  , freshName
  , matchTerm
    -- Renderable and it's use cases.
  , Renderable(..)
  , matchArgs
  , matchDef
  , matchCtor
  , matchDataType
    -- * Additional primitive types.
  , BoolType(..)
  , BitvectorType(..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Bits
import qualified Data.Map as Map
import Data.String

import Verifier.SAW.Prim
import Verifier.SAW.Conversion
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.TermNet as Net

-- | How many bits do we need to represent the given number.
needBits :: Nat -> Integer
needBits n0 | n0 <= 0    = 0
            | otherwise = go n0 0
  where go :: Nat -> Integer -> Integer
        go 0 i = i
        go n i = (go $! (shiftR n 1)) $! (i+1)

cache :: (MonadState s m, Ord k)
      => Simple Lens s (Map.Map k v)
      -> k
      -> m v
      -> m v
cache l k a = do
  m0 <- use l
  case Map.lookup k m0 of
    Just r -> return r
    Nothing -> do
      r <- a
      l %= Map.insert k r
      return r

freshName :: (MonadState s m, Num n, Show n, IsString nm)
          => Simple Lens s n
          -> String
          -> m nm
freshName l base = do
  c <- use l
  l .= c + 1
  return $ fromString $ base ++ show c

-- | Match a term against a net in a state monad and run action if found or not found.
matchTerm :: (MonadState s m, Net.Pattern t)
          => (s -> Net.Net (Matcher (MaybeT m) t v)) -- ^ Function for getting net.
          -> t -- ^ Term to match
          -> m (Maybe v)
matchTerm getter t = do
  let go [] = return Nothing
      go (rl:rls) = do
        mr <- runMaybeT (runMatcher rl t)
        maybe (go rls) (return . Just) mr
  net <- gets getter
  go (Net.match_term net t)

class Renderable a m t b where
  mapMatcher :: Matcher m t a -> Matcher m t b

  -- | Returns the patterns used to match the arguments to this renderable.
  -- Parameters used for typechecking, and may not be evaluated.
  argPats :: a -> Matcher m t b -> [Net.Pat]

  -- | Returns a function for matching all the arguments.
  argFn :: a -> [t] -> m (b,[t])


instance Monad m => Renderable a m t a where
  mapMatcher = id
  argPats _ _ = []
  argFn a l = return (a,l)

instance Monad m => Renderable (m a) m t a where
  mapMatcher m = thenMatcher m id
  argPats _ _ = []
  argFn ma l = do a <- ma; return (a,l)

instance (Applicative m, Monad m, Termlike t, Matchable m t a, Renderable b m t c)
      => Renderable (a -> b) m t c where
  mapMatcher m = mapMatcher $ thenMatcher (m <:> defaultMatcher) (\(f :*: x) -> return (f x))
  
  argPats = go defaultMatcher
    where go :: forall a m t b c . (Renderable b m t c, Matchable m t a)
             => Matcher m t a -- ^ Default matcher for m t a
             -> (a -> b) -- Dummy argument for typechecking
             -> Matcher m t c -- Dummy argument for typechecking
             -> [Net.Pat]
          go m f r = matcherPat m : argPats (f undefined) r

  argFn _ [] = fail "empty arguments"
  argFn fn (h:r) = do
    x <- runMatcher defaultMatcher h
    argFn (fn x) r

matchArgs :: (Monad m, Termlike t, Renderable a m t b) => Matcher m t x -> a -> Matcher m t b
matchArgs m f = mapMatcher (thenMatcher m (\_ -> return f))

matchDef :: (Monad m, Termlike t, Renderable v m t a)
          => Ident -> v -> Matcher m t a
matchDef d v = asGlobalDef d `matchArgs` v

matchCtor :: (Monad m, Termlike t, Renderable v m t a)
          => Ident -> v -> Matcher m t a
matchCtor c v = res
  where res = asCtor c (ArgsMatcher (argPats v res) (argFn v)) 

matchDataType :: (Monad m, Termlike t, Renderable v m t a)
              => Ident -> v -> Matcher m t a
matchDataType c v = res
  where res = asDataType c (ArgsMatcher (argPats v res) (argFn v))

------------------------------------------------------------------------
-- Additional primitive types.

data BoolType = BoolType

instance (Functor m, Monad m, Termlike t) => Matchable m t BoolType where
  defaultMatcher = BoolType <$ asBoolType

-- | A bitvector with a constant width.
data BitvectorType = BitvectorType Nat

instance (Applicative m, Monad m, Termlike t) => Matchable m t BitvectorType where
  defaultMatcher = asGlobalDef "Prelude.bitvector" `matchArgs` BitvectorType