{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
module Verifier.SAW.Export.SMT.Common
  ( cache
  , freshName
  , matchTerm
  , Renderable
  , matchArgs
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.State
import Control.Monad.Trans.Maybe
import qualified Data.Map as Map
import Data.String

import Verifier.SAW.Conversion
import qualified Verifier.SAW.TermNet as Net

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

class Renderable m t a b where
  mapMatcher :: Matcher m t a -> Matcher m t b

instance Renderable m t r r where
  mapMatcher = id

instance (Applicative m, Monad m, Termlike t, Matchable m t a, Renderable m t b c)
      => Renderable m t (a -> b) c where
  mapMatcher m = mapMatcher $ thenMatcher (m <:> defaultMatcher) (\(f :*: x) -> return (f x))

matchArgs :: (Monad m, Termlike t, Renderable m t a b) => Matcher m t x -> a -> Matcher m t b
matchArgs m f = mapMatcher (thenMatcher m (\_ -> return f))