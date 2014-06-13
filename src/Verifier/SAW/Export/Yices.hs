module Verifier.SAW.Export.Yices ( yices, BV(..), YVal(..), YResult(..), ppVal
  , getIdent
  ) where

import Text.ParserCombinators.Parsec as P
import Text.PrettyPrint as PP hiding (parens)
import Data.Char
import Control.Monad(mplus,msum)
import Control.Applicative((<*))
import Numeric
import Data.List
import Data.Function
import System.Directory (findExecutable)
import System.Process
import qualified Data.Map as M
import SMTLib1

data BV   = BV { val :: !Integer, width :: !Int } deriving Show

data YVal = YFun [([BV],BV)] BV
          | YVal BV
          | YVar String
           deriving Show

data YResult  = YUnknown
              | YUnsat
              | YSat (M.Map String YVal)

yices :: Maybe Int -> Script -> IO YResult
yices mbTime script =
  do mbYicesExe <- findExecutable "yices"
     case mbYicesExe of
       Nothing -> fail $ "Unable to find yices executable; please ensure that it is in your path."
       Just yicesExe -> do
         txt <- readProcess yicesExe (["--full-model"] ++ timeOpts)
                    (show (pp script))
         case parseOutput txt of
           Right a -> return a
           Left e -> fail $ unlines [ "yices: Failed to parse the output from Yices"
                                    , show e
                                    ]
      where timeOpts = case mbTime of
                         Nothing -> []
                         Just t  -> ["--timeout=" ++ show t]


getIdent :: M.Map String YVal -> Ident -> YVal
getIdent model i = getVar (show (pp i))
  where
  getVar x = case M.lookup x model of
               Just (YVar y) -> getVar y
               Just v        -> v
               Nothing       -> YVar x    -- Should not happen!




--------------------------------------------------------------------------------

tok     :: Parser a -> Parser a
tok p    = p <* P.spaces

str     :: String -> Parser ()
str x    = tok (string x >> return ())

parens  :: Parser a -> Parser a
parens p = between (tok (P.char '(')) (tok (P.char ')')) p

pName   :: Parser String
pName    = tok $
  do x <- satisfy isAlpha
     xs <- many (satisfy isAlphaNum)
     return (x:xs)

pBV :: Parser BV
pBV = tok $
  do str "0b"
     ds <- many (P.char '0' `mplus` P.char '1')
     let twos = 1 : map (2*) twos
         dig '0' = 0
         dig _   = 1
     return BV { val   = sum (zipWith (*) twos (reverse (map dig ds)))
               , width = length ds
               }

pVal :: Parser (String, YVal)
pVal = parens $ do str "="
                   x <- pName
                   v <- (YVar `fmap` pName) `mplus` (YVal `fmap` pBV)
                   return (x, v)

pFun :: Parser (String, YVal)
pFun = do n <- try $ do str "---"
                        n <- pName
                        str "---"
                        return n
          vs <- many $ parens $
                do str "="
                   ks <- parens (pName >> many1 pBV)
                   v <- pBV
                   return (ks,v)
          str "default:"
          v <- pBV
          return (n, YFun (sortBy (compare `on` (map val . fst)) vs) v)

pOut :: Parser YResult
pOut =
  do r <- msum [ do try (str "sat")
                    str "MODEL"
                    xs <- many (pVal `mplus` pFun)
                    str "----"
                    return $ YSat $ M.fromList xs
               , try (str "unsat") >> return YUnsat
               , try (str "unknown") >> return YUnknown
               ]
     P.spaces
     return r

parseOutput :: String -> Either P.ParseError YResult
parseOutput = parse pOut "Yices output"


--------------------------------------------------------------------------------


ppVal :: (String, YVal) -> Doc
ppVal (x,vv) =
  case vv of
    YVar v -> text x <+> text "=" <+> text v
    YVal n -> text x <+> text "=" <+> ppV n
    YFun vs v -> vcat (map ppEnt vs) $$
                 text x <> brackets (text "_") <+> text "=" <+> ppV v
      where ppEnt (as,b) = text x <>
                  brackets (fsep $ punctuate comma $ map (integer . val) as)
                      <+> text "=" <+> ppV b

  where hex v = text "0x" <> text (showHex v "")
        ppV n = hex (val n) <+> text ":" <+> brackets (int (width n))


