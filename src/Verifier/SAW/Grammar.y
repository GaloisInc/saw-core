{
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Grammar 
  ( Decl(..)
  , Expr(..)
  , parseSAW
  , runParser
  , lexer
  ) where

import Control.Applicative ((<$>))
import Control.Monad
import Control.Monad.State
import qualified Data.ByteString.Lazy.UTF8 as B
import Data.Word
import System.Directory (getCurrentDirectory)

import Verifier.SAW.UntypedAST
import Verifier.SAW.Lexer

import Debug.Trace

}

%name parseSAW
--%expect 0
%tokentype { PosPair Token }
%monad { Parser }
%lexer { lexer } { PosPair _ TEnd }
%error { parseError }
%expect 0

%token
  '#'     { PosPair _ (TKey "#") }
  '->'    { PosPair _ (TKey "->") }
  '='     { PosPair _ (TKey "=") }
  '\\'    { PosPair _ (TKey "\\") }
  ';'     { PosPair _ (TKey ";") }
  '::'    { PosPair _ (TKey "::") }
  ','     { PosPair _ (TKey ",") }
  '.'     { PosPair _ (TKey ".") }
  '?'     { PosPair _ (TKey "?") }
  '??'    { PosPair _ (TKey "??") }
  '???'   { PosPair _ (TKey "???") }
  '('     { PosPair _ (TKey "(") }
  ')'     { PosPair _ (TKey ")") }
  '['     { PosPair _ (TKey "[") }
  ']'     { PosPair _ (TKey "]") }
  '{'     { PosPair _ (TKey "{") }
  '}'     { PosPair _ (TKey "}") }
  'data'  { PosPair _ (TKey "data") }
  'sort'  { PosPair _ (TKey "sort") }
  'where' { PosPair _ (TKey "where") }
  var     { PosPair _ (TVar _) }
  con     { PosPair _ (TCon _) }
  nat     { PosPair _ (TNat _) }

%%

SAWDecls :: { [Decl] }
SAWDecls : list(SAWDecl) { $1 }

SAWDecl :: { Decl }
SAWDecl : 'data' Con '::' LExpr 'where' '{' list(CtorDecl) '}' { DataDecl $2 $4 $7 }
        | DeclLhs '::' LExpr ';' {% mkTypeDecl $1 $3 }
        | DeclLhs '='  Expr ';'  {% mkTermDef  $1 $3 }

DeclLhs :: { DeclLhs }
DeclLhs : Con list(LambdaArg) { ($1, $2) }
        | Var list(LambdaArg) { ($1, $2) }

CtorDecl :: { CtorDecl }
CtorDecl : Con '::' LExpr ';' { Ctor $1 $3 }

AtomExpr :: { Expr }
AtomExpr : nat                          { IntLit (pos $1) (tokNat (val $1)) }
         | Var                          { Var $1 }
         | Con                          { Con $1 }
         | 'sort' nat                   { Sort (pos $1) (mkSort (tokNat (val $2))) }
         |     '(' sepBy(Expr, ',') ')' {% parseVParen (pos $1) $2 }
         | '#' '(' sepBy(Expr, ',') ')' {% parseTParen (pos $1) $3 }
         | '{' list(RecValue) '}'       { RecordValue (pos $1) $2 } 
         | '#' '{' list(RecType) '}'    { RecordType  (pos $1) $3 }
         | '[' sepBy(Expr, ',') ']'     { ArrayValue (pos $1) $2 }
         | AtomExpr '.' Var             { RecordSelector $1 $3 }

-- Expression formed from applications of atomic expressions.
AppExpr :: { Expr }
AppExpr : AtomExpr                   { $1 }
        | AppExpr AtomExpr           { App $1 NormalParam $2 }
        | AppExpr ParamType AtomExpr { App $1 $2 $3 }

-- Expression with uses of pi and lambda, but no typing.
LExpr :: { Expr }
LExpr : AppExpr                          {  $1 }
      | PiArg '->' LExpr                 {% mkPi (pos $2) $1 $3 }
      | '\\' list1(LambdaArg) '->' LExpr {  Lambda (pos $1) $2 $4 }

Expr :: { Expr }
Expr : LExpr { $1 }
     | LExpr '::' LExpr { TypeConstraint $1 (pos $2) $3 }

PiArg :: { (ParamType, Expr) }
PiArg : ParamType AtomExpr { ($1, $2) } 
      | AppExpr            { (NormalParam, $1) }

LambdaArg :: { (ParamType, Expr) }
LambdaArg : AtomExpr           { (NormalParam, $1) }
          | ParamType AtomExpr { ($1, $2) }

ParamType :: { ParamType }
ParamType : '?'   { ImplicitParam }
          | '??'  { InstanceParam }
          | '???' { ProofParam    }

RecValue :: { (PosPair Ident, Expr) }
RecValue : Var '=' Expr ';' { ($1, $3) }

RecType :: { (PosPair Ident, Expr) }
RecType : Var '::' LExpr ';' { ($1, $3) } 

Var :: { PosPair Ident }
Var : var { fmap (mkIdent . tokVar) $1 }

Con :: { PosPair Ident }
Con : con { fmap (mkIdent . tokCon) $1 }

-- A possibly-empty list of p's separated by q.
sepBy(p,q) : {- empty -} { [] }
           | rsepBy1(p,q) { reverse $1 }

rsepBy1(p,q) : p { [$1] }
             | rsepBy1(p,q) q p { $3 : $1 }

-- A list of 0 or more p's, terminated by q's
list(p) : {- empty -} { [] }
        | rlist1(p) { reverse $1 }

-- A reversed list of at least 1 p's
rlist1(p) : p           { [$1]    }
          | rlist1(p) p { $2 : $1 }

-- A list of at least 1 p's
list1(p) : rlist1(p) { reverse $1 }

{
paramTypeToken :: ParamType -> String
paramTypeToken tp =
  case tp of
    NormalParam -> ""
    ImplicitParam -> "?"
    InstanceParam -> "??"
    ProofParam -> "???"

data ParseError
  = UnexpectedLex [Word8]
  | UnexpectedEndOfBlockComment
  | UnexpectedToken Token
  | ParseError String
  | UnexpectedEnd
  deriving (Show)

type ErrorList = [PosPair ParseError]

data ParserState = PS { psInput :: AlexInput
                      , psErrors :: [PosPair ParseError]
                      }

newtype Parser a = Parser { _unParser :: State ParserState a }
  deriving (Functor, Monad)

addError :: Pos -> ParseError -> Parser ()
addError p err = Parser $ modify $ \s -> s { psErrors = PosPair p err : psErrors s }

setInput :: AlexInput -> Parser ()
setInput inp = Parser $ modify $ \s -> s { psInput = inp }

parsePos :: Parser Pos
parsePos = Parser $ gets (pos . psInput)

lexer :: (PosPair Token -> Parser a) -> Parser a
lexer f = do
  let go prevErr next = do
        let addErrors =
              case prevErr of
                Nothing -> return ()
                Just (po,l) -> addError po (UnexpectedLex (reverse l))
        s <- Parser get
        let inp@(PosPair p (Buffer _ b)) = psInput s
            end = addErrors >> next (PosPair p TEnd)
        case alexScan inp 0 of
          AlexEOF -> end
          AlexError _ ->
            case alexGetByte inp of
              Just (w,inp') -> do
                setInput inp'
                case prevErr of
                  Nothing -> go (Just (p,[w])) next
                  Just (po,l) -> go (Just (po,w:l)) next
              Nothing -> end
          AlexSkip inp' _ -> addErrors >> setInput inp' >> go Nothing next
          AlexToken inp' l act -> do
            addErrors
            setInput inp'
            let v = act (B.toString (B.take (fromIntegral l) b))
            next (PosPair p v)
  let read i tkn =
        case val tkn of
          TCmntS -> go Nothing (read (i+1))
          TCmntE | i > 0 -> go Nothing (read (i-1))
                 | otherwise -> do
                     addError (pos tkn) (UnexpectedLex (fmap (fromIntegral . fromEnum) "-}"))
                     go Nothing (read 0)
          _ | i > 0 -> go Nothing (read i)
            | otherwise -> f tkn 
  go Nothing (read (0::Integer))

runParser :: FilePath -> B.ByteString -> Parser a -> (a,ErrorList)
runParser path b (Parser m) = (r, reverse (psErrors s))
  where initState = PS { psInput = initialAlexInput path b, psErrors = [] }
        (r,s) = runState m initState

parseError :: PosPair Token -> Parser a
parseError pt = do
  addError (pos pt) (UnexpectedToken (val pt))
  fail $ (ppPos "" (pos pt)) ++ " Parse error\n  " ++ (ppToken (val pt))

addParseError :: Pos -> String -> Parser ()
addParseError p s = addError p (ParseError s)

unexpectedIntLiteral :: Pos -> Integer -> String -> Parser ()
unexpectedIntLiteral p _ ctxt = do
  addParseError p $ "Unexpected integer literal when parsing " ++ ctxt ++ "."

unexpectedParameterAnnotation :: Pos -> ParamType -> Parser ()
unexpectedParameterAnnotation p _ = 
  addParseError p "Multiple parameter annotations are not supported."

unexpectedTypeConstraint :: Pos -> Parser ()
unexpectedTypeConstraint p = addParseError p "Unexpected type constraint."

unexpectedPi :: Pos -> Parser ()
unexpectedPi p = addParseError p "Unexpected pi expression"

unexpectedLambda :: Pos -> Parser ()
unexpectedLambda p = addParseError p "Unexpected lambda expression"

unexpectedOpenParen :: Pos -> Parser ()
unexpectedOpenParen p = addParseError p "Unexpected parenthesis"

mergeParamType :: ParamType -> Pos -> ParamType -> Parser ParamType
mergeParamType NormalParam _ tp = return tp
mergeParamType pt p mpt = do
  unexpectedParameterAnnotation p mpt >> return pt

-- Attempts to parses an expression as a list of identifiers.
-- Will return a value on all expressions, but may add errors to parser state.
exprAsVarList :: Expr -> String -> Parser [PosPair Ident]
exprAsVarList ex errMsg =
  case ex of
    Var pi -> return [pi]
    App x _ y -> liftM2 (++) (exprAsVarList x errMsg) (exprAsVarList y errMsg)
    BadExpression _ -> return []
    _ -> addParseError (pos ex) errMsg >> return []

mkPi :: Pos -> (ParamType, Expr) -> Expr -> Parser Expr
mkPi ptp (ppt,l) r = parseLhs l
  where parseLhs (Paren _ (TypeConstraint x _ t)) = 
          fmap (\l -> Pi ppt l t ptp r) $ 
               exprAsVarList x "Invalid arguments to Pi expression."
        parseLhs e =
          return $ Pi ppt [PosPair (pos e) (mkIdent "_")] e ptp r   

parseVParen :: Pos -> [Expr] -> Parser Expr
parseVParen p [expr] = return $ Paren p expr
parseVParen p l = return $ TupleValue p l

parseTParen :: Pos -> [Expr] -> Parser Expr
parseTParen p [expr] = do
  addParseError p "Tuple may not contain a single value."
  return (badExpr p)
parseTParen p l = return $ TupleType p l

asAppList :: Expr -> (Expr,[Expr])
asAppList = \x -> impl x []
  where impl (App x _ y) r = impl x (y:r)
        impl x r = (x,r)

type DeclLhs = (PosPair Ident, [LambdaBinding Expr])

mkTypeDecl :: DeclLhs -> Expr -> Parser Decl
mkTypeDecl (op,args) rhs = fmap (\l -> TypeDecl (op:l) rhs) $ filterArgs args []
  where filterArgs ((NormalParam,Var pi):l) r = filterArgs l (pi:r)
        filterArgs ((NormalParam,e):l) r = do
          addParseError (pos e) "Expected variable identifier in type declaration."
          filterArgs l r
        filterArgs ((pt,e):l) r = do
          addParseError (pos e) $ "Unexpected token " ++ paramTypeToken pt ++ "."
          filterArgs l r
        filterArgs [] r = return (reverse r)

mkTermDef :: DeclLhs -> Expr -> Parser Decl
mkTermDef (op,args) rhs = return (TermDef op args rhs)
}