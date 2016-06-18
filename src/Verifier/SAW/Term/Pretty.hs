{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Verifier.SAW.Term.Pretty
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Term.Pretty
 ( Prec(..)
 , LocalVarDoc
 , emptyLocalVarDoc
 , TermDoc(..)
 , ppTermDoc
 , docShowLocalNames
 , docShowLocalTypes
 , TermPrinter
 , PPOpts(..)
 , defaultPPOpts
 , ppAppParens
 , ppIdent
 , ppDefEqn
 , ppTermF
 , ppTermF'
 , ppFlatTermF
 , ppFlatTermF'
 , ppRecordF
 , ppCtor
 , ppDataType
 , ppPat
 , ppTypeConstraint
 , commaSepList
 , semiTermList
 , ppParens
 , ppTermlike
 , ppTermDepth
 ) where

import Control.Applicative hiding (empty)
import Control.Lens
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Foldable (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import Numeric (showIntAtBase)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as PPL

import Prelude hiding (all, foldr, sum)

import Verifier.SAW.Term.Functor

data Prec
  = PrecNone   -- ^ Nonterminal 'Term'
  | PrecLambda -- ^ Nonterminal 'LTerm'
  | PrecApp    -- ^ Nonterminal 'AppTerm'
  | PrecArg    -- ^ Nonterminal 'AppArg'
  deriving (Eq, Ord)

data LocalVarDoc =
  LVD
  { docModuleName :: Map ModuleName String
  , _docShowLocalNames :: Bool
  , _docShowLocalTypes :: Bool
  , docMap :: !(Map DeBruijnIndex Doc)
  , docLvl :: !DeBruijnIndex
  , docUsedMap :: Map String DeBruijnIndex
  }

emptyLocalVarDoc :: LocalVarDoc
emptyLocalVarDoc =
  LVD { docModuleName = Map.empty
      , _docShowLocalNames = True
      , _docShowLocalTypes = False
      , docMap = Map.empty
      , docLvl = 0
      , docUsedMap = Map.empty
      }

-- | Flag indicates doc should use local names (default True)
docShowLocalNames :: Simple Lens LocalVarDoc Bool
docShowLocalNames = lens _docShowLocalNames (\s v -> s { _docShowLocalNames = v })

-- | Flag indicates doc should print type for locals (default false)
docShowLocalTypes :: Simple Lens LocalVarDoc Bool
docShowLocalTypes = lens _docShowLocalTypes (\s v -> s { _docShowLocalTypes = v })

freshVariant :: Map String a -> String -> String
freshVariant used name
  | Map.member name used = freshVariant used (name ++ "'")
  | otherwise = name

consBinding :: LocalVarDoc -> String -> LocalVarDoc
consBinding lvd i = lvd { docMap = Map.insert lvl (text i) m
                        , docLvl = lvl + 1
                        , docUsedMap = Map.insert i lvl (docUsedMap lvd)
                        }
 where lvl = docLvl lvd
       m = case Map.lookup i (docUsedMap lvd) of
             Just pl -> Map.delete pl (docMap lvd)
             Nothing -> docMap lvd

lookupDoc :: LocalVarDoc -> DeBruijnIndex -> Doc
lookupDoc lvd i
    | lvd^.docShowLocalNames =
        case Map.lookup lvl (docMap lvd) of
          Just d -> d
          Nothing -> text ('!' : show (i - docLvl lvd))
    | otherwise = text ('!' : show i)
  where lvl = docLvl lvd - i - 1

type TermPrinter e = LocalVarDoc -> Prec -> e -> Doc

(<<$>>) :: Doc -> Doc -> Doc
x <<$>> y = (PPL.<$>) x y

doublecolon :: Doc
doublecolon = colon <> colon

bracesList :: [Doc] -> Doc
bracesList = encloseSep lbrace rbrace comma

-- | Print a list of items separated by semicolons
semiTermList :: [Doc] -> Doc
semiTermList = hsep . fmap (<> semi)

commaSepList :: [Doc] -> Doc
commaSepList [] = empty
commaSepList [d] = d
commaSepList (d:l) = d <> comma <+> commaSepList l

-- | Add parenthesis around a document if condition is true.
ppParens :: Bool -> Doc -> Doc
ppParens b = if b then parens . align else id

data PPOpts = PPOpts { ppBase :: Int }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { ppBase = 10 }

ppNat :: PPOpts -> Integer -> Doc
ppNat opts i
  | base > 36 = integer i
  | otherwise = prefix <> text value
  where
    base = ppBase opts

    prefix = case base of
      2  -> text "0b"
      8  -> text "0o"
      10 -> empty
      16 -> text "0x"
      _  -> text "0"  <> char '<' <> int base <> char '>'

    value  = showIntAtBase (toInteger base) (digits !!) i ""
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"

ppIdent :: Ident -> Doc
ppIdent i = text (show i)

ppCtor :: TermPrinter e -> Ctor Ident e -> Doc
ppCtor f c = hang 2 $ group (ppIdent (ctorName c) <<$>> doublecolon <+> tp)
  where
    lcls = emptyLocalVarDoc
    tp = f lcls PrecLambda (ctorType c)

ppTypeConstraint :: TermPrinter e -> LocalVarDoc -> Doc -> e -> Doc
ppTypeConstraint f lcls sym tp = hang 2 $ group (sym <<$>> doublecolon <+> f lcls PrecLambda tp)

ppLocalDef :: Applicative f
           => (LocalVarDoc -> Prec -> e -> f Doc)
           -> LocalVarDoc -- ^ Context outside let
           -> LocalVarDoc -- ^ Context inside let
           -> LocalDef e
           -> f Doc
ppLocalDef pp lcls lcls' (Def nm _qual tp eqs) =
    ppd <$> (pptc <$> pp lcls PrecLambda tp)
        <*> traverse (ppDefEqnF pp lcls' sym) (reverse eqs)
  where sym = text nm
        pptc tpd = hang 2 $ group (sym <<$>> doublecolon <+> tpd <> semi)
        ppd tpd eqds = vcat (tpd : eqds)

ppDefEqn :: TermPrinter e -> LocalVarDoc -> Doc -> DefEqn e -> Doc
ppDefEqn pp lcls sym eq = runIdentity (ppDefEqnF pp' lcls sym eq)
  where pp' l' p' e' = pure (pp l' p' e')

ppDefEqnF :: Applicative f
          => (LocalVarDoc -> Prec -> e -> f Doc)
          -> LocalVarDoc -> Doc -> DefEqn e -> f Doc
ppDefEqnF f lcls sym (DefEqn pats rhs) =
    ppEq <$> traverse ppPat' pats
-- Is this OK?
         <*> f lcls' PrecNone rhs
--         <*> f lcls' PrecLambda rhs
  where ppEq pd rhs' = group $ nest 2 (sym <+> (hsep (pd++[equals])) <<$>> rhs' <> semi)
        lcls' = foldl' consBinding lcls (concatMap patBoundVars pats)
        ppPat' = fmap ppTermDoc . ppPat (\p e -> TermDoc <$> f lcls' p e) PrecArg

ppDataType :: TermPrinter e -> DataType Ident e -> Doc
ppDataType f dt =
  group $ (group ((text "data" <+> tc) <<$>> (text "where" <+> lbrace)))
          <<$>>
          vcat ((indent 2 . ppc) <$> dtCtors dt)
          <$$>
          rbrace

  where lcls = emptyLocalVarDoc
        sym = ppIdent (dtName dt)
        tc = ppTypeConstraint f lcls sym (dtType dt)
        ppc c = ppCtor f c <> semi

-- | Type TermDoc facilitates the pretty-printing of nested tuple and
-- record structures using non-nested syntax.
data TermDoc
  = TermDoc Doc
  | TupleDoc [Doc]
  | TupleTDoc [Doc]
  | RecordDoc [(FieldName, Doc)]
  | RecordTDoc [(FieldName, Doc)]
  | LabelDoc FieldName

ppTermDoc :: TermDoc -> Doc
ppTermDoc td =
  case td of
    TermDoc doc       -> doc
    TupleDoc docs     -> tupled docs
    TupleTDoc docs    -> char '#' <> tupled docs
    RecordDoc fields  -> bracesList (map (ppField "=") fields)
    RecordTDoc fields -> char '#' <> bracesList (map (ppField ":") fields)
    LabelDoc s        -> text (show s)
  where
    ppField s (name, rhs) = group (nest 2 (text name <+> text s <<$>> rhs))

ppPairValue :: TermDoc -> TermDoc -> TermDoc
ppPairValue x (TupleDoc docs) = TupleDoc (ppTermDoc x : docs)
ppPairValue x y = TermDoc $ parens (ppTermDoc x <+> char '|' <+> ppTermDoc y)

ppPairType :: TermDoc -> TermDoc -> TermDoc
ppPairType x (TupleTDoc docs) = TupleTDoc (ppTermDoc x : docs)
ppPairType x y = TermDoc $ char '#' <> parens (ppTermDoc x <+> char '|' <+> ppTermDoc y)

ppFieldValue :: TermDoc -> TermDoc -> TermDoc -> TermDoc
ppFieldValue (LabelDoc f) x (RecordDoc fields) = RecordDoc ((f, ppTermDoc x) : fields)
ppFieldValue f x y = TermDoc $ braces (eqn (ppTermDoc f) x <+> char '|' <+> ppTermDoc y)
  where eqn l r = group (nest 2 (l <+> equals <<$>> ppTermDoc r))

ppFieldType :: TermDoc -> TermDoc -> TermDoc -> TermDoc
ppFieldType (LabelDoc f) x (RecordTDoc fields) = RecordTDoc ((f, ppTermDoc x) : fields)
ppFieldType f x y = TermDoc $ char '#' <> braces (eqn (ppTermDoc f) x <+> char '|' <+> ppTermDoc y)
  where eqn l r = group (nest 2 (l <+> equals <<$>> ppTermDoc r))

ppRecordSelector :: TermDoc -> TermDoc -> TermDoc
ppRecordSelector x (LabelDoc f) = TermDoc (ppTermDoc x <> char '.' <> text f)
ppRecordSelector x f = TermDoc (ppTermDoc x <> char '.' <> ppParens True (ppTermDoc f))

ppAppParens :: Prec -> Doc -> Doc
ppAppParens p d = ppParens (p > PrecApp) d

ppAppList :: Prec -> Doc -> [Doc] -> Doc
ppAppList _ sym [] = sym
ppAppList p sym l = ppAppParens p $ hsep (sym : l)

ppPat :: Applicative f
      => (Prec -> e -> f TermDoc)
      -> Prec -> Pat e -> f TermDoc
ppPat f p pat =
  case pat of
    PVar i _ _ -> pure $ TermDoc $ text i
    PUnused{}  -> pure $ TermDoc $ char '_'
    PCtor c pl -> TermDoc . ppAppList p (ppIdent c) . map ppTermDoc <$>
                  traverse (ppPat f PrecArg) pl
    PUnit      -> pure $ TermDoc $ text "()"
    PPair x y  -> ppPairValue <$> ppPat f PrecNone x <*> ppPat f PrecNone y
    PEmpty     -> pure $ TermDoc $ text "{}"
    PField n x y -> ppFieldValue <$> ppPat f PrecNone n
                    <*> ppPat f PrecNone x <*> ppPat f PrecNone y
    PString s  -> pure $ LabelDoc s

ppRecordF :: Applicative f => (t -> f Doc) -> Map String t -> f Doc
ppRecordF pp m = braces . semiTermList <$> traverse ppFld (Map.toList m)
  where ppFld (fld,v) = eqCat (text fld) <$> pp v
        eqCat x y = group $ nest 2 (x <+> equals <<$>> y)

ppFlatTermF' :: Applicative f => PPOpts -> (Prec -> t -> f TermDoc) -> Prec -> FlatTermF t -> f TermDoc
ppFlatTermF' opts pp prec tf =
  case tf of
    GlobalDef i   -> pure $ TermDoc $ ppIdent i
    UnitValue     -> pure $ TupleDoc []
    UnitType      -> pure $ TupleTDoc []
    PairValue x y -> ppPairValue <$> pp PrecNone x <*> pp PrecNone y
    PairType x y  -> ppPairType <$> pp PrecNone x <*> pp PrecNone y
    PairLeft t    -> TermDoc . ppParens (prec > PrecArg) . (<> (text ".L")) <$> pp' PrecArg t
    PairRight t   -> TermDoc . ppParens (prec > PrecArg) . (<> (text ".R")) <$> pp' PrecArg t
    EmptyValue         -> pure $ RecordDoc []
    EmptyType          -> pure $ RecordTDoc []
    FieldValue f x y   -> ppFieldValue <$> pp PrecNone f <*> pp PrecNone x <*> pp PrecNone y
    FieldType f x y    -> ppFieldType <$> pp PrecNone f <*> pp PrecNone x <*> pp PrecNone y
    RecordSelector t f -> ppRecordSelector <$> pp PrecArg t <*> pp PrecArg f

    CtorApp c l      -> TermDoc . ppAppList prec (ppIdent c) <$> traverse (pp' PrecArg) l
    DataTypeApp dt l -> TermDoc . ppAppList prec (ppIdent dt) <$> traverse (pp' PrecArg) l

    Sort s -> pure $ TermDoc $ text (show s)
    NatLit i -> pure $ TermDoc $ ppNat opts i
    ArrayValue _ vl -> TermDoc . list <$> traverse (pp' PrecNone) (V.toList vl)
    FloatLit v  -> pure $ TermDoc $ text (show v)
    DoubleLit v -> pure $ TermDoc $ text (show v)
    StringLit s -> pure $ LabelDoc s
    ExtCns (EC _ v _) -> pure $ TermDoc $ text v
  where
    pp' p t = ppTermDoc <$> pp p t

-- | This version has the type expected by various modules in
-- Verifier/SAW/Typechecker, but it does not properly display nested
-- tuples or records.
ppFlatTermF :: Applicative f => PPOpts -> (Prec -> t -> f Doc) -> Prec -> FlatTermF t -> f Doc
ppFlatTermF opts pp prec tf = fmap ppTermDoc (ppFlatTermF' opts pp' prec tf)
  where pp' p t = fmap TermDoc (pp p t)

ppTermF :: PPOpts -> (LocalVarDoc -> Prec -> t -> TermDoc)
        -> LocalVarDoc -> Prec -> TermF t -> TermDoc
ppTermF opts pp lcls p tf = runIdentity (ppTermF' opts pp' lcls p tf)
  where pp' l' p' t' = pure (pp l' p' t')

ppTermF' :: Applicative f
         => PPOpts
         -> (LocalVarDoc -> Prec -> e -> f TermDoc)
         -> LocalVarDoc
         -> Prec
         -> TermF e
         -> f TermDoc
ppTermF' opts pp lcls prec (FTermF tf) = ppFlatTermF' opts (pp lcls) prec tf
  --(group . nest 2) <$> (ppFlatTermF' (pp lcls) p tf)
ppTermF' _opts pp lcls prec (App l r) = ppApp <$> pp lcls PrecApp l <*> pp lcls PrecArg r
  where ppApp l' r' = TermDoc $ ppAppParens prec $ group $ hang 2 $
                      ppTermDoc l' Leijen.<$> ppTermDoc r'

ppTermF' _opts pp lcls p (Lambda name tp rhs) =
    ppLam
      <$> pp lcls  PrecLambda tp
      <*> pp lcls' PrecLambda rhs
  where ppLam tp' rhs' = TermDoc $
          ppParens (p > PrecLambda) $ group $ hang 2 $
            text "\\" <> parens (text name' <> doublecolon <> ppTermDoc tp')
              <+> text "->" Leijen.<$> ppTermDoc rhs'
        name' = freshVariant (docUsedMap lcls) name
        lcls' = consBinding lcls name'

ppTermF' _opts pp lcls p (Pi name tp rhs) = ppPi <$> lhs <*> pp lcls' PrecLambda rhs
  where ppPi lhs' rhs' = TermDoc $ ppParens (p > PrecLambda) $
                         lhs' <<$>> text "->" <+> ppTermDoc rhs'
        subDoc = align . group . nest 2 . ppTermDoc
        lhs | name == "_" = subDoc <$> pp lcls PrecApp tp
            | otherwise = ppArg <$> pp lcls PrecLambda tp
        ppArg tp' = parens (text name' <+> doublecolon <+> subDoc tp')
        name' = freshVariant (docUsedMap lcls) name
        lcls' = consBinding lcls name'

ppTermF' _opts pp lcls p (Let dl u) =
    ppLet <$> traverse (ppLocalDef pp' lcls lcls') dl
          <*> pp lcls' PrecNone u
  where ppLet dl' u' = TermDoc $
          ppParens (p > PrecNone) $
            text "let" <+> lbrace <+> align (vcat dl') <$$>
            indent 4 rbrace <$$>
            text " in" <+> ppTermDoc u'
        nms = concatMap localVarNames dl
        lcls' = foldl' consBinding lcls nms
        pp' a b c = ppTermDoc <$> pp a b c
ppTermF' _opts _pp lcls _p (LocalVar i)
--    | lcls^.docShowLocalTypes = pptc <$> pp lcls PrecLambda tp
    | otherwise = pure $ TermDoc d
  where d = lookupDoc lcls i
--        pptc tpd = ppParens (p > PrecNone)
--                            (d <> doublecolon <> tpd)
ppTermF' _ _ _ _ (Constant i _ _) = pure $ TermDoc $ text i

-- | Pretty print a term with the given outer precedence.
ppTermlike :: forall t. Termlike t => PPOpts -> LocalVarDoc -> Prec -> t -> Doc
ppTermlike opts lcls0 p0 trm = ppTermDoc (pp lcls0 p0 trm)
  where
    pp :: LocalVarDoc -> Prec -> t -> TermDoc
    pp lcls p t = ppTermF opts pp lcls p (unwrapTermF t)

ppTermDepth :: forall t. Termlike t => PPOpts -> Int -> t -> Doc
ppTermDepth opts d0 = pp d0 emptyLocalVarDoc PrecNone
  where
    pp :: Int -> TermPrinter t
    pp d lcls p t = ppTermDoc (pp' d lcls p t)

    pp' :: Int -> LocalVarDoc -> Prec -> t -> TermDoc
    pp' 0 _ _ _ = TermDoc $ text "_"
    pp' d lcls p t = case unwrapTermF t of
      App t1 t2 -> TermDoc $
        ppAppParens p $ group $ hang 2 $
        (pp d lcls PrecApp t1) Leijen.<$>
        (pp (d-1) lcls PrecArg t2)
      tf ->
        ppTermF opts (pp' (d-1)) lcls p tf