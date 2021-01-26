{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Verifier.SAW.Cryptol.Prelude
-- Copyright   : Galois, Inc. 2021
-- License     : BSD3
-- Maintainer  : val@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
module Verifier.SAW.Translation.Coq.CryptolPrelude
  ( writeCoqCryptolPrimitivesForSAWCore,
  )
where

import Data.Text.Prettyprint.Doc (vcat)
import Verifier.SAW.Cryptol.Prelude
import Verifier.SAW.Module (emptyModule)
import Verifier.SAW.Name (mkModuleName)
import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Translation.Coq as Coq
import qualified Verifier.SAW.UntypedAST as Untyped

coqTranslationConfiguration ::
  [(String, String)] ->
  [String] ->
  Coq.TranslationConfiguration
coqTranslationConfiguration notations skips = Coq.TranslationConfiguration
  { Coq.notations          = notations
  , Coq.monadicTranslation = False
  , Coq.skipDefinitions    = skips
  , Coq.vectorModule       = "SAWVectorsAsCoqVectors"
  }

nameOfCryptolPrimitivesForSAWCoreModule :: Untyped.ModuleName
nameOfCryptolPrimitivesForSAWCoreModule = Untyped.moduleName cryptolModule

writeCoqCryptolPrimitivesForSAWCore ::
  FilePath ->
  [(String, String)] ->
  [String] ->
  IO ()
writeCoqCryptolPrimitivesForSAWCore outputFile notations skips = do
  sc <- mkSharedContext
  () <- scLoadPreludeModule sc
  () <- scLoadCryptolModule sc
  () <- scLoadModule sc (emptyModule (mkModuleName ["CryptolPrimitivesForSAWCore"]))
  m <- scFindModule sc nameOfCryptolPrimitivesForSAWCoreModule
  let configuration = coqTranslationConfiguration notations skips
  let doc = Coq.translateSAWModule configuration m
  let extraPreamble =
        vcat
          [ "From CryptolToCoq Require Import SAWCorePrelude.",
            "Import SAWCorePrelude."
          ]
  writeFile
    outputFile
    ( show . vcat $
        [ Coq.preamblePlus configuration extraPreamble,
          doc
        ]
    )
