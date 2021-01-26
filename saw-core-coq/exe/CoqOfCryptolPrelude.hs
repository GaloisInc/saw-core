module Main where

import Verifier.SAW.Translation.Coq.CryptolPrelude ( writeCoqCryptolPrimitivesForSAWCore )

main :: IO ()
main = do
  writeCoqCryptolPrimitivesForSAWCore "coq/generated/CryptolToCoq/CryptolPrelude.v" [] []
