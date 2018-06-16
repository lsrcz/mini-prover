{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
module Main where

import MiniProver.TopLevel.TopLoop
import MiniProver.Utils.ContextForTesting
import System.IO
import System.Console.CmdArgs

newtype VerboseLevel = VerboseLevel {verbose :: Int}
                   deriving (Show, Data, Typeable)

defaultVerbose = VerboseLevel {verbose=0 &= help "Change the verbose flag"}

main :: IO ()
main = do
  VerboseLevel l <-  cmdArgs defaultVerbose
  let
    verboseLevel
      | l <= 0 = 0
      | l >= 3 = 3
      | otherwise =l
  handle <- openFile "./libs/Init/Prelude.v" ReadMode
  p <- processFile handle 0 []
  ctx <- topLoop verboseLevel p
  print ctx

