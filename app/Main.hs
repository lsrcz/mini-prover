module Main where

import MiniProver.TopLevel.TopLoop
import MiniProver.Utils.ContextForTesting
import System.IO

main :: IO ()
main = do
  handle <- openFile "./libs/Init/Prelude.v" ReadMode
  -- p <- processFile handle 1 []
  ctx <- topLoop 3 realEx2Context --ilistContext
  print ctx

{-
main :: IO ()
main = putStrLn "n" 
-}
