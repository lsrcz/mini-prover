module Main where

import MiniProver.TopLevel.TopLoop
import MiniProver.Utils.ContextForTesting
import System.IO

main :: IO ()
main = do
  handle <- openFile "./libs/Init/Prelude.1.v" ReadMode
  p <- processFile handle 0 []
  ctx <- topLoop 3 p --ilistContext
  print ctx

{-
main :: IO ()
main = putStrLn "n" 
-}
