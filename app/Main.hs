module Main where

import MiniProver.TopLevel.TopLoop
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = do
  ctx <- processOneCommand 3 ilistContext
  print ctx

{-
main :: IO ()
main = putStrLn "n" 
-}
