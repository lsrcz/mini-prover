module MiniProver.TopLevel.IO where

import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST
import MiniProver.PrettyPrint.Colorful
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import Control.Monad (when)
import Data.List (elemIndex)
import System.IO

-- printing functions for verbose levels
printIfNoLessThan :: (Show a) => Int -> Int -> a -> IO ()
printIfNoLessThan i threshold x =
  when (i >= threshold) $ print x

putStrIfNoLessThan :: Int -> Int -> String -> IO ()
putStrIfNoLessThan i threshold str =
  when (i >= threshold) $ putStr str

putStrLnIfNoLessThan :: Int -> Int -> String -> IO ()
putStrLnIfNoLessThan i threshold str =
  when (i >= threshold) $ putStrLn str

prettyPrintIfNoLessThan :: Int -> Int -> Term -> IO ()
prettyPrintIfNoLessThan i threshold tm =
  when (i >= threshold) $ prettyPrint tm

prettyPrintCommandIfNoLessThan :: Int -> Int -> Command -> IO ()
prettyPrintCommandIfNoLessThan i threshold cmd =
  when (i >= threshold) $ prettyPrintCommand cmd

prettyPrintASTIfNoLessThan :: Int -> Int -> Term -> IO ()
prettyPrintASTIfNoLessThan i threshold tm =
  when (i >= threshold) $ prettyPrintAST tm

prettyPrintCommandASTIfNoLessThan :: Int -> Int -> Command -> IO ()
prettyPrintCommandASTIfNoLessThan i threshold cmd =
  when (i >= threshold) $ prettyPrintCommandAST cmd

errorColor :: String -> String
errorColor = frontGroundColor BRED

infoColor :: String -> String
infoColor = frontGroundColor BYELLOW

okColor :: String -> String
okColor = frontGroundColor BGREEN

getInputCommand :: IO String
getInputCommand = do
  str <- getLine 
  case elemIndex '.' str of
    Just t -> return $ take (t + 1) str
    Nothing -> do
      str1 <- getInputCommand
      return $ str ++ " " ++ str1

hGetInputCommand :: Handle -> IO String
hGetInputCommand handle = do
  eofFlag <- hIsEOF handle
  if eofFlag
    then return ""
    else do
      str <- hGetLine handle
      case elemIndex '.' str of
        Just t -> return $ take (t + 1) str
        Nothing -> do
          str1 <- hGetInputCommand handle
          return $ str ++ " " ++ str1

removeLeadingSpaces :: String -> String
removeLeadingSpaces [] = []
removeLeadingSpaces str@(x:xs)
  | x == ' ' = removeLeadingSpaces xs
  | otherwise = str
