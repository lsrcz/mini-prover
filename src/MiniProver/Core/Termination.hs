{-# LANGUAGE LambdaCase #-}
module MiniProver.Core.Termination (
    isTerminating
  ) where

import           MiniProver.Core.Syntax

-- Not terminating => return Nothing
-- Terminating     => the number of arguments decreasing on
isTerminating :: Term -> Maybe Int
isTerminating (TmFix (TmLambda nm ty tm)) =
    let (d, term) = capArg 0 tm in
        forCheck d d term

haltCheck :: Int -> Int -> Int -> Term -> [Int] -> Bool
haltCheck deg d s term lst =
    case term of
      TmMatch (TmRel _ ind) [_] _ eqlst
        | (ind `elem` lst) || (ind == d) ->
            extMatchCheck deg d s eqlst lst
        | otherwise -> matchCheck deg d s eqlst lst
      TmMatch tm [_] _ eqlst ->
        (haltCheck deg d s tm lst) &&
        (matchCheck deg d s eqlst lst)
      TmAppl tmlst -> appCheck deg d s tmlst lst
      TmProd _ ty tm ->
        (haltCheck deg d s ty lst) &&
        (haltCheck (deg + 1) (d + 1) s tm (liftList 1 lst))
      TmLambda _ ty tm ->
        (haltCheck deg d s ty lst) &&
        (haltCheck (deg + 1) (d + 1) s tm (liftList 1 lst))
      TmFix tm ->
        haltCheck deg d s tm lst
      TmLetIn _ ty tm1 tm2 ->
        (haltCheck deg d s ty lst) &&
        (haltCheck deg d s tm1 lst) &&
        (haltCheck (deg + 1) (d + 1) s tm2 (liftList 1 lst))
      TmIndType _ tmlst ->
        all (\x -> haltCheck deg d s x lst) tmlst
      TmConstr _ tmlst ->
        all (\x -> haltCheck deg d s x lst) tmlst
      _ -> True

appCheck :: Int -> Int -> Int -> [Term] -> [Int] -> Bool
appCheck deg d s tmlst lst =
    case tmlst of
      [] -> True
      (TmRel _ ind):b
        | ind == deg -> spotCheck s b lst
        | otherwise -> all (\x -> haltCheck deg d s x lst) b
      _ -> all (\x -> haltCheck deg d s x lst) tmlst

spotCheck :: Int -> [Term] -> [Int] -> Bool
spotCheck s tmlst lst
    | s == 0 =
        case head tmlst of
          TmRel _ ind -> ind `elem` lst
          _           -> False
    | otherwise = spotCheck (s - 1) (tail tmlst) lst

extMatchCheck :: Int -> Int -> Int -> [Equation] -> [Int] -> Bool
extMatchCheck deg d s eq lst =
    all (\case
        Equation nm tm ->
            let l = length nm -1 in
                haltCheck (deg + l) (d + l) s tm ((liftList l lst) ++ [0..l-1]))
        eq

matchCheck :: Int -> Int -> Int -> [Equation] -> [Int] -> Bool
matchCheck deg d s eq lst =
    all (\case
        Equation nm tm ->
            let l = length nm -1 in
                haltCheck (deg + l) (d + l) s tm (liftList l lst))
        eq

forCheck :: Int -> Int -> Term -> Maybe Int
forCheck deg k term
    | k == 0 = Nothing
    | haltCheck deg (k - 1) (deg - k) term [] == False
        = forCheck deg (k - 1) term
    | otherwise = Just (deg - k + 1)

capArg :: Int -> Term -> (Int, Term)
capArg d term =
    case term of
      TmLambda _ _ tm ->
        capArg (d + 1) tm
      _ ->
        (d, term)

liftList :: Int -> [Int] -> [Int]
liftList d lst = map (+d) lst
