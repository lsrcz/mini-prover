module MiniProver.Core.Build (
    BuiltCommand
  , BuiltTerm
  , buildCommand
  , buildTerm
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Subst
import Data.Either (fromRight)

type BuiltCommand = Context -> Command
type BuiltTerm = Context -> Term
type BuiltEquation = Context -> Equation
type BuiltConstructor = Context -> Constructor

buildCommand :: Command -> BuiltCommand
buildCommand (Ax name tm) ctx = Ax name $ buildTerm tm ctx
buildCommand (Def name ty tm) ctx = Def name (buildTerm ty ctx) (buildTerm tm ctx)
buildCommand (Ind name int ty tm lst) ctx =
  Ind name int (buildTerm ty ctx) (buildTerm tm ctx) $
    map (\(namei, cty, ctm) -> (namei, buildTerm cty ctx, buildTerm ctm ctx)) lst
buildCommand (Fix name tm) ctx =
  Fix name (buildTerm tm ctx)
buildCommand (Theorem name tm) ctx = Theorem name $ buildTerm tm ctx
buildCommand (Check tm) ctx = Check $ buildTerm tm ctx

-- before building the term, check whether all the names are bounded
buildTerm :: Term -> BuiltTerm
buildTerm (TmVar name) ctx = 
  case nameToIndex ctx name of
    Right i -> TmRel name i
    Left IsConstructor -> 
      fromRight (error "This should not happen") $ getConstrTerm ctx name
    Left IsTypeConstructor -> 
      fromRight (error "This should not happen") $ getIndTypeTerm ctx name
    _ -> error "This should not happen"
buildTerm (TmAppl lst) ctx =
  case map (`buildTerm` ctx) lst of
    [] -> error "This should not happen"
    [h] -> h
    ls@(x:xs) ->
      case x of
        TmAppl ls' -> TmAppl $ ls' ++ xs
        _ -> TmAppl ls
buildTerm (TmProd name ty tm) ctx = 
  TmProd name (buildTerm ty ctx) (buildTerm tm (addName ctx name))
buildTerm (TmLambda name ty tm) ctx = 
  TmLambda name (buildTerm ty ctx) (buildTerm tm (addName ctx name))
buildTerm (TmFix n tm) ctx = TmFix n (buildTerm tm ctx)
buildTerm (TmLetIn name ty tm bdy) ctx =
  TmLetIn name 
    (buildTerm ty ctx) 
    (buildTerm tm ctx) 
    (buildTerm bdy (addName ctx name))
buildTerm (TmIndType name tmlst) ctx =
  TmIndType name $
    map (`buildTerm` ctx) tmlst
buildTerm (TmConstr name tmlst) ctx =
  TmConstr name $
    map (`buildTerm` ctx) tmlst
buildTerm TmType _ = TmType

buildTerm (TmMatch _ tm name namelst rty equlst) ctx =
  let
    Right(n, _) = getIndTypeType ctx (head namelst)
  in
    TmMatch n (buildTerm tm ctx) name namelst (buildTerm rty (addName (foldl addName ctx (drop (1+n) namelst)) name)) $
      map (\eq -> buildEquation n eq ctx) equlst
buildTerm _ _ = error "this should not happen"

buildEquation :: Int -> Equation -> BuiltEquation
buildEquation n (Equation namelst tm) ctx =
  Equation namelst $
    buildTerm tm (foldl addName ctx (drop (1+n) namelst))
