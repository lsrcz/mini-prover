{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.Equivalence (
    handleEquivalence
  , findContradition
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import MiniProver.PrettyPrint.PrettyPrintAST
import MiniProver.Proof.Tactics.Induction
import Debug.Trace
import Data.Maybe

buildRefllst :: Term -> Int -> [Term] -> [Term]
buildRefllst _ _ [] = []
buildRefllst ity@(TmProd _ ty tm) i (x:xs)
  | i > 0 = buildRefllst (betaReduction $ TmAppl [ity, x]) (i - 1) xs
  | otherwise = TmConstr "eq_refl" [ty,x] : buildRefllst (betaReduction $ TmAppl [ity, x]) (i - 1) xs

buildMatchRetType :: Goal -> Term -> Int -> Int -> Int -> [Term] -> Term
buildMatchRetType g@(Goal _ _ gty) _ base depth _ [] =
  tmShift (base - depth + 2) gty
buildMatchRetType g ity@(TmProd _ ty tm) base depth shiftconst (x:xs)
  | depth > 0 = buildMatchRetType g (betaReduction $ TmAppl [ity, x]) base (depth - 1) shiftconst xs
  | otherwise = TmProd "." (TmIndType "eq" [tmShift (base - depth + 2) ty, TmRel "." shiftconst, tmShift (base - depth + 2) x])
      $ buildMatchRetType g tm base (depth - 1) shiftconst xs

lengthOfConstr :: Term -> Int
lengthOfConstr (TmProd _ _ tm) = 1 + lengthOfConstr tm
lengthOfConstr TmIndType{} = 0

buildRetTypeWithLambda :: Term -> Int -> Term
buildRetTypeWithLambda tm i
  | i == 0 = TmLambda "." TmType tm
  | i > 0 = TmLambda "." TmType $ buildRetTypeWithLambda tm (i - 1)

applyToInnerMostConstr :: Int -> Term -> Term -> Term
applyToInnerMostConstr i (TmProd name ty tm) retty = TmProd name ty $
  applyToInnerMostConstr i tm (tmShift 1 retty)
applyToInnerMostConstr i (TmIndType _ tmlst) retty = 
  let
    strategy =
      StrategySet (strategyListToSet [BetaLambda]) 0 0 0
  in
    reductionWithStrategy strategy [] (TmAppl (retty:drop i tmlst++[TmType]))

removeProd :: Term -> Term
removeProd (TmProd _ _ tm) = removeProd tm
removeProd tm = tm

removeLambda :: Term -> Term
removeLambda (TmLambda _ _ tm) = removeLambda tm
removeLambda tm = tm

removeAbst :: Term -> Int -> Term
removeAbst tm i
  | i == 0 = tm
removeAbst (TmLambda _ _ tm) i = removeAbst tm (i - 1)
removeAbst (TmProd _ _ tm) i = removeAbst tm (i - 1)

buildMatchBranchType :: Term -> Int -> [Term] -> Term -> Term
buildMatchBranchType constrty i tmlst retty =
  let
    strategy =
      StrategySet (strategyListToSet [BetaProd]) 0 0 0
    constrtyTail = reductionWithStrategy strategy [] (TmAppl (constrty:take i tmlst))
    branchType = applyToInnerMostConstr i constrtyTail retty
  in
    removeAbst branchType (lengthOfConstr constrty - i)

prodToLambda :: Term -> Term
prodToLambda (TmProd name ty tm) = TmLambda name ty (prodToLambda tm)
prodToLambda tm = tm

buildMatchBranch :: Constructor -> Int -> [Term] -> Term -> Equation
buildMatchBranch (Constructor name ty _) i tmlst tmret =
  Equation (name:replicate i "_"++replicate (lengthOfConstr ty - i) ".") $
  prodToLambda (buildMatchBranchType ty i tmlst tmret)

buildMatchTerm :: Goal -> Tactic -> (Int, Term, Term, [Constructor]) -> Term -> Int -> Term
buildMatchTerm g@(Goal d ctx ty) e@(Equivalence name) (i,ity,itm,constrlst) (TmIndType iname tmlst) idx =
  let
    rettype = buildMatchRetType g ity i i (length tmlst - 1) tmlst
    rettypeWithLambda = buildRetTypeWithLambda rettype (length tmlst - i)
  in
  TmMatch i (TmRel name idx) "." (iname:replicate i "_"++replicate (length tmlst - i) ".")
  rettype
  (map (\constr -> buildMatchBranch constr i tmlst rettypeWithLambda) constrlst)

buildNotEqEquivalence :: Goal -> Tactic -> Term -> Int -> Result
buildNotEqEquivalence g@(Goal d ctx ty) e@(Equivalence name) it@(TmIndType iname tmlst) idx =
  case getIndType ctx iname of
    Left err -> error "This should not happen"
    Right ind@(i,ity,itm,constrlst) ->
      buildResultFromTerm
      (renameTerm ctx $
      TmAppl (buildMatchTerm g e ind it idx : buildRefllst ity i tmlst))
      g e (length tmlst - i)

buildGoalFromTerm :: Int -> Term -> Goal -> Goal
buildGoalFromTerm j t (Goal d ctx _)
  | j == 0 = Goal d ctx t
  | otherwise =
    case t of
      TmLambda name ty tm ->
        buildGoalFromTerm (j - 1) tm (Goal (d + 1) (addBinding ctx name (VarBind ty)) t)
{-

        case buildGoalFromTerm (j-1) tm (Goal d ctx tm) of
          Goal d1 ctx1 t1 -> Goal (d1 + 1) (addBinding ctx1 name (VarBind ty)) t1 -}

substGoalTerm :: Int -> Term -> Term -> Term
substGoalTerm j _ goaltm
  | j == 0 = goaltm
substGoalTerm j (TmLambda name ty tm) goaltm =
  TmLambda name ty (substGoalTerm (j - 1) tm goaltm)

buildResultFromTerm :: Term -> Goal -> Tactic -> Int -> Result
buildResultFromTerm (TmAppl (TmMatch i tm n namelst retty equlst:lst)) g@(Goal d ctx ty) e numOfParam = Result
  (map (\case Equation namelst equtm -> buildGoalFromTerm numOfParam equtm g) equlst)
  (\tmlst -> checkResult g e $ renameTerm ctx $ TmAppl (TmMatch i tm n namelst retty
    (map (\case (Equation namelst equtm, goaltm) -> Equation namelst $ substGoalTerm numOfParam equtm goaltm) $ zip equlst tmlst)
  :lst))

typeTotParam :: Term -> Int
typeTotParam (TmProd _ _ tm) = typeTotParam tm
typeTotParam (TmLambda _ _ tm) = typeTotParam tm
typeTotParam (TmIndType _ lst) = length lst
typeTotParam (TmConstr _ lst) = length lst

makeEquation :: Int -> Term -> Constructor -> Equation
makeEquation i tminner (Constructor name ty tm) =
  Equation (name:replicate i "_"++replicate (typeTotParam tm - i) ".") tminner

buildEquationWithOneNameTrue :: Term -> Int -> Name -> [Constructor] -> [Equation]
buildEquationWithOneNameTrue _ _ _ [] = []
buildEquationWithOneNameTrue onetm i name1 (constr@(Constructor name ty tm):xs)
  | name == name1 = makeEquation i onetm constr : buildEquationWithOneNameTrue onetm i name1 xs
  | otherwise = makeEquation i (TmIndType "False" []) constr : buildEquationWithOneNameTrue onetm i name1 xs

findContradition :: Int -> Context -> Term -> Term -> Maybe Term
findContradition idx ctx (TmConstr name1 tmlst) (TmConstr name2 tmlst2)
  | name1 /= name2 =
    let
      Right indname = getConstrIndTypeName ctx name1
      Right (i,ty,tm,constrlst) = getIndType ctx indname
      ntotind = typeTotParam tm
    in Just $
      TmMatch 
        i
        (TmRel "." idx)
        "." (indname:replicate i "_"++replicate (ntotind - i) ".") TmType
        (buildEquationWithOneNameTrue (TmIndType "True" [] ) i name1 constrlst)
  | name1 == name2 =
    let
      Right indname = getConstrIndTypeName ctx name1
      Right (i,ty,tm,constrlst) = getIndType ctx indname
      ntotind = typeTotParam tm
      innertms = filter isJust
        (map (\(tm1,tm2,i) -> findContradition i ctx tm1 tm2) $
          zip3 (reverse $ drop i tmlst) (reverse tmlst2) [0..])
    in
      if null innertms
        then
          Nothing
        else
          let
            Just x = head innertms
            (TmMatch _ r _ _ _ _) = x
            (TmMatch i _ n ns retty eq) = tmShift (length tmlst - i) x

          in
          Just $
          TmMatch i (TmRel "." idx) "." (indname:replicate i "_"++replicate (ntotind - i) ".") TmType

          (buildEquationWithOneNameTrue (TmMatch i r n ns retty eq) i name1 constrlst)



-- when applied to a hypothesis that is not a eq, it checks the equivalence
-- relation in the type
-- when applied to a hypothesis that is a eq, it check the equivalence of
-- the rhs and lhs
handleEquivalence :: Goal -> Tactic -> Either TacticError Result
handleEquivalence g@(Goal d ctx ty) e@(Equivalence name) =
  case nameToIndex ctx name of
    Left UnboundName -> Left $ TacticError $ "Unbound name " ++ name
    Left IsTypeConstructor -> Left $ TacticError "Can only inversion on local terms with inductive types"
    Left IsConstructor -> Left $ TacticError "Can only inversion on local terms with inductive types"
    Right idx
      | idx >= d -> Left $ TacticError "Can only inversion on local terms with inductive types"
      | otherwise -> trace (show idx) $
        case getBindingType ctx idx of
          Left err -> error "This should not happen"
          Right itype@(TmIndType iname tmlst)
            | iname == "eq" -> handleInduction g (Induction (TmRel name idx))
            | otherwise ->
              Right $ buildNotEqEquivalence g e itype idx
              
