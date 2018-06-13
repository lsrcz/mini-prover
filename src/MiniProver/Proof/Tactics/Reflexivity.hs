module MiniProver.Proof.Tactics.Reflexivity (
    handleReflexivity
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename

handleReflexivity :: Goal -> Tactic -> Either TacticError Result
handleReflexivity g@(Goal d ctx ty) r@Reflexivity =
  case ty of
    TmIndType name tmlst
      | name == "eq" ->
        if termEqNameless (fullBZIDReduction ctx $ tmlst !! 1) (fullBZIDReduction ctx $ tmlst !! 2)
          then Right $ Result [] (\[] -> checkResult g r (TmConstr "eq_refl" $ take 2 tmlst))
          else Left $ TacticError "The types of the two sides don't match"
    _ ->
      let
        strategy =
          StrategySet (strategyListToSet [BetaLambda]) 0 0 0
      in
        case reductionWithStrategy strategy ctx ty of
          TmIndType name tmlst
            | name == "eq" ->
              if termEqNameless (fullBZIDReduction ctx $ tmlst !! 1) (fullBZIDReduction ctx $ tmlst !! 2)
                then Right $ Result [] (\[] -> checkResult g r (TmConstr "eq_refl" $ take 2 tmlst))
                else Left $ TacticError "The types of the two sides don't match"
          _ ->
            case fullBZIDReduction ctx ty of
              TmIndType name tmlst
                | name == "eq" ->
                  if termEqNameless (tmlst !! 1) (tmlst !! 2)
                    then Right $ Result [] (\[] -> checkResult g r (TmConstr "eq_refl" $ take 2 tmlst))
                    else Left $ TacticError "The types of the two sides don't match"
              _ ->
                Left $ TacticError "No eq type found"
