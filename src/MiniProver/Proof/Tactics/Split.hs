module MiniProver.Proof.Tactics.Split (
    handleSplit
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import Data.Either

split :: Goal -> Tactic -> [Term] -> Result
split g@(Goal d ctx ty) r tmlst =
  let
    a = head tmlst
    b = head $ tail tmlst
  in
    Result [Goal d ctx a, Goal d ctx b]
      (\[t1,t2] -> checkResult g r (TmConstr "conj" [a,b,t1,t2]))

handleSplit :: Goal -> Tactic -> Either TacticError Result
handleSplit g@(Goal d ctx ty) s@Split =
  case ty of
    TmIndType name tmlst
      | name == "and" -> Right $ split g s tmlst
    _ ->
      let
        strategy =
          StrategySet (strategyListToSet [BetaLambda]) 0 0 0
      in
        case reductionWithStrategy strategy ctx ty of
          TmIndType name tmlst
            | name == "and" -> Right $ split g s tmlst
          TmAppl (rel@TmRel{}:xs) ->
            case reductionWithStrategy strategy ctx $ TmAppl (deltaReduction ctx rel:xs) of
              TmIndType name tmlst
                | name == "and" -> Right $ split g s tmlst
              _ ->
                Left $ TacticError "No and or iff type found"
          _ ->
            Left $ TacticError "No and or iff type found"
