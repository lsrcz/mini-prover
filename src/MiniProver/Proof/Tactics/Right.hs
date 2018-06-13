module MiniProver.Proof.Tactics.Right (
    handleRight
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import Data.Either

right :: Goal -> Tactic -> [Term] -> Result
right g@(Goal d ctx ty) r tmlst =
  let
    a = head tmlst
    b = head $ tail tmlst
  in
    Result [Goal d ctx b]
      (\[t1] -> checkResult g r (TmConstr "or_intror" [a,b,t1]))

handleRight :: Goal -> Tactic -> Either TacticError Result
handleRight g@(Goal d ctx ty) s@RightTac =
  case ty of
    TmIndType name tmlst
      | name == "or" -> Right $ right g s tmlst
    _ ->
      let
        strategy =
          StrategySet (strategyListToSet [BetaLambda]) 0 0 0
      in
        case reductionWithStrategy strategy ctx ty of
          TmIndType name tmlst
            | name == "or" -> Right $ right g s tmlst
          _ ->
            Left $ TacticError "No or type found"
