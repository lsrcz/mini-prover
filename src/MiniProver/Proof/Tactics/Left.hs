module MiniProver.Proof.Tactics.Left (
    handleLeft
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import Data.Either

left :: Goal -> Tactic -> [Term] -> Result
left g@(Goal d ctx ty) r tmlst =
  let
    a = head tmlst
    b = head $ tail tmlst
  in
    Result [Goal d ctx a]
      (\[t1] -> checkResult g r (TmConstr "or_introl" [a,b,t1]))

handleLeft :: Goal -> Tactic -> Either TacticError Result
handleLeft g@(Goal d ctx ty) s@LeftTac =
  case ty of
    TmIndType name tmlst
      | name == "or" -> Right $ left g s tmlst
    _ ->
      let
        strategy =
          StrategySet (strategyListToSet [BetaLambda]) 0 0 0
      in
        case reductionWithStrategy strategy ctx ty of
          TmIndType name tmlst
            | name == "or" -> Right $ left g s tmlst
          _ ->
            Left $ TacticError "No or type found"
