module MiniProver.Proof.Tactics.Exists (
    handleExists
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import Data.Either

exists :: Goal -> Tactic -> [Term] -> Term -> Result
exists g@(Goal d ctx ty) e tmlst tm =
  let
    a = head tmlst
    p = head $ tail tmlst
    strategy =
      StrategySet (strategyListToSet [BetaLambda]) 0 0 0
  in
    Result [Goal d ctx $ reductionWithStrategy strategy ctx (TmAppl [p,tm])]
      (\[t1] -> checkResult g e (TmConstr "ex_intro" [a,p,tm,t1]))

handleExists :: Goal -> Tactic -> Either TacticError Result
handleExists g@(Goal d ctx ty) e@(Exists tm) =
  case ty of
    TmIndType name tmlst
      | name == "ex" -> Right $ exists g e tmlst tm
    _ ->
      let
        strategy =
          StrategySet (strategyListToSet [BetaLambda]) 0 0 0
      in
        case reductionWithStrategy strategy ctx ty of
          TmIndType name tmlst
            | name == "ex" -> Right $ exists g e tmlst tm
          _ ->
            Left $ TacticError "No or type found"
