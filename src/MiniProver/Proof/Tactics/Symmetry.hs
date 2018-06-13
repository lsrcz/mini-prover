module MiniProver.Proof.Tactics.Symmetry (
    handleSymmetry
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import Data.Either

symmetry :: Goal -> Tactic -> Index -> [Term] -> Result
symmetry g@(Goal d ctx ty) r idx tmlst =
  let
    t = head tmlst
    t1 = tmlst !! 1
    t2 = tmlst !! 2
  in
    Result [Goal d ctx (TmIndType "eq" [t,t2,t1])]
      (\[tm] -> checkResult g r (TmAppl [TmRel "eq_sym" idx, t, t2, t1, tm]))

handleSymmetry :: Goal -> Tactic -> Either TacticError Result
handleSymmetry g@(Goal d ctx ty) s@Symmetry =
  let idx = fromRight undefined $ nameToIndex ctx "eq_sym" in
  case ty of
    TmIndType name tmlst
      | name == "eq" -> Right $ symmetry g s idx tmlst
    _ ->
      let
        strategy =
          StrategySet (strategyListToSet [BetaLambda]) 0 0 0
      in
        case reductionWithStrategy strategy ctx ty of
          TmIndType name tmlst
            | name == "eq" -> Right $ symmetry g s idx tmlst
          _ ->
            Left $ TacticError "No eq type found"
