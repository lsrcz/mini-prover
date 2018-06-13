{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.Simpl (
    handleSimpl
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename

handleSimpl :: Goal -> Tactic -> Either TacticError Result
handleSimpl g@(Goal d ctx ty) s@(Simpl Nothing) =
  Right $ Result
  [ Goal d ctx
    ( reductionWithStrategy
      ( clearStrategyInSet (clearStrategyInSet fullBZIDStrategySet DeltaRestricted) DeltaRel)
      ctx ty)]
  (\[tm] -> checkResult g s tm)
handleSimpl g@(Goal d ctx ty) s@(Simpl (Just name)) =
  case nameToIndex ctx name of
    Left UnboundName -> Left $ TacticError $ "Unbound hypothesis name " ++ name
    Left _ -> Left $ TacticError "Can only simpl in local bindings"
    Right hypoidx
      | hypoidx >= d -> Left $ TacticError "Can only simpl in local bindings"
      | otherwise -> Right $ Result
        [ Goal d (simplIth hypoidx ctx) ty ]
        (\[tm] -> checkResult g s tm)

simplIth :: Int -> Context -> Context
simplIth i (x@(name, VarBind ty):xs)
  | i > 0 = x : simplIth (i-1) xs
  | otherwise =
    (name, VarBind $
      reductionWithStrategy
        ( clearStrategyInSet (clearStrategyInSet fullBZIDStrategySet DeltaRestricted) DeltaRel)
        xs ty) : xs
simplIth i (x:xs) = error (show i ++ show x)


