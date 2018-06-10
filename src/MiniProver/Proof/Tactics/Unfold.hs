module MiniProver.Proof.Tactics.Unfold (
    handleUnfold
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename

deltaOne :: Int -> Term -> Term -> Term
deltaOne i tmst =
  tmMap (\nm c x -> if c + i == x then tmShift c tmst else TmRel nm x) 0

handleUnfold :: Goal -> Tactic -> Either TacticError Result
handleUnfold g@(Goal d ctx ty) u@(Unfold nm mbtm) =
  case nameToIndex ctx nm of
    Left UnboundName -> Left $ TacticError $ "Unbound name " ++ nm
    Left IsTypeConstructor -> Left $ TacticError "Can't unfold type constructors"
    Left IsConstructor -> Left $ TacticError "Can't unfold constructors"
    Right idx
      | idx < d -> Left $ TacticError "Can only unfold global bindings"
      | otherwise ->
        case mbtm of
          Nothing ->
            case getBinding ctx idx of
              Right (TmAbbBind _ Nothing) -> Left $ TacticError "Can't unfold axioms"
              Right (TmAbbBind _ (Just tm)) -> 
                let
                  binormalform = fullBIReduction ctx tm
                  newty = renameTerm ctx $ deltaOne idx binormalform ty
                in
                  Right $
                  Result
                  [ Goal d ctx newty ]
                  (\tmlst -> checkResult g u (head tmlst))
              _ -> error "This should not happen"
          Just hyponame ->
            case nameToIndex ctx hyponame of
              Left UnboundName -> Left $ TacticError $ "Unbound hypothesis name " ++ nm
              Left _ -> Left $ TacticError "Can only unfold in local bindings"
              Right hypoidx
                | hypoidx >= d -> Left $ TacticError "Can only unfold in local bindings"
                | otherwise ->
                  case getBinding ctx idx of
                    Right (TmAbbBind _ Nothing) -> Left $ TacticError "Can't unfold axioms"
                    Right (TmAbbBind _ (Just tm)) -> 
                      let
                        ((_,VarBind tybinder):ctxtl) = drop hypoidx ctx
                        ctxhd = take hypoidx ctx
                        binormalform = tmShift (-hypoidx-1) $ fullBIReduction ctx tm
                        newctx = ctxhd ++
                          ((hyponame,VarBind $ renameTerm' (hyponame:map fst ctxhd) ctxtl $
                              deltaOne (idx-hypoidx-1) binormalform tybinder):ctxtl)
                      in
                        Right $
                        Result
                        [ Goal d newctx ty ]
                        (\tmlst -> checkResult g u (head tmlst))


  
                  



