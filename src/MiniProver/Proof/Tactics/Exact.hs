module MiniProver.Proof.Tactics.Exact (
    handleExact
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.Core.SimplifyIndType
import MiniProver.PrettyPrint.PrettyPrint

handleExact :: Goal -> Tactic -> Either TacticError Result
handleExact g@(Goal _ ctx ty) e@(Exact tm) =
  case typeof ctx tm of
    Left err -> Left $ TacticError $ 
      case err of
        TypingError tm1 str ->
          "Typing error in term:\n" ++ prettyShow tm1 ++ "\nin term:\n" ++
          prettyShow tm ++ "\n" ++ str
    Right ty1 ->
      if typeeq ctx (Right ty) (Right ty1)
        then Right (Result [] (\[] -> checkResult g e (simplifyIndType tm)))
        else Left $ TacticError $
          "The term:\n" ++ prettyShow tm ++
          "\nhas the type:\n" ++ prettyShow ty1 ++
          "\ndoesn't match the goal's type\n" ++ prettyShow ty
