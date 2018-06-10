module MiniProver.Proof.Tactics.Intros (
    handleIntros
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Proof.Tactics.Intro
import MiniProver.Core.Typing
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.PrettyPrint.PrettyPrint
import Data.Either (fromRight)

handleIntros :: Goal -> Tactic -> Either TacticError Result
handleIntros g@(Goal d ctx ty) i@Intros = 
    case ty of 
        TmProd _ _ _ -> 
            let Result goals resultfunc = fromRight (error "This should not happen") $ 
                    handleIntro (Goal d ctx ty) (Intro []) in
                let curgoal = head goals in
                    let y = handleIntros curgoal Intros in
                        case y of
                            Right (Result goals' resultfunc') ->
                                Right $ Result goals' $ captureFunc resultfunc resultfunc'
                            Left str -> Left str
        _ -> 
            Right $ Result [(Goal d ctx ty)] (\tmlst -> checkResult g i (head tmlst))

captureFunc :: ([Term] -> Term) -> ([Term] -> Term) -> [Term] -> Term
captureFunc f1 f2 lst =
    f1 $ [f2 lst]
