module MiniProver.Proof.Tactics.Intro (
    handleIntro
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Rename
import MiniProver.PrettyPrint.PrettyPrint
import Debug.Trace

handleIntro :: Goal -> Tactic -> Either TacticError Result
handleIntro goal tactic =
    let x = introFunc goal tactic in
        case x of
            Right (onegoal, outparam) ->
                Right $ Result [onegoal] (captureOutParam outparam) 
            Left str -> Left str

introFunc :: Goal -> Tactic -> Either TacticError (Goal, [(Name, Term)])
introFunc (Goal d ctx ty) (Intro []) = 
    case ty of 
        TmProd nm ty1 tm1 -> 
            let newnm = getNewName ctx nm ty1 in
                let ctx' = addBinding ctx newnm $ VarBind ty1 in
                    let newtm = renameTerm ctx' tm1 in
                        Right ((Goal (d + 1) ctx' newtm), [(newnm, ty1)])
        _ -> Left $ TacticError "No enough products"
introFunc (Goal d ctx ty) (Intro (nm1:nmlst)) =
    case ty of
        TmProd nm ty1 tm1 ->
            let newnm = getNewName ctx nm1 ty1 in
                if newnm /= nm1 && nm /= "_" then 
                    Left $ TacticError $ "Name "++nm++" already used"
                else 
                    let ctx' = addBinding ctx newnm $ VarBind ty1 in
                        let newtm = renameTerm ctx' tm1 in
                            case nmlst of
                                [] -> 
                                    Right ((Goal (d + 1) ctx' newtm), [(newnm, ty1)])
                                _ -> 
                                    let x = introFunc (Goal (d + 1) ctx' newtm) (Intro nmlst) in
                                        case x of 
                                            Right (tg, tlst) -> Right (tg, tlst++[(newnm, ty1)]) 
                                            Left str -> Left str
        _ -> Left $ TacticError "No enough products"



captureOutParam :: [(Name, Term)] -> [Term] -> Term
captureOutParam lst1 lst2 = warpOutParam lst1 $ head lst2

warpOutParam :: [(Name, Term)] -> Term -> Term
warpOutParam [] tm = tm
warpOutParam ((x, y):b) tm = 
    warpOutParam b $ TmLambda x y tm


getNewName :: Context -> Name -> Term -> Name
getNewName ctx nm tm = rightPair $
    if nm == "_" then 
        addAnonymousName ctx [] "." $ Just tm
    else if isNameBound ctx nm then
            addAnonymousName ctx [] nm $ Just tm
    else ([], nm)
            


rightPair :: (a, b) -> b
rightPair (x, y) = y
