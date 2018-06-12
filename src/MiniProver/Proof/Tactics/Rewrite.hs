module MiniProver.Proof.Tactics.Rewrite (
    handleRewrite
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Proof.Tactics.Apply
import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.SimplifyIndType
import MiniProver.Core.Subst
import MiniProver.Core.Context
import MiniProver.PrettyPrint.PrettyPrint
import Debug.Trace
handleRewrite :: Goal->Tactic->Either TacticError Result
handleRewrite g@(Goal num ctx goal) (Rewrite flag t Nothing) = 
  case typeof ctx t of
    Left (TypingError _ er) -> Left (TacticError ("typing error!" ++ er))
    Right ty -> 
      case fullBZIDReduction ctx ty of 
        TmIndType "eq" [eqTy,x,y] ->
          let 
            newGoal = caseReplace x y goal flag 
          in 
            let
              p =getP ctx eqTy goal t newGoal x y flag
            in
              (trace (show p)handleApply g (Apply p Nothing) )
        _ -> Left (TacticError "The type of term is not eq type")


handleRewrite g@(Goal num ctx goal) (Rewrite flag t (Just name)) = 
  case typeof ctx t of
    Left (TypingError _ er) -> Left (TacticError ("typing error!" ++ er))
    Right ty -> 
      case fullBZIDReduction ctx ty of 
        TmIndType "eq" [eqTy,x,y] ->
          case nameToIndex ctx name of
            Left er -> Left (TacticError "No this name")
            Right index ->
              let
                (Right ty1) = getBindingType ctx index
              in
                let 
                  p = getP' ctx eqTy goal t ty1 x y flag
                in
                  (trace (show p) handleApply g (Apply p (Just name)))
        _ -> Left (TacticError "The type of term is not eq type")
getP' :: Context->Term->Term->Term->Term->Term->Term->Bool->Term
getP' ctx eqTy goal t ty1 x y flag =
  let
    (Right index1) = nameToIndex ctx "eq_rect"
    (Right index2) = nameToIndex ctx "eq_rect_r"
  in
    case flag of
      False ->
        TmLambda
          ""
          ty1
          (TmAppl  
            [ (TmRel "eq_rect" (index1+1)),
              (tmShift 1 eqTy),
              (tmShift 1 x),
              (TmLambda
                ""
                (tmShift 1 eqTy)
                (TmLambda
                  ""
                  (TmIndType "eq" [(tmShift 2 eqTy),(tmShift 2 x),(TmRel "" 0)])
                  (replace (TmRel "" 1) (tmShift 3 x) (tmShift 3 goal)))),
              (TmRel "" 0),  -- ??????
              (tmShift 1 y),
              (tmShift 1 t)
            ])
      True ->
        TmLambda
          ""
          ty1
          (TmAppl  
            [ (TmRel "eq_rect_r" (index2+1)),  
              (tmShift 1 eqTy),
              (tmShift 1 y),
              (TmLambda
                ""
                (tmShift 1 eqTy)
                (TmLambda
                  ""
                  (TmIndType "eq" [(tmShift 2 eqTy),(tmShift 2 y),(TmRel "" 0)])
                  (replace (TmRel "" 1) (tmShift 3 y) (tmShift 3 goal)))),
              (TmRel "" 0),  -- ??????
              (tmShift 1 x),
              (tmShift 1 t)
            ])


getP :: Context->Term->Term->Term->Term->Term->Term->Bool->Term
getP ctx eqTy goal t newGoal x y flag =
  let
    (Right index1) = nameToIndex ctx "eq_rect"
    (Right index2) = nameToIndex ctx "eq_rect_r"
  in
    case flag of
      True ->
        TmLambda 
          "" 
          newGoal 
          (TmAppl  
            [ (TmRel "eq_rect" (index1+1)),
              (tmShift 1 eqTy),
              (tmShift 1 x),
              (TmLambda
                ""
                (tmShift 1 eqTy)
                (TmLambda
                  ""
                  (TmIndType "eq" [(tmShift 2 eqTy),(tmShift 2 x),(TmRel "" 0)])
                  (replace (TmRel "" 1) (tmShift 3 y) (tmShift 3 goal)))),
              (TmRel "" 0),  -- ??????
              (tmShift 1 y),
              (tmShift 1 t)
            ])
      False ->
        TmLambda 
          "" 
          newGoal
          (TmAppl  
            [ (TmRel "eq_rect_r" (index2+1)),
              (tmShift 1 eqTy),
              (tmShift 1 y),
              (TmLambda
                ""
                (tmShift 1 eqTy)
                (TmLambda
                  ""
                  (TmIndType "eq" [(tmShift 2 eqTy),(tmShift 2 y),(TmRel "" 0)])
                  (replace (TmRel "" 1) (tmShift 3 x) (tmShift 3 goal)))),
              (TmRel "" 0),  -- ??????
              (tmShift 1 x),
              (tmShift 1 t)
            ])             

caseReplace :: Term->Term->Term->Bool->Term
caseReplace x y goal flag =
  case flag of
    True -> replace x y goal
    False -> replace y x goal

replace :: Term->Term->Term->Term
replace x y t@(TmAppl ls) =
  if termEqNameless t y
    then x
    else
      (TmAppl
        (map
          (replace x y)
          ls))
replace x y t@(TmLambda name ty tm) =
  if termEqNameless t y
    then x
    else
      (TmLambda
        name
        (replace x y ty)
        (replace (tmShift 1 x) (tmShift 1 y) tm))
replace x y t@(TmProd name ty tm) =
  if termEqNameless t y
    then x
    else
      (TmProd
        name
        (replace x y ty)
        (replace (tmShift 1 x) (tmShift 1 y) tm))
replace x y t@(TmLetIn name t1 t2 t3) = 
  if termEqNameless t y
    then x
    else
      (TmLetIn
        name
        (replace x y t1)
        (replace x y t2)
        (replace (tmShift 1 x) (tmShift 1 y) t3))
replace x y t@(TmIndType name ls) =
  if termEqNameless t y
    then x
    else
      (TmIndType
        name
        (map
          (replace x y)
          ls))
replace x y t@(TmConstr name ls) =
  if termEqNameless t y
    then x
    else
      (TmConstr
        name
        (map
          (replace x y)
          ls))
replace x y t@(TmMatch num t1 name nameLs t2 eqLs) =
  if termEqNameless t y
    then x
    else
      (TmMatch
        num
        (replace x y t1)
        name
        nameLs
        (replace 
          (tmShift ((length nameLs)-num) x) 
          (tmShift ((length nameLs)-num) y) 
          t2)
        (map
          (\(Equation nameLs t)->
            (Equation 
              nameLs
              (replace 
                (tmShift ((length nameLs)-num-1) x)
                (tmShift ((length nameLs)-num-1) y)
                t)))
          eqLs))

replace x y t =
  if termEqNameless t y
    then x
    else t  
