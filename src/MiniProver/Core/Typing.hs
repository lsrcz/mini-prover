module MiniProver.Core.Typing (
    TypingError(..)
  , simplifyType
  , typeof
  , checkCommandType
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import MiniProver.Core.Context
import MiniProver.Core.Reduction
import MiniProver.Core.SimplifyIndType
import MiniProver.PrettyPrint.PrettyPrint
import Debug.Trace

data TypingError = 
    TypingError Term String
  deriving (Eq, Show)

-- Trying to simplify the type to a still readable term
-- only do beta-reduction in certain cases
-- should only apply to well-typed term, applying to ill-typed term is undefined
-- no context needed
simplifyType :: Term -> Term
simplifyType (TmAppl lst) =
  case map simplifyType lst of
    [x] -> x
    (x:y:xs) ->
      case x of
        TmLambda _ _ tm -> simplifyType $ TmAppl $ tmSubstTop y tm : xs
        _ -> TmAppl (x:y:xs)
    _ -> error "This should not happen"
simplifyType (TmProd name ty tm) =
  TmProd name (simplifyType ty) (simplifyType tm)
simplifyType tm = tm

typeof :: Context -> Term -> Either TypingError Term
typeof ctx tm = simplifyIndType <$> typeof' ctx tm

typeof' :: Context -> Term -> Either TypingError Term 
typeof' ctx (TmProd name t1 t2) = 
  let
    type1 = typeof' ctx t1 
    type2 = typeof' (addBinding ctx name (VarBind t1)) t2 
  in
    case (type1, type2) of
      (Left err1, _) -> Left err1
      (_, Left err2) -> Left err2
      (Right _, Right _) -> Right TmType

typeof' ctx (TmRel name index) =
  let 
    bind = getBinding ctx index 
  in
    case bind of
      Right (VarBind term) -> Right term
      Right (TmAbbBind term _) -> Right term
      Right IndTypeBind{} -> error "This should not happen" -- Right (TmIndType name [])  --emmmm.There is a small question.
      Right NameBind -> error "This should not happen" -- Left (TypingError t "NameBind is not a type.")
      _ -> error "This should not happen" -- Left (TypingError t "There is no such bind")
 
typeof' ctx (TmAppl ls) =
  let
    hd = head ls
  in
    case hd of
      TmLambda{} ->
        let
          ty = typeof' ctx hd 
        in
          case ty of
            Left er -> Left er
            Right tytm -> recCheck ctx (tail ls) tytm
      TmRel name index ->
        let
          bind = getBinding ctx index
        in
          case bind of
            Right (TmAbbBind ty _)-> recCheck ctx (tail ls) ty 
            Right (VarBind ty) -> recCheck ctx (tail ls) ty 
            Right (IndTypeBind _ ty _ _) -> error "This should not happen" -- recCheck ctx (tail ls) ty
            Right NameBind -> error "This should not happen" -- Left (TypingError hd "It is not a func")
            _ -> error "This should not happen" -- Left (TypingError hd "don't exist this func/inductiveType")
      TmProd{} ->  --  ??????????????
        let
          ty = recCheck ctx (tail ls) hd 
        in
          case ty of
            Left er -> Left er
            Right _ -> Right TmType
      _ -> Left (TypingError hd "this should't be applied")

typeof' ctx (TmLambda name t1 t2) =
  let 
    type1 = typeof' ctx t1 
  in
    case type1 of
      Left er -> Left er
      Right _ ->
        case typeof' (addBinding ctx name (VarBind t1)) t2 of
          Left er -> Left er
          Right tm2 -> Right (TmProd name t1 tm2) 
 
typeof' ctx (TmFix _ tm) =
  let 
    tmpty = typeof' ctx tm 
  in
    case tmpty of
      Left er -> Left er
      Right complexty -> 
        let 
          ty = simplifyType complexty
        in
          case ty of
            (TmProd _ t1 t2) ->
              if typeeq ctx (Right t1) (Right (tmShift (-1) t2))  
                then Right t1 
                else Left (TypingError tm "can't be fixed")
            _ -> Left (TypingError tm "can not be fixed")

typeof' ctx (TmLetIn name t1 t2 t3) =
  let 
    type1 = typeof' ctx t1 
  in
    case type1 of 
      Left er -> Left er
      Right _ ->
        if typeeq ctx (Right t1) (typeof' ctx t2 )
          then 
            typeof' ctx (betaReduction (TmAppl [TmLambda name t1 t3,t2])) 
          else 
            Left (TypingError t2 "type not match!") 

typeof' ctx TmType = Right TmTypeHigher

typeof' ctx t@(TmIndType name ls) =
  case getIndTypeType ctx name of 
    Left er -> Left (TypingError t "This is not a inductive type")
    Right (_,ty) -> recCheck ctx ls ty 

typeof' ctx t@(TmConstr name ls) =
  case getConstrType ctx name of
    Left er -> Left (TypingError t "This is not a constructor")
    Right ty -> recCheck ctx ls ty 


  
typeof' ctx t@(TmMatch n t1 name nameLs retType consLs) =
  let 
    tmpindty = typeof' ctx t1
  in
    case  tmpindty of
      Left er ->Left er
      Right complexindty ->
        let 
          indty = simplifyType complexindty
        in
          case indty of
            TmIndType indName ls ->
              if indName /= (head nameLs) 
                then 
                  Left (TypingError t "this inductive type not match the name")
                else
                  let
                    p = 
                      buildTy 
                        ctx 
                        (deleteN n ls) 
                        (deleteN n (tail nameLs)) 
                        retType 
                        name 
                        indty
                  in
                    let 
                      check = checkEquation ctx consLs ls p n
                    in 
                      case check of
                        Left er -> Left er
                        Right _ -> 
                          Right $
                            subsN 
                            ((length ls) - n + 1)
                            p 
                            ((deleteN n ls) ++ [t1])
deleteN n ls =
  if n == 0 
    then ls
  else 
    deleteN (n-1) (tail ls)
buildTy::Context->[Term]->[Name]->Term->Name->Term->Term
buildTy ctx _ [] t name ty = 
  if name == ""
    then t
    else TmLambda name ty t
buildTy ctx (tm:ls1) (name:ls2) t na ty= 
  let 
    Right tmTy = (typeof' ctx tm)
  in
    TmLambda name tmTy (buildTy ctx ls1 ls2 t na ty) 
--the order is equal to ls

checkEquation::Context->[Equation]->[Term]->Term->Int->Either TypingError Bool
checkEquation _ [] _ _ _ = Right True
checkEquation ctx ((Equation nameLs tm):eqLs) ls p n =
  let 
    Right (constrTy,constrTm) = getConstr ctx (head nameLs)
  in
    let 
      argumentTerm = subsN n constrTm ls
    in
      let
        argumentType = subsN n constrTy ls
      in 
        let 
          trueTy =
            addForall 
              argumentType 
              (subP 
                argumentTerm 
                argumentType 
                (tmShift (length nameLs -1 -n) p) 
                n)
        in
          let 
            realTy =typeof' ctx $ addLambda argumentTerm tm
              {- buildTy 
                ctx 
                (deleteN n ls) 
                (deleteN n (tail nameLs)) 
                tm 
                "" 
                TmType -}
          in
            if typeeq ctx realTy {-(trace (show trueTy)-} (Right trueTy) -- )
              then checkEquation ctx eqLs ls p n
              else 
                Left 
                (TypingError tm "the type of this term not match return type")


addLambda::Term->Term->Term
addLambda (TmLambda name t1 t2) t =
  TmLambda name t1 (addLambda t2 t)
addLambda _ t = t

addForall::Term->Term->Term
addForall (TmProd name t1 t2) t =
  TmProd name t1 (addForall t2 t)
addForall _ t = t

subsN::Int->Term->[Term]->Term
subsN n tm ls = 
  if n == 0
    then tm
    else subsN (n-1) (betaReduction (TmAppl [tm,(head ls)])) (tail ls) 
subP::Term->Term->Term->Int->Term
subP (TmLambda _ _ t1) (TmProd _ _ t2) p n = subP t1 t2 p n
subP t@(TmConstr name1 ls1) (TmIndType name2 ls2) p n =
  subsN
    ((length ls2) - n + 1) 
    p
    ((deleteN n ls2) ++ [t])
--subP (TmLambda _ _ )
   

typeeq :: Context -> Either TypingError Term -> Either TypingError Term -> Bool
typeeq ctx ty1 ty2 =
  case (ty1,ty2) of
    (Right tm1, Right tm2) ->
      let
        simpleType1 = fullBZIDReduction ctx  tm1
        simpleType2 = fullBZIDReduction ctx  tm2
      in
        namelessTypeEq simpleType1 simpleType2
          --This should consider that name will be ignored.
    _ -> False
namelessTypeEq::Term->Term->Bool
namelessTypeEq t1 t2 =
{-
  case (t1,t2) of
    (TmLambda name1 ty1 tm1,TmLambda name2 ty2 tm2) ->
      (namelessTypeEq ty1 ty2) && (namelessTypeEq tm1 tm2)
    (TmProd name1 ty1 tm1,TmProd name2 ty2 tm2) ->
      (namelessTypeEq ty1 ty2) && (namelessTypeEq tm1 tm2)
    (TmRel _ num1,TmRel _ num2) -> num1 == num2
    (TmFix num1 tm1,TmFix num2 tm2) ->
      (num1 == num2) && (namelessTypeEq tm1 tm2)
    (TmIndType name1 ls1,TmIndType name2 ls2) ->
      name1 == name2 
      && 
      namelessTypelsEq ls1 ls2
    (TmConstr name1 ls1,TmConstr name2 ls2) ->
      name1 == name2
      &&
      namelessTypelsEq ls1 ls2
    _ -> False  --without apply and var and letin and match
-}
    
  case t1 of
    TmLambda name1 ty1 tm1 ->
      case t2 of 
        TmLambda name2 ty2 tm2 ->
          (namelessTypeEq ty1 ty2) && (namelessTypeEq tm1 tm2)
        _ -> False
    TmProd name1 ty1 tm1 ->
      case t2 of
        TmProd name2 ty2 tm2 ->
          (namelessTypeEq ty1 ty2) && (namelessTypeEq tm1 tm2)
        _ -> False
    TmRel _ num1 ->
      case t2 of
        TmRel _ num2 -> num1 == num2
        _ -> False
    TmFix num1 tm1 ->
      case t2 of 
        TmFix num2 tm2 -> (num1 == num2) && (namelessTypeEq tm1 tm2)
        _ -> False
    TmIndType name1 ls1 ->
      case t2 of 
        TmIndType name2 ls2 -> 
          name1 == name2 
          && 
          namelessTypelsEq ls1 ls2
        _ -> False
    TmConstr name1 ls1 ->
      case t2 of
        TmConstr name2 ls2 ->
          name1 == name2
          &&
          namelessTypelsEq ls1 ls2
        _ -> False

    _ -> t1 == t2 --without apply and var and letin and match 
namelessTypelsEq::[Term]->[Term]->Bool
namelessTypelsEq ls1 ls2 =
  (length ls1) == (length ls2)
  && 
  (foldl
    (\c (tm1,tm2) ->
      if c
        then namelessTypeEq tm1 tm2
        else False)
    True
    (zip ls1 ls2))

recCheck :: Context -> [Term] -> Term -> Either TypingError Term
recCheck ctx ls complextyls =
  let 
    tyls = simplifyType complextyls
  in
    case ls of
      [] -> Right tyls
      x:xs -> 
        case tyls of
          TmProd _ ty _ -> 
            if typeeq ctx (typeof' ctx x) (Right ty) 
              then  recCheck ctx xs (betaReduction (TmAppl [tyls,x])) 
            else
              Left (TypingError x "not match")
          _ -> Left (TypingError x "too many params")

checkCommandType::Context->Command->Maybe TypingError
checkCommandType ctx (Ax name term) =
  let
    ty = typeof' ctx term
  in
    if typeeq ctx ty (Right TmType)
      then Nothing
      else Just (TypingError term "the type of it is not Type")
checkCommandType ctx (Def name ty tm) =
  let
    tyty = typeof' ctx ty
  in
    case tyty of
      Left er -> Just er
      Right _ -> 
        let
          tmty = typeof' ctx tm
        in
          if typeeq ctx tmty (Right ty)
            then Nothing
            else Just (TypingError tm "the type of it not match the given type")
checkCommandType ctx (Fix name term) = 
  let 
    ty = typeof' ctx term
  in
    case ty of
      Left er -> Just er
      Right _ -> Nothing
checkCommandType ctx (Ind name n t1 t2 ls) = 
  let
    newctx = 
      addBinding 
        ctx 
        name 
        (IndTypeBind
          n
          t1
          t2
          (listToConstr ls))
  in
    let
      ty = typeof' newctx (tmShift 1 t1) 
    in
      case ty of
        Left er -> Just er
        Right _ -> checkConstr newctx ls
listToConstr::[(Name, Term, Term)]->[Constructor]
listToConstr [] = []
listToConstr ((name,t1,t2):ls) = (Constructor name t1 t2):(listToConstr ls)

checkConstr::Context->[(Name, Term, Term)]->Maybe TypingError
checkConstr ctx [] = Nothing
checkConstr ctx ((name,t1,t2):ls) =
  let 
    ty = typeof' ctx (tmShift 1 t1) 
  in 
    case ty of
      Left er -> Just er
      Right _ -> checkConstr ctx ls
  
--fullBetaReduction :: Context -> Term ->Term
--fullBetaR eduction ctx tm = TmType
