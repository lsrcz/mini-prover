module MiniProver.Core.Typing (
    TypingError(..)
  , simplifyType
  , typeof
  , checkCommandType
  , typeeq
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

typeof' ctx (TmRel _ index) =
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
  case typeof' ctx (head ls) of
    Left er -> Left er
    Right ty -> recCheck ctx (tail ls) ty
      
        
 -- case (fullBZIDReduction ctx (typeof' ctx (head ls))) of
    

{-

typeof' ctx (TmAppl ls) = let hd = head ls in
  case (fullBZIDReduction ctx hd) of
    TmLambda{} ->
      case typeof' ctx hd  of
        Left er -> Left er
        Right tytm -> recCheck ctx (tail ls) tytm
    TmRel _ index ->
      case getBinding ctx index of
        Right (TmAbbBind ty _)-> recCheck ctx (tail ls) ty 
        Right (VarBind ty) -> recCheck ctx (tail ls) ty 
        Right (IndTypeBind _ ty _ _) -> error "This should not happen" -- recCheck ctx (tail ls) ty
        Right NameBind -> error "This should not happen" -- Left (TypingError hd "It is not a func")
        _ -> error "This should not happen" -- Left (TypingError hd "don't exist this func/inductiveType")
    TmProd{} ->  --  ??????????????
      -- typeof' ctx (recCheck ctx (tail ls) hd)
      case (recCheck ctx (tail ls) hd) of
        Left er -> Left er
        (Right ret) -> typeof' ctx ret 
    {-  case recCheck ctx (tail ls) hd  of
        Left er -> Left er
        Right _ -> Right TmType -}
    _ -> Left (TypingError hd "this should't be applied")
-}



typeof' ctx (TmLambda name t1 t2) =
  case typeof' ctx t1  of
    Left er -> Left er
    Right _ ->
      case typeof' (addBinding ctx name (VarBind t1)) t2 of
        Left er -> Left er
        Right tm2 -> Right (TmProd name t1 tm2) 
 
typeof' ctx (TmFix _ tm) =
  case typeof' ctx tm of
    Left er -> Left er
    Right complexty -> 
      case fullBZIDReduction ctx complexty of
        (TmProd _ t1 t2) ->
          if typeeq ctx (Right t1) (Right (tmShift (-1) t2))  
            then Right t1 
            else Left (TypingError tm "can't be fixed")
        _ -> Left (TypingError tm "can not be fixed")

typeof' ctx (TmLetIn name t1 t2 t3) =
  case typeof' ctx t1  of 
    Left er -> Left er
    Right _ ->
      if typeeq ctx (Right t1) (typeof' ctx t2 )
        then 
          typeof' ctx (betaReduction (TmAppl [TmLambda name t1 t3,t2])) 
        else 
          Left (TypingError t2 "type not match!") 

typeof' _ TmType = Right TmTypeHigher

typeof' ctx t@(TmIndType name ls) =
  case getIndTypeType ctx name of 
    Left er -> Left (TypingError t "This is not a inductive type")
    Right (_,ty) -> recCheck ctx ls ty 

typeof' ctx t@(TmConstr name ls) =
  case getConstrType ctx name of
    Left er -> Left (TypingError t "This is not a constructor")
    Right ty -> recCheck ctx ls ty 


  
typeof' ctx t@(TmMatch n t1 name nameLs retType consLs) =
    case typeof' ctx t1 of
      Left er ->Left er
      Right complexindty ->
        let 
          indty = fullBZIDReduction ctx complexindty
        in
          case indty of
            TmIndType indName ls
              | indName /= head nameLs ->
                  Left (TypingError t "this inductive type not match the name")
              | otherwise ->
                  let
                    p = 
                      buildTy 
                        ctx 
                        (deleteN n ls) 
                        (deleteN n (tail nameLs)) 
                        retType 
                        name 
                        indty
                    check = checkEquation ctx consLs ls p n
                  in 
                    case check of
                      Left er -> Left er
                      Right _ -> 
                        Right $
                          subsN 
                          (length ls - n + 1)
                          p 
                          (deleteN n ls ++ [t1])

deleteN :: Int -> [a] -> [a]
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
buildTy ctx (tm:ls1) (name:ls2) t na ty = 
  let 
    Right tmTy = typeof' ctx tm
  in
    TmLambda name tmTy (buildTy ctx ls1 ls2 t na ty) 
--the order is equal to ls

checkEquation::Context->[Equation]->[Term]->Term->Int->Either TypingError Bool
checkEquation _ [] _ _ _ = Right True
checkEquation ctx (Equation nameLs tm:eqLs) ls p n =
  let 
    Right (constrTy,constrTm) = getConstr ctx (head nameLs)
    argumentTerm = subsN n constrTm ls
    argumentType = subsN n constrTy ls 
    trueTy =
      addForall 
        argumentType 
        (subP 
          argumentTerm 
          argumentType 
          (tmShift (length nameLs -1 -n) p) 
          n)
    realTy = typeof' ctx $ addLambda argumentTerm tm
  in
    if typeeq ctx realTy  (Right trueTy)
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
    else subsN (n-1) (betaReduction (TmAppl [tm,head ls])) (tail ls) 
subP::Term->Term->Term->Int->Term
subP (TmLambda _ _ t1) (TmProd _ _ t2) p n = subP t1 t2 p n
subP t@(TmConstr name1 ls1) (TmIndType name2 ls2) p n =
  subsN
    (length ls2 - n + 1) 
    p
    (deleteN n ls2 ++ [t])
--subP (TmLambda _ _ )
   

typeeq :: Context -> Either TypingError Term -> Either TypingError Term -> Bool
typeeq ctx ty1 ty2 =
  case (ty1,ty2) of
    (Right tm1, Right tm2) ->
      let
        simpleType1 = fullBZIDReduction ctx  tm1
        simpleType2 = fullBZIDReduction ctx  tm2
      in
        termEqNameless simpleType1 simpleType2
          --This should consider that name will be ignored.
    _ -> False

recCheck :: Context -> [Term] -> Term -> Either TypingError Term
recCheck ctx ls complextyls =
  let 
    tyls = fullBZIDReduction ctx complextyls
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
checkCommandType ctx (Ax _ term) =
  if typeeq ctx (typeof' ctx term) (Right TmType)
    then Nothing
    else Just (TypingError term "the type of it is not Type")
checkCommandType ctx (Def _ ty tm) =
  case typeof' ctx ty of
    Left er -> Just er
    Right _ -> 
      let
        tmty = typeof' ctx tm
      in
        if typeeq ctx  tmty (Right ty)
          then Nothing
          else Just (TypingError tm "the type of it not match the given type")
checkCommandType ctx (Fix name term) = 
  case typeof' ctx term of
    Left er -> Just er
    Right _ -> Nothing
checkCommandType ctx (Ind name n t1 t2 ls) = 
  let
    newctx = 
      addBinding ctx name 
        (IndTypeBind n t1 t2 (listToConstr ls))
  in
    case typeof' newctx (tmShift 1 t1)  of
      Left er -> Just er
      Right _ -> checkConstr newctx ls
checkCommandType ctx (Theorem _ term) =
  if typeeq ctx (typeof' ctx term) (Right TmType)
    then Nothing
    else Just (TypingError term "the type of it is not Type")

listToConstr::[(Name, Term, Term)]->[Constructor]
listToConstr [] = []
listToConstr ((name,t1,t2):ls) = Constructor name t1 t2:listToConstr ls

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
