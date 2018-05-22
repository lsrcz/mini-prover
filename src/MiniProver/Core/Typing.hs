module MiniProver.Core.Typing (
    simplifyType
  , typeof
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import MiniProver.Core.Context
import MiniProver.Core.Reduction
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
typeof ctx t = 
  case t of
    TmProd name t1 t2 ->
      let
        type1 = typeof ctx t1
      in
        case type1 of 
          Left er -> Left er
          Right t ->
            let
              type2 = typeof (addBinding ctx name (VarBind t1)) t2
            in
              case type2 of
                Left er -> Left er
                Right t -> Right TmType
    TmRel name index ->let bind = getBinding ctx index in
      case bind of
        Right (VarBind term) -> Right term
        Right (TmAbbBind term _) -> Right term
        Right (IndTypeBind _ _ _ _) -> Right (TmIndType name [])  --emmmm.There is a small question.
        Right NameBind -> Left (TypingError t "NameBind is not a type.")
        _ -> Left (TypingError t "There is no such bind")
    TmAppl ls ->
      let
        hd = head ls
      in
        case hd of
          TmLambda _ _ _ ->
            let
              ty = typeof ctx hd
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
                Right (IndTypeBind _ ty _ _) -> recCheck ctx (tail ls) ty
                Right NameBind -> Left (TypingError hd "It is not a func")
                _ -> Left (TypingError hd "don't exist this func/inductiveType")
          TmProd _ _ _ ->
            let
              ty = recCheck ctx (tail ls) hd
            in
              case ty of
                Left er -> Left er
                Right _ -> Right TmType
          _ -> Left (TypingError hd "this should't be applied")
    TmLambda name t1 t2 -> let type1 = typeof ctx t1 in
      case type1 of
        Left er -> Left er
        Right tm1 ->
          let
            type2 = typeof 
                    (addBinding 
                    ctx name 
                    (VarBind t1)) t2
          in
            case type2 of
              Left er -> Left er
              Right tm2 -> Right (TmProd name t1 tm2)
    TmFix _ tm -> let ty = typeof ctx tm in
      case ty of
        Right (TmProd _ t1 t2) ->
          if typeeq ctx (Right t1) (Right t2)
            then Right t1 
            else Left (TypingError tm "can't be fixed")
        Left er -> Left er
        _ -> Left (TypingError tm "can not be fixed")
    TmLetIn name t1 t2 t3 -> let type1 = typeof ctx t1 in
      case type1 of 
        Left er -> Left er
        Right ty ->
          if typeeq ctx (Right t1) (typeof ctx t2)
            then 
              typeof ctx (betaReduction (TmAppl ((TmLambda name t1 t3):t2:[])))
            else 
              Left (TypingError t2 "!")
    TmType -> Right TmTypeHigher
    TmTypeHigher -> error "typeof TmTypeHigher!!!!!"
    TmIndType name ls ->
      let
        indBind = getIndTypeType ctx name
      in
        case indBind of 
          Left er -> Left (TypingError t "This is not a inductive type")
          Right (_,ty) -> recCheck ctx ls ty
    TmConstr name ls ->
      let
        consBind = getConstrType ctx name
      in
        case consBind of
          Left er -> Left (TypingError t "This is not a constructor")
          Right ty -> recCheck ctx ls ty
    TmMatch tm nameLs retTy consLs ->
      let
        matchTy = typeof ctx tm
      in
        case matchTy of
          Left er -> Left er
          Right (TmIndType name indLs) -> 
            if (length indLs) /= (length nameLs - 1)
              then
                Left $
                  TypingError tm 
                    "The length of term list is not equal to the length of name list"
            else
              if
                (name /= head nameLs)
              then
                Left $
                TypingError tm 
                  "The name of this inductive type is not matched"
            else
              let
                Right (_, _, _, realConsLs) = getIndType ctx name
              in
                if (length realConsLs)/=(length consLs)
                  then
                    Left $
                      TypingError t
                        "the number of constructor is not matched."
              else
                let
                  newRet = snd $
                    foldl
                      (\(n,acc) tm1 -> (n - 1, tmSubstInsideN n tm1 acc))
                      (length indLs, retTy) 
                      indLs
                in
                  let
                    retTyTy = typeof ctx newRet
                  in
                    case retTyTy of
                      Left er -> Left er
                      Right _ ->
                        let
                          checkEquation eqList =
                            case eqList of
                              [] -> Right newRet
                              (Equation consNameLs consTerm):restList -> 
                                let consName = head consNameLs in
                                  if
                                    foldl 
                                      (\b (Constructor n _ _) -> 
                                        if n==consName then True else b) 
                                      True 
                                      realConsLs
                                    then 
                                      let constr = getConstrType ctx consName in
                                        case constr of
                                          Left _ -> Left 
                                              (TypingError t 
                                              "This is not a constructor")
                                          Right consType ->
                                            let
                                              checkConst ty=
                                                case ty of
                                                  TmProd _ _ nty -> 1+(checkConst nty)
                                                  _ -> 0
                                            in
                                              if (checkConst consType) /=
                                                (length (tail consNameLs))
                                              then
                                                Left $
                                                  TypingError
                                                  t $
                                                  "the number of params don't match the" ++ 
                                                  "type of this constructor"
                                              else
                                                let
                                                  termType =
                                                    typeof 
                                                    (fst $ foldl
                                                      (\(c,ty) t-> 
                                                        case ty of
                                                          TmProd _ y nty ->
                                                            ((addBinding c t (VarBind y))
                                                            ,nty))
                                                      (ctx,consType)
                                                      (tail consNameLs))
                                                    consTerm
                                                in
                                                  if typeeq ctx termType (Right newRet)
                                                    then checkEquation restList
                                                    else
                                                      Left $
                                                        TypingError
                                                        consTerm $
                                                        "this type is not" ++
                                                        "equal to return type"
                                    else 
                                      Left $
                                        TypingError t $
                                        "This constructor is" ++
                                        "not match the inductive type"
                        in 
                          checkEquation consLs
          Right _ -> Left (TypingError tm "This is not a inductive type")
typeeq :: Context->Either TypingError Term -> Either TypingError Term ->Bool
typeeq ctx ty1 ty2 =
  case ty1 of
    Left er -> False
    Right tm1 -> case ty2 of
      Left er -> False
      Right tm2 -> let simpleType1 = fullBZIDReduction ctx 0 tm1 in
        let simpleType2 = fullBZIDReduction ctx 0 tm2 in
          simpleType1 == simpleType2  --This should consider that name will be ignored.
recCheck ::Context->[Term]->Term->Either TypingError Term
recCheck ctx ls tyls =
  case ls of
    [] -> Right tyls
    x:xs -> case tyls of
      TmProd name ty tm -> if typeeq ctx (typeof ctx x) (Right ty) then
          recCheck ctx xs (betaReduction (TmAppl (tyls:x:[])))
        else
          Left (TypingError x "not match")
      _ -> Left (TypingError x "too many params")

--fullBetaReduction :: Context -> Term ->Term
--fullBetaR eduction ctx tm = TmType
