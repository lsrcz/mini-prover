module MiniProver.Core.Typing (
    TypingError(..)
  , simplifyType
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
typeof ctx t = typeof' ctx t 0

typeof' :: Context -> Term -> Int -> Either TypingError Term 
typeof' ctx t n = 
  case t of
    TmProd name t1 t2 ->
      let
        type1 = typeof' ctx t1 n
        type2 = typeof' (addBinding ctx name (VarBind t1)) t2 (n+1)
      in
        case (type1, type2) of
          (Left err1, _) -> Left err1
          (_, Left err2) -> Left err2
          (Right _, Right _) -> Right TmType
    TmRel name index -> let bind = getBinding ctx index in
      case bind of
        Right (VarBind term) -> Right term
        Right (TmAbbBind term _) -> Right term
        Right IndTypeBind{} -> error "This should not happen" -- Right (TmIndType name [])  --emmmm.There is a small question.
        Right NameBind -> error "This should not happen" -- Left (TypingError t "NameBind is not a type.")
        _ -> error "This should not happen" -- Left (TypingError t "There is no such bind")
    TmAppl ls ->
      let
        hd = head ls
      in
        case hd of
          TmLambda{} ->
            let
              ty = typeof' ctx hd n
            in
              case ty of
                Left er -> Left er
                Right tytm -> recCheck ctx (tail ls) tytm n
          TmRel name index ->
            let
              bind = getBinding ctx index
            in
              case bind of
                Right (TmAbbBind ty _)-> recCheck ctx (tail ls) ty n
                Right (VarBind ty) -> recCheck ctx (tail ls) ty n
                Right (IndTypeBind _ ty _ _) -> error "This should not happen" -- recCheck ctx (tail ls) ty
                Right NameBind -> error "This should not happen" Left (TypingError hd "It is not a func")
                _ -> error "This should not happen" Left (TypingError hd "don't exist this func/inductiveType")
          TmProd{} ->
            let
              ty = recCheck ctx (tail ls) hd n
            in
              case ty of
                Left er -> Left er
                Right _ -> Right TmType
          _ -> Left (TypingError hd "this should't be applied")
    TmLambda name t1 t2 -> let type1 = typeof' ctx t1 n in
      case type1 of
        Left er -> Left er
        Right _ ->
          case typeof' (addBinding ctx name (VarBind t1)) t2 (n+1) of
            Left er -> Left er
            Right tm2 -> Right (TmProd name t1 tm2)
    TmFix _ tm -> let ty = typeof' ctx tm n in
      case ty of
        Right (TmProd _ t1 t2) ->
          if typeeq ctx (Right t1) (Right t2) n (n+1)
            then Right t1 
            else Left (TypingError tm "can't be fixed")
        Left er -> Left er
        _ -> Left (TypingError tm "can not be fixed")
    TmLetIn name t1 t2 t3 -> let type1 = typeof' ctx t1 n in
      case type1 of 
        Left er -> Left er
        Right _ ->
          if typeeq ctx (Right t1) (typeof' ctx t2 n) n n
            then 
              typeof' ctx (betaReduction (TmAppl [TmLambda name t1 t3,t2])) n
            else 
              Left (TypingError t2 "!")
    TmType -> Right TmTypeHigher
    TmTypeHigher -> error "typeof TmTypeHigher!!!!!"
    TmIndType name ls ->
      case getIndTypeType ctx name of 
        Left er -> Left (TypingError t "This is not a inductive type")
        Right (_,ty) -> recCheck ctx ls ty n
    TmConstr name ls ->
      case getConstrType ctx name of
        Left er -> Left (TypingError t "This is not a constructor")
        Right ty -> recCheck ctx ls ty n
    TmMatch tm nameLs retTy consLs ->
        case fullBZIDReduction ctx n <$> typeof' ctx tm n of
          Left er -> Left er
          Right (TmIndType name indLs)
            | length indLs /= length nameLs - 1 ->
                Left $
                  TypingError tm 
                    "The length of term list is not equal to the length of name list"
            | name /= head nameLs ->
                Left $
                TypingError tm 
                  "The name of this inductive type is not matched"
            | otherwise ->
              let
                Right (_, _, _, realConsLs) = getIndType ctx name
              in
                if length realConsLs /= length consLs
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
                        case typeof' ctx newRet (n+length indLs) of
                          Left er -> Left er
                          Right _ ->
                            let
                              checkEquation eqList =
                                case eqList of
                                  [] -> Right newRet
                                  Equation consNameLs consTerm:restList -> 
                                    let consName = head consNameLs in
                                      if
                                        foldl 
                                          (\b (Constructor n _ _) -> n==consName || b) 
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
                                                      TmProd _ _ nty -> 1 + checkConst nty
                                                      _ -> 0
                                                in
                                                  if checkConst consType /=
                                                    length (tail consNameLs)
                                                  then
                                                    Left $
                                                      TypingError
                                                      t $
                                                      "the number of params don't match the" ++ 
                                                      "type of this constructor"
                                                  else
                                                    let
                                                      termType =
                                                        typeof'
                                                        (fst $ foldl
                                                          (\(c,ty) t-> 
                                                            case ty of
                                                              TmProd _ y nty ->
                                                                (addBinding c t (VarBind y)
                                                                ,nty))
                                                          (ctx,consType)
                                                          (tail consNameLs))
                                                        consTerm
                                                        (n+length (tail consNameLs))
                                                    in
                                                      if typeeq ctx termType (Right newRet) n n
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
          Right tmm -> trace (show tmm) $ Left (TypingError tm "This is not a inductive type")

typeeq :: Context -> Either TypingError Term -> Either TypingError Term -> Int -> Int -> Bool
typeeq ctx ty1 ty2 n m =
  case (ty1,ty2) of
    (Right tm1, Right tm2) ->
      let
        simpleType1 = fullBZIDReduction ctx n tm1
        simpleType2 = fullBZIDReduction ctx m tm2
      in
        simpleType1 == simpleType2  --This should consider that name will be ignored.
    _ -> False

recCheck :: Context -> [Term] -> Term -> Int -> Either TypingError Term
recCheck ctx ls tyls n =
  case ls of
    [] -> Right tyls
    x:xs -> case tyls of
      TmProd _ ty _ -> if typeeq ctx (typeof' ctx x n) (Right ty) n n then
          recCheck ctx xs (betaReduction (TmAppl [tyls,x])) n
        else
          Left (TypingError x "not match")
      _ -> Left (TypingError x "too many params")

--fullBetaReduction :: Context -> Term ->Term
--fullBetaR eduction ctx tm = TmType
