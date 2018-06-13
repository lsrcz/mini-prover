{-# LANGUAGE LambdaCase #-}
module MiniProver.TopLevel.Command (
    addEnvCommand
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Rename
import MiniProver.Core.Subst
import MiniProver.Core.Typing
import MiniProver.Core.SimplifyIndType
import Debug.Trace
import Data.Maybe
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST


addEnvCommand :: Context -> Command -> Context
addEnvCommand ctx cmd = addEnvCmd ctx (simplifyIndCmd cmd)

addEnvCmd :: Context -> Command -> Context
addEnvCmd ctx (Ax nm ty) = 
    addBinding ctx nm $ TmAbbBind ty Nothing
addEnvCmd ctx (Def nm ty tm) = 
    addBinding ctx nm $ TmAbbBind ty $ Just tm
addEnvCmd ctx (Fix nm tm) = 
    case tm of 
      TmFix _ (TmLambda _ ty _) -> 
        addBinding ctx nm $ TmAbbBind ty $ Just tm
      _ -> error "This should not happen"
addEnvCmd ctx (Ind nm' d' ty' tm' lst') = 
    let (Ind nm d ty tm lst) = renameInd ctx $ Ind nm' d' ty' tm' lst' in
        let ctx' = addBinding ctx nm $ IndTypeBind d ty tm $
                map (\case (a, b, c) -> (Constructor a b c)) lst in
            --trace ("hello2") $
            let indterm = buildIndTermOuterParam ctx' nm d (ty, tm) lst in
                case indterm of
                    Nothing -> ctx
                    Just term -> 
                        --trace ("hello3 "++prettyShowAST term) $
                        let newty = typeof ctx' term in
                            --trace ("hello4 "++show newty) $
                            case newty of
                                Right tyterm ->
                                    --trace ("hello5") $
                                    addBinding ctx' (nm++"_rect") $ 
                                        TmAbbBind (renameTerm ctx' tyterm) $ 
                                        Just $ renameTerm ctx' term
                                Left str -> 
                                        error "This should not happen"


buildIndTermOuterParam :: Context -> Name -> Int -> (Term, Term) -> [(Name, Term, Term)] -> Maybe Term
buildIndTermOuterParam ctx nm d (ty, tm) lst 
    | d == 0 = 
        buildIndTermOuterProp ctx nm (ty, tm) lst
    | otherwise = 
        --trace ("here") $
        case (ty, tm) of
            (TmProd nm1 ty1 inty, TmLambda nm1' ty1' intm) ->
                case buildIndTermOuterParam ctx nm (d - 1) (inty, intm) lst of
                    Nothing -> Nothing
                    Just term -> Just $ TmLambda nm1' ty1' term


buildIndTermOuterProp :: Context -> Name -> (Term, Term) -> [(Name, Term, Term)] -> Maybe Term
buildIndTermOuterProp ctx nm (ty, tm) lst = 
    case buildIndTermOuterFs ctx nm lst 1 False of
        Nothing -> Nothing
        Just term -> 
            let ty' = buildIndPropType ctx nm tm in
                Just $ TmLambda ".P" ty' term


buildIndTermOuterFs :: Context -> Name -> [(Name, Term, Term)] -> Int -> Bool -> Maybe Term
buildIndTermOuterFs ctx nm [] d isfix = 
    Just $ buildIndTermInnerParam ctx nm isfix 
buildIndTermOuterFs ctx nm ((nm1, ty1, tm1):res) d isfix =
    let (ftype, isfix') = buildIndTermOuterSingleF ctx nm (nm1, ty1, tm1) d in
        let tm' = buildIndTermOuterFs ctx nm res (d + 1) (isfix || isfix') in
            if (isNothing ftype) || (isNothing tm') then 
                Nothing
            else 
                Just $ TmLambda ".f" (fromJust ftype) (fromJust tm')
                

buildIndTermOuterSingleF :: Context -> Name -> (Name, Term, Term) -> Int -> (Maybe Term, Bool)
buildIndTermOuterSingleF ctx indnm (nm, ty, tm) d =
    let newty = tmShift d $ stripExpParam ctx indnm ty in
        let newtm = tmShift d $ stripExpParam ctx indnm tm in
           buildIndConstrF ctx indnm (newty, newtm) d  


buildIndTermInnerParam :: Context -> Name -> Bool -> Term
buildIndTermInnerParam ctx nm True = 
    case getIndType ctx nm of
        Right (d, ty, tm, lst) ->
            let impd = getArgs $ stripExpParam ctx nm ty in
                let fixterm = buildIndFixF ctx nm impd in
                    TmFix (1 + impd) fixterm
        _ -> error "This should not happen"
buildIndTermInnerParam ctx nm False = 
    let x = getIndType ctx nm in
        case x of
            Right (d, ty, tm, conlst) ->
                let len = length conlst in
                    let newtm = tmShift (1 + len) $ stripExpParam ctx nm tm in
                        buildPreMatchTerm ctx nm len newtm
            _ -> error "This should not happen"
    

buildIndMatch :: Context -> Name -> Int -> Term
buildIndMatch ctx nm pd = 
    let x = getIndType ctx nm in
        case x of
            Right (d, ty, tm, conlst) ->
                let imparglst = getArgByFirstLetterDot $ stripExpParam ctx nm tm in
                    let matchlst = nm:(repeatList "_" d)++imparglst in
                        let retlst = TmAppl $ (TmRel ".P" (1 + pd + length imparglst)):
                                (buildMatchRetList imparglst)++[(TmRel "." 0)] in
                            let eqlst = buildIndMatchEqList ctx nm (pd - 1) in
                                TmMatch d (TmRel "." 0) "." matchlst retlst eqlst
            _ -> error "This should not happen"


buildIndMatchEq :: Context -> Name -> Constructor -> Int -> Equation
buildIndMatchEq ctx nm (Constructor nm1 ty1 tm1) fd = 
    --trace ("Constructor is "++nm1) $
    --trace ("tm1 is "++show tm1) $
    let newtm = stripExpParam ctx nm tm1 in
        --trace ("newtm is "++show newtm) $
        let x = getIndType ctx nm in
            case x of
                Right (d, ty, tm, _) -> 
                    let arglst = getArgByFirstLetterDot newtm in
                        let eqstr = nm1:(repeatList "_" d)++arglst in
                            if arglst == [] then 
                                Equation eqstr (TmRel ".f" fd)
                            else 
                                let bigfd = 1 + length arglst + getArgs (stripExpParam ctx nm tm) in
                                    let applst = buildIndMatchEqApp ctx nm newtm bigfd [] $ getArgs newtm - 1 in
                                        Equation eqstr $ TmAppl $ (TmRel ".f" $ fd + length arglst):applst
                _ -> error "This should not happen"


buildIndMatchEqApp :: Context -> Name -> Term -> Int -> [(String, Int)] -> Int -> [Term]
buildIndMatchEqApp ctx nm (TmConstr _ _) bigfd lst curid = []
buildIndMatchEqApp ctx nm (TmLambda nm1 ty tm) bigfd lst curid =
    --trace ("before head 1 "++(show $ length nm1)) $
    let dotname = "."++[head nm1] in
        --trace ("after head 1") $
        let newlst = (dotname, curid):lst in
            let nxt = buildIndMatchEqApp ctx nm tm bigfd newlst (curid - 1) in
                case ty of
                    TmRel _ _ -> 
                        (TmRel dotname curid):nxt
                    TmIndType nm2 tmlst ->
                        if nm /= nm2 then
                            (TmRel dotname curid):nxt
                        else 
                            --trace ("tmlist "++show tmlst) $
                            let rawlst = drop (getIndTypeInt ctx nm) tmlst in
                                --trace ("raw list is "++show rawlst) $
                                --trace ("lst is "++show lst) $
                                --trace ("bigfd is "++show bigfd) $
                                --trace ("dotname is "++dotname) $
                                --trace ("nxt is "++show nxt) $
                                let applst = map (\case (TmRel _ id) -> searchAndReplace ctx nm lst id bigfd) rawlst in
                                    (TmRel dotname curid): 
                                    (TmAppl $ (TmRel ".F" bigfd):
                                        applst++[(TmRel dotname 0)]):nxt 
                    TmAppl _ ->
                        (TmRel dotname curid):nxt
                    _ -> error "This should not happen"


searchAndReplace :: Context -> Name -> [(String, Int)] -> Int -> Int -> Term
searchAndReplace ctx nm lst id bigfd 
    | length lst > id =
        --trace ("before head 2: list length is "++(show $ length lst)++" drop number is "++(show id)) $
        let (nm, d) = head (drop id lst) in
            --trace ("after head 2") $
            TmRel nm d
    | otherwise =
        let 
            exp = getIndTypeInt ctx nm
            conslen = getIndTypeConstrlstLen ctx nm
            k = 1 - (length lst - id + exp) 
            index = k + exp + 1 + bigfd + conslen
        in
            TmRel "?" index


getIndTypeConstrlstLen :: Context -> Name -> Int
getIndTypeConstrlstLen ctx nm =
    let con = getIndTypeConstrlst ctx nm in
        case con of
            Right conlst -> length conlst
            _ -> error "This should not happen"


buildIndMatchEqList :: Context -> Name -> Int -> [Equation]
buildIndMatchEqList ctx nm fd =
    case getIndTypeConstrlst ctx nm of
        Right conlst ->
            buildIndMatchEqs ctx nm fd conlst
        _ -> error "This should not happen"


buildIndMatchEqs :: Context -> Name -> Int -> [Constructor] -> [Equation]
buildIndMatchEqs ctx nm fd [] = []
buildIndMatchEqs ctx nm fd (x:y) = 
    (buildIndMatchEq ctx nm x fd):(buildIndMatchEqs ctx nm (fd - 1) y)


buildMatchRetList :: [String] -> [Term]
buildMatchRetList lst =
    case lst of
        [] -> []
        x:y -> (TmRel x $ length lst):(buildMatchRetList y)


repeatList :: a -> Int -> [a]
repeatList x d 
    | d == 0 = [] 
    | otherwise = x:(repeatList x (d - 1))


getArgByFirstLetterDot :: Term -> [String]
getArgByFirstLetterDot term =
    case term of
        TmProd nm _ tm1 -> 
            --trace ("here is prod and "++show nm)$
            ("."++[head nm]):(getArgByFirstLetterDot tm1)
        TmLambda nm _ tm1 ->
            --trace ("here is lambda and "++show nm)$
            ("."++[head nm]):(getArgByFirstLetterDot tm1)
        _ -> []


buildIndFixF :: Context -> Name -> Int -> Term 
buildIndFixF ctx nm d =
    let x = getIndType ctx nm in
        case x of
            Right (d, ty, tm, conlst) -> 
                let len = length conlst in
                    let newtm = tmShift (1 + len) $ stripExpParam ctx nm tm in
                        let ftype = buildIndFixFType ctx nm newtm len in
                            let fterm = buildPreMatchTerm ctx nm (len + 1) $ tmShift 1 newtm in
                                TmLambda ".F" ftype fterm
            _ -> error "This should not happen"


buildPreMatchTerm :: Context -> Name -> Int -> Term -> Term
buildPreMatchTerm ctx nm pd (TmLambda nm1 ty1 tm2) = 
    let term = buildPreMatchTerm ctx nm (pd + 1) tm2 in
        TmLambda nm1 ty1 term
buildPreMatchTerm ctx nm pd (TmIndType nm1 lst) =
    let term = buildIndMatch ctx nm (pd + 1) in
        TmLambda "." (TmIndType nm1 lst) term


buildIndFixFType :: Context -> Name -> Term -> Int -> Term
buildIndFixFType ctx nm (TmLambda nm1 ty1 tm2) d =
    let term = buildIndFixFType ctx nm tm2 (d + 1) in
        TmProd nm1 ty1 term
buildIndFixFType ctx nm (TmIndType nm1 lst) d =
    TmProd "." (TmIndType nm1 lst) $
    TmAppl $ (TmRel ".P" (d + 1)):(listShift 1 $ 
    drop (getIndTypeInt ctx nm) lst)++[(TmRel "." 0)]


buildIndConstrF :: Context -> Name -> (Term, Term) -> Int -> (Maybe Term, Bool)
buildIndConstrF ctx nm (ty, tm) d =
    case (ty, tm) of
        (TmProd nm1 ty1 tm1, TmLambda nm2 ty2 tm2) ->
            case ty1 of
                TmRel nm' index -> 
                    let inner = buildIndConstrF ctx nm (tm1, tm2) (d + 1) in
                        case inner of
                            (Nothing, _) -> (Nothing, False)
                            (Just term, isfix) -> (Just $ TmProd nm2 ty2 term, isfix)
                TmIndType nm' lst -> 
                    if nm' /= nm then
                        let inner = buildIndConstrF ctx nm (tm1, tm2) (d + 1) in
                            case inner of
                                (Nothing, _) -> (Nothing, False)
                                (Just term, isfix) -> (Just $ TmProd nm2 ty2 term, isfix)
                    else
                        let inner = buildIndConstrF ctx nm (tmShift 1 tm1, tmShift 1 tm2) (d + 2) in
                            case inner of
                                (Nothing, _) -> (Nothing, False) 
                                (Just term, _) -> 
                                    let cnt = getIndTypeInt ctx nm in
                                        let pty = TmAppl $ (TmRel ".P" d):(listShift 1 $ drop cnt lst)++[(TmRel nm2 0)]  in
                                            (Just $ TmProd nm2 ty2 $ TmProd "_" pty term, True)
                TmAppl applst -> 
                    let inner = buildIndConstrF ctx nm (tm1, tm2) (d + 1) in
                        case inner of
                            (Nothing, _) -> (Nothing, False)
                            (Just term, isfix) -> (Just $ TmProd nm2 ty2 term, isfix)
                _ -> (Nothing, False)
        (TmIndType nm1 lst1, TmConstr nm2 lst2) ->
            let cnt = getIndTypeInt ctx nm in
                (Just $ TmAppl $ (TmRel ".P" (d - 1)):(drop cnt lst1)++[(tm)], False) 
        _ -> error "This should not happen"


stripExpParam :: Context -> Name -> Term -> Term
stripExpParam ctx nm tm = stripExpParamForDTimes tm $ getIndTypeInt ctx nm 


getIndTypeInt :: Context -> Name -> Int
getIndTypeInt ctx nm =
    case getIndType ctx nm of
        Right (d, _, _, _) -> d
        _ -> error "This should not happen"


stripExpParamForDTimes :: Term -> Int -> Term
stripExpParamForDTimes tm d 
    | d == 0 = tm
    | otherwise = 
        case tm of
            TmProd _ _ tm' -> stripExpParamForDTimes tm' (d - 1)
            TmLambda _ _ tm' -> stripExpParamForDTimes tm' (d - 1)
            _ -> error "This should not happen"


buildIndPropType :: Context -> Name -> Term -> Term
buildIndPropType ctx nm tm =
    case tm of
        TmLambda nm1 ty1 tm1 ->
            TmProd nm1 ty1 $ buildIndPropType ctx nm tm1
        TmIndType nm1 tmlst ->
            TmProd "_" tm TmType
        _ -> error "This should not happen" 
     

listShift :: Int -> [Term] -> [Term]
listShift d lst = map (\x -> tmShift d x) lst


getArgs :: Term -> Int
getArgs tm =
    case tm of
        TmLambda _ _ tm' -> 1 + getArgs tm'
        TmProd _ _ tm' -> 1 + getArgs tm'
        _ -> 0
