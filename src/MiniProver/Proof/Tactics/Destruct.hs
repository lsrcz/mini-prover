{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.Destruct (
    handleDestruct
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Proof.Tactics.Intro
import MiniProver.Core.Typing
import MiniProver.Core.Context
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import MiniProver.Core.Reduction
import MiniProver.Core.Syntax
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST
import Data.Either (fromRight)
import Debug.Trace


multipleItems :: Int -> a -> [a]
multipleItems d x 
    | d == 0 = []
    | otherwise = x:multipleItems (d - 1) x


handleDestruct :: Goal -> Tactic -> Either TacticError Result
handleDestruct g@(Goal d ctx ty) tac@(Destruct tm) = 
    let ty' = typeof ctx tm in
        case ty' of 
            Right (TmIndType nm inty) ->
                let 
                    nmlst = buildMatchNameList ctx nm 
                    ups = getImpParams (tail nmlst) + 2
                    substlst = buildSubstList ctx (ups - 1) tm (TmIndType nm inty)
                    (newctx, returntype, apps) = buildMatchReturnType ups (Goal d ctx ty) substlst tm 
                in
                    --trace ("Apps "++show apps) $
                    let typeofbranchP = buildTermPBeforeBranch returntype (ups - 1) in
                        --trace ("P is "++show typeofbranchP) $
                        let 
                            len = length apps
                            branches = buildTermInConstrs d len newctx nm typeofbranchP inty 
                            subgoals = map (\case (a, _, _) -> a) branches
                            resultcases = map (\case (_, b, c) -> (b, c)) branches
                            resultf = buildResultFunc len ctx (getIndTypeExpInt ctx nm) 
                                tm nmlst returntype resultcases apps
                        in
                            --trace (show branches) $ dummyreturn
                            trace (prettyShowAST $ resultf $ multipleItems (length subgoals) TmType) $
                            Right $ Result subgoals (checkResult g tac . resultf)
            Right _ ->
                Left $ TacticError "Not an inductive product"
            Left _ ->
                Left $ TacticError "TypingError"



buildResultEqs :: Int -> [([Name], Term)] -> [Term] -> [Equation]
buildResultEqs len [] [] = []
buildResultEqs len ((nmlst, tm1):a) (tm2:b) =
    let 
        nxt = buildResultEqs len a b 
        cur = Equation nmlst $ substAfterDLambda len tm1 tm2
    in 
        cur:nxt 


substAfterDLambda :: Int -> Term -> Term -> Term
substAfterDLambda d tm1 tm2 
    | d == 0 = tm2
    | otherwise =
        case tm1 of
            TmLambda nm ty tm ->
                TmLambda nm ty $ substAfterDLambda (d - 1) tm tm2
            _ -> error "This should not happen"
    

buildResultFunc :: Int -> Context -> Int -> Term -> [Name] -> Term -> [([Name], Term)] -> [Term]
    -> [Term] -> Term
buildResultFunc len ctx d tm nmlst ty cases [] goals =
    renameTerm ctx $ TmMatch d tm ".0" nmlst ty $ buildResultEqs len cases goals
buildResultFunc len ctx d tm nmlst ty cases apps goals =
    renameTerm ctx $ 
    TmAppl $ (TmMatch d tm ".0" nmlst ty $ buildResultEqs len cases goals):apps


buildTermInConstr :: Int -> Int -> Context -> Int -> Constructor -> Term -> [Term] -> (Goal, [Name], Term)
buildTermInConstr origin num ctx d (Constructor nm ty tm) tm' tmlst =
    let newtm = applyDTerms d tm tmlst in
        let typeofbranch = fullBReduction ctx $ typeOfBranch d ctx newtm tm' in
            --trace ("Before recons "++prettyShowAST typeofbranch) $
            let (newadd, ctx', nmlst, finalterm') = refineTermAndBuildContext ctx typeofbranch in
                let caselst = nm:(repeatPatternWithoutLabel d "_")++nmlst in
                    let 
                        finalterm = renameTerm ctx' finalterm' 
                        (ctx'', subty) = filterTermIntoContext ctx' num finalterm
                        subgoal = Goal (newadd + origin + num) ctx'' subty
                    in
                        (subgoal, caselst, finalterm)
                    --trace ("Branch case "++show caselst) $
                    --trace ("Inner Goal "++prettyShowAST finalterm) $ seq caselst ([], TmType)
                    
            
filterTermIntoContext :: Context -> Int -> Term -> (Context, Term)
filterTermIntoContext ctx num tm 
    | num == 0 = (ctx, tm)
    | otherwise = 
        case tm of
            TmLambda nm ty tm' ->
                let ctx' = addBinding ctx nm (VarBind ty) in 
                    filterTermIntoContext ctx' (num - 1) tm'
            _ -> error "This should not happen"


refineTermAndBuildContext :: Context -> Term -> (Int, Context, [Name], Term)
refineTermAndBuildContext ctx (TmProd nm ty tm) =
    let (_, newnm) = addAnonymousName ctx [] nm Nothing in
        let ctx' = addBinding ctx newnm (VarBind ty) in
            let newtm = tmShift 1 $ fullBReduction ctx' $ TmAppl [(TmProd nm ty tm), TmRel newnm 0] in
                let (s, ctx'', nmlst, rettm) = refineTermAndBuildContext ctx' newtm in
                    (s + 1, ctx'', newnm:nmlst, rettm)
refineTermAndBuildContext ctx tm = (0, ctx, [], tm)


typeOfBranch :: Int -> Context -> Term -> Term -> Term
typeOfBranch d ctx ctm ptm =
    --trace ("Context "++show (firstDItems 4 ctx)) $
    --trace ("Type of term "++show (typeof ctx ctm)) $
    --trace ("Term "++show ctm) $
    --trace ("P Term "++show ptm++"\n") $
    case fromRight undefined $ typeof ctx ctm of
        TmProd nm ty _ ->
            let 
                (_, newnm) = addAnonymousName ctx [] nm Nothing 
                ctx' = addBinding ctx newnm (VarBind ty) 
            in
                TmProd newnm ty $ typeOfBranch d ctx' (TmAppl [tmShift 1 ctm, TmRel newnm 0]) $ tmShift 1 ptm
        TmIndType nm tmlst ->
            TmAppl $ ptm:(drop d tmlst)++[ctm]
        _ -> error "This should not happen"
   

applyDTerms :: Int -> Term -> [Term] -> Term
applyDTerms d tm tmlst 
    | d == 0 = tm
    | otherwise =
        let lst = firstDItems d tmlst in
            TmAppl $ tm:lst


buildTermInConstrs :: Int -> Int -> Context -> Name -> Term -> [Term] -> [(Goal, [Name], Term)]
buildTermInConstrs k num ctx nm tm tmlst =
    let cons = fromRight undefined $ getIndTypeConstrlst ctx nm in
        let d = getIndTypeExpInt ctx nm in
            map (\x -> buildTermInConstr k num ctx d x tm tmlst) cons


buildTermPBeforeBranch :: Term -> Int -> Term 
buildTermPBeforeBranch tm d
    | d == 0 = tm
    | otherwise = 
        TmLambda "." TmType $ buildTermPBeforeBranch tm (d - 1)


buildMatchReturnType :: Int -> Goal -> [(Term, Term, Int)] -> Term -> (Context, Term, [Term])
buildMatchReturnType ups (Goal d ctx ty) tmp tm =
    let substlst = map (\case (tm1, tm2, x) -> (tm1, tm2, d - x)) tmp in
        let (ctx', params, substlst', apps) = 
                rebuildContextAndReturnTypeParam ups d d ctx substlst (getForbName tm) in
            --trace ("params "++show params++"\nsubstlist "++show substlst') $ 
            --trace ("rawinner "++show ty) $
            let inner = accSubstTerm (d + 1) (tmShift (length params + ups - 1) ty) substlst' in
                let ret = abstractParamsAndInner params inner in
                    (ctx', ret, apps)


abstractParamsAndInner :: [Term] -> Term -> Term
abstractParamsAndInner [] tm = tm
abstractParamsAndInner ((TmLambda nm ty _):b) tm =
    TmLambda nm ty $ abstractParamsAndInner b tm


rebuildContextAndReturnTypeParam :: Int -> Int -> Int -> Context 
        -> [(Term, Term, Int)] -> Name -> (Context, [Term], [(Term, Term, Int)], [Term])
rebuildContextAndReturnTypeParam ups d od ctx substlst forbnm
    | d == 0 = (ctx, [], substlst, [])
    | otherwise =
        let (ctx', tmlst', substlst', apps') = 
                rebuildContextAndReturnTypeParam (ups + 1) (d - 1) od (tail ctx) substlst forbnm 
            (nm, (VarBind tm)) = head ctx 
            hd = (nm, (VarBind tm)) 
        in
            if head nm == '~' then 
                (hd:ctx', tmlst', substlst', apps')
            else if matchNameInList nm substlst' then
                (("~"++nm, (VarBind tm)):ctx', tmlst', substlst', apps')
            else 
                let newtm = tmShift (ups + length tmlst') tm in
                    --trace (show newtm++show ups) $ 
                    if any (\case (tm1, _, c) -> c < d && findAndAlert newtm tm1) substlst' then
                        let acterm = accSubstTerm d newtm substlst' 
                            hd' = ("~"++nm, (VarBind tm)) 
                            putterm = TmLambda nm acterm TmType 
                        in
                            let newsubstlst = map 
                                    (\case (tm1, tm2, d) -> (tmShift 1 tm1, tmShift 1 tm2, d)) 
                                    substlst'
                                putsub = (TmRel nm (ups + length tmlst'), TmRel nm 0, d)
                                newapp = TmRel nm (od - d) 
                            in 
                                (hd':ctx', tmlst'++[putterm], newsubstlst++[putsub], apps'++[newapp]) 
                    else (hd:ctx', tmlst', substlst', apps')


matchNameInList :: Name -> [(Term, Term, Int)] -> Bool
matchNameInList nm [] = False
matchNameInList nm ((TmRel nm1 _, _, _):b) = 
    nm == nm1 || matchNameInList nm b
matchNameInList nm (a:b) =
    matchNameInList nm b


accSubstTerm :: Int -> Term -> [(Term, Term, Int)] -> Term
accSubstTerm d tm [] = tm
accSubstTerm d tm ((tm1, tm2, c):b) 
    | c < d =
        --trace ("into subst "++show tm ++ "\n" ++ show tm1) $
        let tm' = findAndReplace tm tm1 tm2 in
            accSubstTerm d tm' b
    | otherwise = accSubstTerm d tm b


leaveOutContextTerm :: Context -> Int -> Context
leaveOutContextTerm (cur:ctx) d 
    | d == 0 =
        case cur of
            (nm, (VarBind ty)) -> 
                let newnm = "~"++nm in
                    (newnm, (VarBind ty)):ctx
            _ -> error "Can not leave out non-Varbind term"
    | otherwise = cur:leaveOutContextTerm ctx (d - 1)


buildSubstList :: Context -> Int -> Term -> Term -> [(Term, Term, Int)]
buildSubstList ctx d tm (TmIndType nm tmlst) =
    let init = (tmShift d tm, TmRel ".0" 0, gethighestIndex tm) in
        let k = getIndTypeExpInt ctx nm in
            init:reverse (mapReplaceAnonymousTerm d $ drop k tmlst)


mapReplaceAnonymousTerm :: Int -> [Term] -> [(Term, Term, Int)]
mapReplaceAnonymousTerm d [] = []
mapReplaceAnonymousTerm d (tm:tmlst) =
    let k = length tmlst + 1 in
        (tmShift d tm, TmRel ("."++show k) k, gethighestIndex tm):mapReplaceAnonymousTerm d tmlst


gethighestIndex :: Term -> Int 
gethighestIndex tm =
    case tm of
        TmRel _ idx -> idx
        TmVar _ -> -1
        TmAppl tmlst -> 
            accmax (\x -> gethighestIndex x) tmlst 
        TmProd _ tm4 tm5 -> 
            max (gethighestIndex tm4) (gethighestIndex tm5 - 1)
        TmLambda _ tm4 tm5 -> 
            max (gethighestIndex tm4) (gethighestIndex tm5 - 1)
        TmFix _ tm4 ->
            gethighestIndex tm4
        TmLetIn _ tm4 tm5 tm6 ->
            max (gethighestIndex tm4) $ max (gethighestIndex tm5) (gethighestIndex tm6 - 1)
        TmIndType _ tmlst ->
            accmax (\x -> gethighestIndex x ) tmlst
        TmConstr nm tmlst -> 
            accmax (\x -> gethighestIndex x ) tmlst
        TmType -> -1
        TmTypeHigher -> -1
        TmMatch d tm4 _ nmlst tm5 eqlst ->
            let k = length nmlst - d in
                max (gethighestIndex tm4) $ max (gethighestIndex tm5 - k) $
                accmax (\x -> gethighestIndexInEq x) eqlst


gethighestIndexInEq :: Equation -> Int
gethighestIndexInEq (Equation nmlst tm1) =
    let s = getImpParams $ tail nmlst in
        -s + gethighestIndex tm1


findAndAlert :: Term -> Term -> Bool
findAndAlert tm1 tm2 
    | termEqNameless tm1 tm2 = True
    | otherwise = 
        case tm1 of
            TmVar _ -> False
            TmRel _ _ -> False
            TmAppl tmlst -> 
                any (\x -> findAndAlert x tm2) tmlst 
            TmProd nm tm4 tm5 -> 
                findAndAlert tm4 tm2 ||  
                findAndAlert tm5 (tmShift 1 tm2) 
            TmLambda nm tm4 tm5 -> 
                findAndAlert tm4 tm2 ||
                findAndAlert tm5 (tmShift 1 tm2) 
            TmFix d tm4 ->
                findAndAlert tm4 tm2 
            TmLetIn nm tm4 tm5 tm6 ->
                findAndAlert tm4 tm2 || 
                findAndAlert tm5 tm2 ||
                findAndAlert tm6 (tmShift 1 tm2) 
            TmIndType nm tmlst ->
                any (\x -> findAndAlert x tm2) tmlst
            TmConstr nm tmlst -> 
                any (\x -> findAndAlert x tm2) tmlst
            TmType -> False
            TmTypeHigher -> False
            TmMatch d tm4 nm nmlst tm5 eqlst ->
                let k = length nmlst - d in
                    findAndAlert tm4 tm2 ||
                    findAndAlert tm5 (tmShift k tm2) ||
                    any (\x -> findAndAlertInEq x tm2) eqlst


findAndAlertInEq :: Equation -> Term -> Bool
findAndAlertInEq (Equation nmlst tm1) tm2 =
    let s = getImpParams $ tail nmlst in
        findAndAlert tm1 (tmShift s tm2)


findAndReplace :: Term -> Term -> Term -> Term
findAndReplace tm1 tm2 tm3 
    | termEqNameless tm1 tm2 = tm3
    | otherwise =
        case tm1 of
            TmVar _ -> tm1
            TmRel _ _ -> tm1
            TmAppl tmlst -> 
                TmAppl $ map (\x -> findAndReplace x tm2 tm3) tmlst 
            TmProd nm tm4 tm5 -> 
                TmProd nm (findAndReplace tm4 tm2 tm3) $ findAndReplace tm5 (tmShift 1 tm2) (tmShift 1 tm3)
            TmLambda nm tm4 tm5 -> 
                TmLambda nm (findAndReplace tm4 tm2 tm3) $ findAndReplace tm5 (tmShift 1 tm2) (tmShift 1 tm3)
            TmFix d tm4 ->
                TmFix d $ findAndReplace tm4 tm2 tm3
            TmLetIn nm tm4 tm5 tm6 ->
                TmLetIn nm (findAndReplace tm4 tm2 tm3) (findAndReplace tm5 tm2 tm3) $ 
                    findAndReplace tm6 (tmShift 1 tm2) (tmShift 1 tm2)
            TmIndType nm tmlst ->
                TmIndType nm $ map (\x -> findAndReplace x tm2 tm3) tmlst
            TmConstr nm tmlst -> 
                TmConstr nm $ map (\x -> findAndReplace x tm2 tm3) tmlst
            TmType -> tm1
            TmTypeHigher -> tm1
            TmMatch d tm4 nm nmlst tm5 eqlst ->
                let k = length nmlst - d in
                    TmMatch d (findAndReplace tm4 tm2 tm3) nm nmlst (findAndReplace tm5 (tmShift k tm2) (tmShift k tm3)) $
                    map (\x -> findAndReplaceInEq x tm2 tm3) eqlst


findAndReplaceInEq :: Equation -> Term -> Term -> Equation
findAndReplaceInEq (Equation nmlst tm1) tm2 tm3 =
    let s = getImpParams $ tail nmlst in
        Equation nmlst $ findAndReplace tm1 (tmShift s tm2) (tmShift s tm3)


buildMatchNameList :: Context -> Name -> [Name]
buildMatchNameList ctx nm =
    let d = getIndTypeExpInt ctx nm in
        let d' = getIndTypeImpInt ctx nm in
            (nm):(repeatPatternWithoutLabel d "_")++(repeatPatternWithLabel d' ".")


repeatPatternWithoutLabel :: Int -> String -> [String]
repeatPatternWithoutLabel d x 
    | d == 0 = []
    | otherwise = x:repeatPatternWithoutLabel (d - 1) x


repeatPatternWithLabel :: Int -> String -> [String]
repeatPatternWithLabel d x 
    | d == 0 = []
    | otherwise = (x++show d):repeatPatternWithLabel (d - 1) x


getForbName :: Term -> Name
getForbName tm =
    case tm of
        TmRel nm _ -> nm
        _ -> ""


captureContextAndRename :: Context -> ([Term] -> Term) -> [Term] -> Term
captureContextAndRename ctx f lst =
    let tm = f lst in
        renameTerm ctx tm


getImpParams :: [Name] -> Int 
getImpParams [] = 0
getImpParams (a:b)
    | a == "_" = getImpParams b
    | otherwise = 1 + getImpParams b


getIndTypeExpInt :: Context -> Name -> Int 
getIndTypeExpInt ctx nm =
    let (d, _, _, _) = fromRight undefined $ getIndType ctx nm in
        d


getIndTypeImpInt :: Context -> Name -> Int
getIndTypeImpInt ctx nm =
    let (d, ty, _, _) = fromRight undefined $ getIndType ctx nm in
        countParams ty - d


countParams :: Term -> Int
countParams tm =
    case tm of
        TmProd _ _ tm' -> countParams tm' + 1
        TmLambda _ _ tm' -> countParams tm' + 1
        _ -> 0
        
accmax :: (a -> Int) -> [a] -> Int
accmax f lst =
    let nlst = map f lst in
        maxList nlst

maxList :: [Int] -> Int
maxList [] = -1
maxList (a:b) = max a $ maxList b

firstDItems :: Int -> [a] -> [a]
firstDItems d lst 
    | d == 0 = []
    | otherwise = (head lst):firstDItems (d - 1) (tail lst)
