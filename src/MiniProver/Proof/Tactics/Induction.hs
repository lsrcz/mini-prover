{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.Induction where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Rename
import MiniProver.Core.Subst
import MiniProver.Core.Reduction
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST
import MiniProver.PrettyPrint.Colorful
import MiniProver.Proof.Tactics.Intros
import Debug.Trace
import Data.Either (fromRight)

termInTerm :: Term -> Term -> Bool
termInTerm tm1 tm2
  | termEqNameless tm1 tm2 = True
termInTerm tm1 (TmAppl termlst) =
  any (termInTerm tm1) termlst
termInTerm tm1 (TmProd _ ty tm) =
  termInTerm tm1 ty || termInTerm (tmShift 1 tm1) tm
termInTerm tm1 (TmLambda _ ty tm) =
  termInTerm tm1 ty || termInTerm (tmShift 1 tm1) tm
termInTerm tm1 (TmFix _ tm) = termInTerm tm1 tm
termInTerm tm1 (TmLetIn _ ty tm bdy) =
  termInTerm tm1 ty || termInTerm tm1 tm || termInTerm (tmShift 1 tm1) bdy
termInTerm tm1 (TmIndType _ termlst) =
  any (termInTerm tm1) termlst
termInTerm tm1 (TmConstr _ termlst) =
  any (termInTerm tm1) termlst
termInTerm tm1 (TmMatch i term _ namelst retty equlst) =
  termInTerm tm1 term || termInTerm (tmShift (length namelst - i) term) retty ||
  any (termInEquation i tm1) equlst
termInTerm _ _ = False

termInEquation :: Int -> Term -> Equation -> Bool
termInEquation i tm1 (Equation namelst tm) =
  termInTerm (tmShift (length namelst - i - 1) tm1) tm

findDepDown :: Context -> Term -> [Bool]
findDepDown ctx tm =
  findDepDownInside ctx [False | _ <- ctx] [tm]

findDepDownSingleTerm :: Context -> Int -> Term -> [Bool]
findDepDownSingleTerm [] i tm = []
findDepDownSingleTerm ((name,VarBind ty):xs) i tm =
  termInTerm tm (tmShift i ty) : findDepDownSingleTerm xs (i+1) tm

findDepDownInside :: Context -> [Bool] -> [Term] -> [Bool]
findDepDownInside ctx origdeplst [] = origdeplst
findDepDownInside ctx origdeplst tmlst =
  let
    depMap = map (findDepDownSingleTerm ctx 1) tmlst
    totDepMap = foldl (zipWith (||)) [False | _ <- ctx] depMap

    deltaDepMap = zipWith (\x y -> x && not y) totDepMap origdeplst
    getNewTmlst :: Int -> [Bool] -> [Term]
    getNewTmlst i [] = []
    getNewTmlst i (False:xs) = getNewTmlst(i+1) xs
    getNewTmlst i (True:xs) = TmRel "x" i : getNewTmlst (i+1) xs
    newTmlst = getNewTmlst 0 deltaDepMap
  in
    if null newTmlst then origdeplst
      else zipWith (||) origdeplst $ findDepDownInside ctx totDepMap newTmlst

findDepDownInd :: Context -> Int -> Term -> Term -> [Bool]
findDepDownInd ctx i itype@(TmIndType _ tmlst) tmorig =
  findDepDownInside ctx [False | _ <- ctx] (tmorig:drop i tmlst)

renameSub :: Term -> Term -> Term -> Term
renameSub tm1 tm2 tmsub
  | termEqNameless tmsub tm1 = tm2
renameSub tm1 tm2 (TmAppl tmlst) =
  TmAppl $ map (renameSub tm1 tm2) tmlst
renameSub tm1 tm2 (TmLambda name ty tm) =
  TmLambda name (renameSub tm1 tm2 ty) (renameSub (tmShift 1 tm1) (tmShift 1 tm2) tm)
renameSub tm1 tm2 (TmProd name ty tm) =
  TmProd name (renameSub tm1 tm2 ty) (renameSub (tmShift 1 tm1) (tmShift 1 tm2) tm)
renameSub tm1 tm2 (TmFix i tm) = TmFix i (renameSub tm1 tm2 tm)
renameSub tm1 tm2 (TmLetIn name ty tm bdy) = TmLetIn name
  (renameSub tm1 tm2 ty) (renameSub tm1 tm2 tm) (renameSub (tmShift 1 tm1) (tmShift 1 tm2) bdy)
renameSub tm1 tm2 (TmIndType name tmlst) = TmIndType name (map (renameSub tm1 tm2) tmlst)
renameSub tm1 tm2 (TmConstr name tmlst) = TmConstr name (map (renameSub tm1 tm2) tmlst)
renameSub tm1 tm2 (TmMatch i tm name namelst retty equlst) =
  let shiftInRetty = tmShift (length namelst - i) in
  TmMatch i (renameSub tm1 tm2 tm) name namelst (renameSub (shiftInRetty tm1) (shiftInRetty tm2) retty) $
  map (renameInEqn tm1 tm2 i) equlst
renameSub _ _ tm = tm

renameInEqn :: Term -> Term -> Int -> Equation -> Equation
renameInEqn tm1 tm2 i (Equation namelst tm) =
  let shiftInEqn = tmShift (length namelst - i - 1) in
  Equation namelst (renameSub (shiftInEqn tm1) (shiftInEqn tm2) tm)

renamePTail :: [Term] -> Term -> Term
renamePTail tmlst term = go 0 tmlst term
  where
    go :: Int -> [Term] -> Term -> Term
    go _ [] tm = tm
    go i (x:xs) tm = go (i + 1) xs $ renameSub x (TmRel "." i) tm

splitAbs :: Term -> Int -> (Term, Term -> Term)
splitAbs tm i
  | i == 0 = (tm, id)
splitAbs (TmLambda name ty tm) i = 
  case splitAbs tm (i - 1) of
    (f,s) -> (f,TmLambda name ty . s)
-- splitAbs t i = error (prettyShowAST t ++ show i)

renameP :: [Term] -> Int -> Term -> Term
renameP tmlst i pterm =
  case splitAbs pterm (i+1) of
    (f,s) -> s $ renamePTail (map (tmShift (i+1)) tmlst) f

buildPTail :: Term -> Int -> Int -> Context -> [Bool] -> Term
buildPTail goalty i j _ [] = tmShift (i + j+1) goalty
buildPTail goalty i j ((_,VarBind ty):ctxs) (True:xs) =
  TmProd "." (tmShift (i + j+1) ty) $ buildPTail goalty (i-1) (j+1) ctxs xs
buildPTail goalty i j (_:ctxs) (False:xs) =
  buildPTail goalty (i-1) j ctxs xs

buildPLambda :: Term -> Int -> Term -> Context -> [Bool] -> Term
buildPLambda goalty i (TmLambda name ty tm) ctx boolmap =
  TmLambda "." ty $ buildPLambda goalty (i+1) tm ctx boolmap
buildPLambda goalty i indty@(TmIndType name tmlst) ctx boolmap =
  let len = length boolmap in
  TmLambda "." indty $ buildPTail goalty (len + i) 0
    (reverse (take (length boolmap) ctx)) (reverse boolmap)
buildPLambda _ _ x _ _ = error $ prettyShowAST x

buildP :: Maybe Int -> Goal -> Term -> Term -> (Term,[Term],[Bool])
buildP idx (Goal d ctx goalty) itype@(TmIndType name tylst) tmorig =
  case getIndType ctx name of
    Left _ -> error "This should not happen"
    Right (i,ty,tm,constrlst) ->
      let
        strategy =
          StrategySet (strategyListToSet [BetaLambda]) 0 0 0
        phead = reductionWithStrategy strategy ctx (TmAppl (tm:take i tylst))
        boolmap = findDepDownInd (take d ctx) i itype tmorig
        setPos :: Bool -> [Bool] -> Int -> [Bool]
        setPos _ [] _ = []
        setPos b (x:xs) i
          | i == 0 = b : xs
          | otherwise = x : setPos b xs (i-1)
        falsedBoolmap =
          case idx of
            Nothing -> boolmap
            Just idxt -> setPos False boolmap idxt
        truedBoolmap =
          case idx of
            Nothing -> boolmap
            Just idxt -> setPos True boolmap idxt
        getDepTms :: Int -> [Term] -> [Bool] -> Context ->  [Term]
        getDepTms _ acc [] _ = acc
        getDepTms i acc (False:bs) (x:xs) = getDepTms (i+1) acc bs xs
        getDepTms i acc (True:bs) ((name,_):xs) = getDepTms (i + 1) (TmRel name i:acc) bs xs
        getDep :: [Bool] -> Context -> [Term]
        getDep = getDepTms 0 []
        plambda = renameTerm ctx $ buildPLambda goalty 0 phead ctx falsedBoolmap
        prenamelambda =
          renameP (tmorig : reverse (drop i tylst)) (length tylst - i) plambda
      in (prenamelambda,drop i tylst ++ (tmorig:getDep falsedBoolmap ctx),truedBoolmap)

genMaskedContext :: Context -> [Bool] -> Context
genMaskedContext ctx [] = ctx
genMaskedContext ((name,binding):cxs) (True:xs) =
  ('~':name,binding) : genMaskedContext cxs xs
genMaskedContext (x:cxs) (False:xs) = x : genMaskedContext cxs xs

genGoalsFromFList :: Int -> Context -> Int -> Int -> Term -> [Goal]
genGoalsFromFList numOfContext maskedContext totf i _
  | totf == i = []
genGoalsFromFList numOfContext maskedContext totf i (TmLambda _ ty tm) =
  Goal numOfContext maskedContext (tmShift (-i) ty)
  : genGoalsFromFList numOfContext maskedContext totf (i + 1) tm
genGoalsFromFList _ _ _ _ t = error (prettyShowAST t)

buildRawResult :: Maybe Int -> Goal -> Term -> Term -> Result
buildRawResult idx goal@(Goal d ctx goalty) itype@(TmIndType name tylst) tmorig =
  case (getBindingTerm ctx (fromRight undefined $ nameToIndex ctx $ name ++ "_rect")
       ,getIndType ctx name) of
    (Right tm, Right (i,ity,itm,constrlst)) ->
      let
        (p,lst,boolmap) = buildP idx goal itype tmorig
        strategy =
          StrategySet (strategyListToSet [BetaAppl .. BetaInLambdaTm]) 0 0 0
        ptail = reductionWithStrategy strategy ctx (TmAppl ((tm:take i tylst) ++ [p]))
        maskedContext = genMaskedContext ctx boolmap
        (goals, funcs) =
          unzip $ map ((\case Result g r -> (g, r)) . fromRight undefined . (`handleIntros` Intros)) $ 
          genGoalsFromFList d maskedContext (length constrlst) 0 ptail
        flatGoals = map head goals
        relTm = TmRel
          (name ++ "_rect")
          (fromRight undefined $ nameToIndex ctx $ name ++ "_rect")
        resultFunc goaltmlst = renameTerm ctx $ TmAppl ((relTm :take i tylst) ++ [p] ++ zipWith (\f x -> f [x]) funcs goaltmlst ++ lst)
      in 
        Result flatGoals resultFunc
    _ -> error "This should not happen"

handleInduction :: Goal -> Tactic -> Either TacticError Result
handleInduction goal@(Goal _ ctx ty) i@(Induction tm) =
  case typeof ctx tm of
    Left (TypingError term err) -> Left $ TacticError (prettyShow term ++ err)
    Right ty@(TmIndType name tylst) ->
      Right $
        case buildRawResult (
          case tm of
            TmRel _ idx -> Just idx
            _ -> Nothing
          ) goal ty tm of
            Result goals func -> Result goals (checkResult goal i . func)
