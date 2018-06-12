module MiniProver.Proof.Tactics.Apply (
    handleApply
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Syntax
import MiniProver.Core.Typing
import MiniProver.Core.SimplifyIndType
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.Core.Context
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename
import Debug.Trace

handleApply :: Goal -> Tactic -> Either TacticError Result
handleApply g@(Goal num ctx t1) a@(Apply t2 Nothing) =
  let 
    ty = typeof ctx t2 
  in 
    case ty of
      Left (TypingError t er) -> Left (TacticError ("typing error: "++er))
      Right realTy ->
        let 
          strategy =
            fullBZIDStrategySet `clearStrategyInSet` BetaInProdTy
            `clearStrategyInSet` ZetaInProdTy
            `clearStrategyInSet` IotaInProdTy
            `clearStrategyInSet` DeltaInProdTy
          simpleTy = reductionWithStrategy strategy ctx realTy
          simpleGoal = fullBZIDReduction ctx t1
        in 
          if typeeq ctx (Right simpleGoal) (Right simpleTy)
            then 
              Left (TacticError "type is not matched")
            else
              case find ctx simpleGoal simpleTy num 0 of
                Left er -> Left er
                Right goalList ->
                  Right (Result (map renameGoal goalList) (\tmlst -> checkResult g a (renameTerm ctx $ simpleResultFunc t2 tmlst)))

handleApply g@(Goal num ctx t1) a@(Apply t2 (Just name)) =
  case typeof ctx t2 of
    Left (TypingError t er) -> Left (TacticError ("typing error: "++er))
    Right realTy ->
      case nameToIndex ctx name of 
        Left _ -> Left (TacticError "No such variable")
        Right index ->
          if index >= num
            then (Left (TacticError "index out of bind"))
            else
              case typeof ctx (TmAppl [t2,(TmRel name index)]) of
                Left er -> Left (TacticError "type is not matched")
                Right ty -> 
                  case getGoal num ctx index (renameTerm ctx ty) t1 of
                    (_,Left er) -> Left er
                    (newList,Right goal) ->
                      Right
                        (Result
                          [renameGoal goal]
                          (\tmlst -> checkResult g a (resultFunc name t2 newList tmlst)))
    
simpleResultFunc :: Term->[Term]->Term
simpleResultFunc f ls = (TmAppl (f:ls))

renameGoal :: Goal -> Goal
renameGoal (Goal i ctx ty) = Goal i ctx (renameTerm ctx ty)


resultFunc :: Name->Term->[Int]->[Term]->Term
resultFunc str func newList [t] = 
  resultFunc' str func newList t 0
resultFunc' :: Name->Term->[Int]->Term->Int->Term
resultFunc' str f newList (TmRel name index) depth=
  if index < depth
    then (TmRel name index)
    else
      let
        realIndex = index - depth
      in
        if name == str
          then  
            (TmAppl [f,(TmRel name (getNewIndex index newList))])
          else
            (TmRel name (getNewIndex index newList))
resultFunc' str f newList (TmAppl ls) depth =
  TmAppl
  (map
    (\t -> resultFunc' str f newList t depth)
    ls)
resultFunc' str f newList (TmProd name t1 t2) depth =
  TmProd
    name
    (resultFunc' str f newList t1 depth)
    (resultFunc' str f newList t2 (depth+1))
resultFunc' str f newList (TmLambda name t1 t2) depth =
  TmLambda
    name
    (resultFunc' str f newList t1 depth)
    (resultFunc' str f newList t2 (depth+1)) 
resultFunc' str f newList (TmFix num t) depth =
  TmFix
    num
    (resultFunc' str f newList t depth)  
resultFunc' str f newList (TmLetIn name t1 t2 t3) depth =
  TmLetIn
    name
    (resultFunc' str f newList t1 depth)
    (resultFunc' str f newList t2 depth)
    (resultFunc' str f newList t3 (depth+1))
resultFunc' str f newList (TmIndType name ls) depth =
  TmIndType
    name
    (map
      (\t -> resultFunc' str f newList t depth)
      ls)
resultFunc' str f newList (TmConstr name ls) depth =
  TmConstr
    name
    (map
      (\t -> resultFunc' str f newList t depth)
      ls)
resultFunc' str f newList (TmMatch num t1 name nameLs t2 eqLs) depth =
  TmMatch  
    num
    (resultFunc' str f newList t1 depth)
    name
    nameLs
    (resultFunc' str f newList t2 (depth+(length nameLs)-num))
    (map
      (\(Equation nameLs t)->
        (Equation nameLs (resultFunc' str f newList t (depth+(length nameLs)-num-1)   )))
      eqLs)
resultFunc' str f newList t depth = t
   

quickSort :: Ord a => [a] -> [a]
quickSort [] = []
quickSort (x:xs) = (quickSort mini) ++ [x] ++ (quickSort maxi)
        where
            mini = filter (<x) xs
            maxi = filter (>=x) xs

getGoal::Int->Context->Int->Term->Term->([Int],Either TacticError Goal)
getGoal num ctx index term oldGoal=
  if anotherDepend ctx index 0
    then ([],(Left (TacticError "some hypothesis is depend on the term")))
    else
      let
        dependLs =quickSort(getDependList ctx index term 0 []) 
      in  --cong xiao dao da qie bu chong fu
        if inList dependLs index
          then
            ([],Left (TacticError "type depend!"))
          else
            let 
              mapList = 
                buildmapList dependLs 0 0 (index-(length dependLs)+1) index
            in
              let
                newList = buildnewList 0 mapList index
              in
                let 
                  newCtx = renameCtx index $ makeCtx ctx newList mapList 0 index ctx term
                  newGoal = changeIndex oldGoal mapList (-1) 
                in
                  (newList,Right(Goal num newCtx newGoal))

renameCtx :: Int -> Context -> Context
renameCtx i ctx@((x,VarBind ty):xs)
  | i == 0 = (x,VarBind $ renameTerm xs ty) : xs
  | otherwise = let newctx = renameCtx (i-1) xs in
      (x,VarBind $ renameTerm newctx ty) : newctx

makeCtx :: Context->[Int]->[Int]->Int->Int->Context->Term->Context
makeCtx ctx newList mapList i bound ls changeTerm =
  if i > bound
    then ls
    else
      let
        Right bind = getBinding ctx (head newList)
        Right name = indexToName ctx (head newList)
      in 
        if (head newList) == bound
          then 
            let
              tmp = 
                changeBind 
                  (case bind of
                    VarBind _ ->VarBind changeTerm
                    TmAbbBind _ tmptm -> TmAbbBind changeTerm tmptm) 
                  mapList 
                  i
            in
              (name,tmp):
              (makeCtx 
                ctx 
                (tail newList) 
                mapList 
                (i+1) 
                bound 
                (tail ls)
                changeTerm) 
          else
            let
              tmp = changeBind bind mapList i
            in
              (name,tmp):
              (makeCtx 
                ctx 
                (tail newList) 
                mapList 
                (i+1) 
                bound 
                (tail ls) 
                changeTerm)

changeBind :: Binding->[Int]->Int->Binding
changeBind NameBind mapList i = NameBind
changeBind (VarBind tm) mapList i = VarBind (changeIndex tm mapList i)
changeBind (TmAbbBind tm Nothing) mapList i = 
  TmAbbBind (changeIndex tm mapList i) Nothing
changeBind (TmAbbBind tm (Just tm1)) mapList i = 
  TmAbbBind (changeIndex tm mapList i) (Just (changeIndex tm1 mapList i))
changeBind (IndTypeBind num t1 t2 ls) mapList i = 
  IndTypeBind 
    num 
    (changeIndex t1 mapList i)
    (changeIndex t2 mapList i)
    (map
      (\(Constructor name tm1 tm2)->
        (Constructor 
          name 
          (changeIndex tm1 mapList i)
          (changeIndex tm2 mapList i)))
      ls)

changeIndex :: Term->[Int]->Int->Term
changeIndex t mapList i= changeIndex' t mapList i 0

changeIndex' :: Term->[Int]->Int->Int->Term
changeIndex' (TmRel name index) mapList i depth =
  if ((index >= depth)&&(index-depth<(length mapList)))
    then TmRel name ((getNewIndex (index-depth) mapList) - i -1 + depth)
    else
      if (index >= depth)
        then TmRel name (index-i-1)
        else TmRel name index
changeIndex' (TmAppl ls) mapList i depth =
  TmAppl 
    (map
      (\t->changeIndex' t mapList i depth)
      ls)
changeIndex' (TmProd name t1 t2) mapList i depth =
  TmProd 
    name 
    (changeIndex' t1 mapList i depth)
    (changeIndex' t2 mapList i (depth+1))
changeIndex' (TmLambda name t1 t2) mapList i depth =
  TmLambda 
    name 
    (changeIndex' t1 mapList i depth)
    (changeIndex' t2 mapList i (depth+1))  
changeIndex' (TmFix num t) mapList i depth =
  TmFix num (changeIndex' t mapList i depth)
changeIndex' (TmLetIn name t1 t2 t3) mapList i depth =
  TmLetIn 
    name
    (changeIndex' t1 mapList i depth)
    (changeIndex' t2 mapList i depth)
    (changeIndex' t3 mapList i (depth+1))
changeIndex' (TmIndType name ls) mapList i depth =
  TmIndType
    name
    (map
      (\t->changeIndex' t mapList i depth)
      ls)
changeIndex' (TmConstr name ls) mapList i depth =
  TmConstr
    name
    (map
      (\t->changeIndex' t mapList i depth)
      ls)
changeIndex' (TmMatch num t1 name nameLs t2 eqLs) mapList i depth = 
  TmMatch   
    num
    (changeIndex' t1 mapList i depth) 
    name
    nameLs
    (changeIndex' t2 mapList i (depth+(length nameLs)-num))
    (map
      (\(Equation nameLs t)->
        (Equation nameLs (changeIndex' t mapList i (depth +(length nameLs)-num-1))))
      eqLs)
changeIndex' t mapList i depth = t


getNewIndex :: Int->[Int]->Int
getNewIndex i (x:ls) =
  if i == 0
    then x
    else 
      getNewIndex (i-1) ls


buildmapList :: [Int]->Int->Int->Int->Int->[Int]
buildmapList dependLs index i base bound=
  if i > bound 
    then []
    else
      if ((not $ null dependLs) &&(i == (head dependLs)))
        then
          (index+base):
          (buildmapList (tail dependLs) (index+1) (i+1) base bound) 
        else
          (i-index):
          (buildmapList dependLs index (i+1) base bound) 

buildnewList :: Int->[Int]->Int->[Int]
buildnewList i ls bound=
  if i > bound
    then []
    else
      (findnumInList i ls 0):(buildnewList (i+1) ls bound)
findnumInList num (x:ls) index=
  if num == x
    then index
    else
      findnumInList num ls (index+1)
  
      
inList :: [Int]->Int->Bool
inList [] num = False
inList (x:ls) num =
  if x == num
    then True
    else  inList ls num

caseBind :: Context->Int->Int->[Int]->[Int]
caseBind ctx bound realIndex newList =
  case getBinding ctx realIndex of 
    Right (NameBind) -> newList
    Right (VarBind term) -> 
      getDependList ctx bound term 0 newList
    Right (TmAbbBind term Nothing) ->
      getDependList ctx bound term 0 newList
    Right (TmAbbBind term (Just term1)) ->
      let 
        newnewList = getDependList ctx bound term 0 newList
      in
        getDependList ctx bound term1 0 newnewList
    Right (IndTypeBind n t1 t2 ls) ->
      let 
        new1List = getDependList ctx bound t1 0 newList
      in
        let 
          new2List = getDependList ctx bound t2 0 new1List
        in
          foldl 
            (\ls (Constructor name t1 t2) -> 
              let
                ls1 = getDependList ctx bound t1 0 ls
              in
                getDependList ctx bound t2 0 ls1)
            new2List
            ls          

getDependList :: Context->Int->Term->Int->[Int]->[Int]      
getDependList ctx bound (TmRel name index) num nowList =
  if ((index >= num) && ((index-num) <= bound))      
    then  -- ???????????????
      let 
        realIndex = index - num
      in
        if inList nowList realIndex
          then nowList
          else
            let 
              newList = realIndex:nowList
            in
              caseBind ctx bound realIndex newList
    else
      nowList
  
getDependList ctx bound (TmAppl ls) num nowList =
  foldl 
    (\ls t -> getDependList ctx bound t num ls)
    nowList
    ls
getDependList ctx bound (TmProd name ty tm) num nowList =
  let 
    newList = getDependList ctx bound ty num nowList
  in
    getDependList ctx bound tm (num+1) newList
getDependList ctx bound (TmLambda name ty tm) num nowList =
  let 
    newList = getDependList ctx bound ty num nowList
  in
    getDependList ctx bound tm (num+1) newList
getDependList ctx bound (TmFix int tm) num nowList =
  getDependList ctx bound tm num nowList

getDependList ctx bound (TmLetIn name t1 t2 t3) num nowList =
  let 
    newList = getDependList ctx bound t1 num nowList
  in
    let 
      newnewList = getDependList ctx bound t2 num newList
    in 
      getDependList ctx bound t3 (num+1) newnewList 

getDependList ctx bound (TmIndType name ls) num nowList = 
  foldl 
    (\ls t -> getDependList ctx bound t num ls)
    nowList
    ls

getDependList ctx bound (TmConstr name ls) num nowList = 
  foldl 
    (\ls t -> getDependList ctx bound t num ls)
    nowList
    ls
getDependList ctx bound (TmMatch i t1 name nameLs t2 eqLs) num nowList = 
  let
    newList = getDependList ctx bound t1 num nowList
  in
    let
      new1List = getDependList ctx bound t2 (num+(length nameLs)-i) newList
    in
      foldl
      (\ls (Equation nameLs t)-> getDependList ctx bound t (num+(length nameLs)-i-1) ls)
      new1List
      eqLs

getDependList ctx bound _ num nowList = nowList



 
find :: Context->Term->Term->Int->Int->Either TacticError [Goal]
find ctx t1 t2 num depth =
  if typeeq ctx (Right t1) (Right t2)
    then
      Right []
    else 
      case t2 of
        TmProd name ty tm ->
          if findDepend ty depth 0
            then Left (TacticError "type depend!")
            else
              case find ctx (tmShift 1 t1) tm num (depth+1) of
                Left er ->Left er
                Right goalLs -> Right ((Goal num ctx (tmShift (-depth) ty)):goalLs) 
        _ -> Left (TacticError "type is not matched")

findDepend :: Term->Int->Int->Bool
findDepend (TmRel _ index) depth newdepth =
  if (index < depth)&&(index >= newdepth)
    then True
    else False
findDepend (TmAppl ls) depth newdepth =
  foldl
    (\b t-> if b then b else (findDepend t depth newdepth))
    False
    ls
findDepend (TmProd _ ty tm) depth newdepth =
  if findDepend ty depth newdepth
    then True
    else  findDepend tm (depth+1) (newdepth+1)
findDepend (TmLambda _ ty tm) depth newdepth =
  if findDepend ty depth newdepth
    then True
    else  findDepend tm (depth+1) (newdepth+1)
findDepend (TmLetIn _ t1 t2 t3) depth newdepth =
  if findDepend t1 depth newdepth
    then True
    else 
      if findDepend t2 depth newdepth 
        then True
        else findDepend t3 (depth+1) (newdepth+1)
findDepend (TmIndType _ ls) depth newdepth = 
  foldl
    (\b t-> if b then b else (findDepend t depth newdepth))
    False
    ls  
findDepend (TmConstr _ ls) depth newdepth = 
  foldl
    (\b t-> if b then b else (findDepend t depth newdepth))
    False
    ls         
findDepend (TmMatch num t1 _ nameLs t2 eqLs) depth newdepth = 
  if findDepend t1 depth newdepth
    then True
    else 
      if findDepend t2 (depth+(length nameLs)-num) (newdepth+(length nameLs)-num) 
        then True
        else
          foldl
            (\b (Equation nameLs t)-> 
              if b 
                then b 
                else 
                  (findDepend 
                    t 
                    (depth+(length nameLs)-num-1) 
                    (newdepth+(length nameLs)-num-1)))
            False
            eqLs  
findDepend t depth newdepth = False



anotherDepend :: Context->Int->Int->Bool
anotherDepend ctx index i =
  if i == index
    then False
    else 
      let
        (Right bind) = getBinding ctx i 
      in
        if 
          (case bind of
            NameBind -> False
            VarBind t -> checkDepend t index 0
            TmAbbBind t1 Nothing -> checkDepend t1 index 0
            TmAbbBind t1 (Just t2) -> (checkDepend t1 index 0)||(checkDepend t2 index 0))
          then True
          else anotherDepend ctx index (i+1)

checkDepend :: Term->Int->Int->Bool
checkDepend (TmRel _ index) goal depth =
  if (index-depth) == goal  
    then True
    else False
checkDepend (TmAppl ls) goal depth =
  foldl
    (\b t->
      if(checkDepend t goal depth)
        then True
        else b)
    False
    ls
checkDepend (TmProd _ t1 t2) goal depth =
  if(checkDepend t1 goal depth)
    then True
    else (checkDepend t2 goal (depth+1))
checkDepend (TmLambda _ t1 t2) goal depth =
  if(checkDepend t1 goal depth)
    then True
    else (checkDepend t2 goal (depth+1))    
checkDepend (TmFix _ t) goal depth =
  checkDepend t goal depth
checkDepend (TmLetIn _ t1 t2 t3) goal depth =
  if(checkDepend t1 goal depth)
    then True
    else 
      if (checkDepend t2 goal depth)
        then True
        else (checkDepend t3 goal (depth+1))
checkDepend (TmIndType _ ls) goal depth =
  foldl
    (\b t->
      if(checkDepend t goal depth)
        then True
        else b)
    False
    ls
checkDepend (TmConstr _ ls) goal depth =
  foldl
    (\b t->
      if(checkDepend t goal depth)
        then True
        else b)
    False
    ls
checkDepend (TmMatch num t1 _ nameLs t2 eqLs) goal depth =
  if(checkDepend t1 goal depth)
    then True
    else 
      if (checkDepend t2 goal (depth+(length nameLs)-num))
        then True
        else 
          (foldl
            (\b (Equation nameLs t)->
              if (checkDepend t goal (depth+(length nameLs)-num-1))
                then True
                else b)
            False
            eqLs)
checkDepend _ _ _ = False