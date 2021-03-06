{-# LANGUAGE LambdaCase #-}
module MiniProver.Core.Reduction (
    betaReduction
  , zetaReduction
  , iotaReduction
  , deltaReduction
  , etaExpansion
  , BetaStrategySet
  , ZetaStrategySet
  , IotaStrategySet
  , DeltaStrategySet
  , BetaStrategy(..)
  , ZetaStrategy(..)
  , IotaStrategy(..)
  , DeltaStrategy(..)
  , StrategySet(..)
  , Strategy(..)
  , strategyToIntBits
  , intBitsToStrategy
  , strategyListToSet
  , hasStrategy
  , clearBetaSet
  , clearZetaSet
  , clearIotaSet
  , clearDeltaSet
  , clearBetaIfUnset
  , clearZetaIfUnset
  , clearIotaIfUnset
  , clearDeltaIfUnset
  , fullBetaStrategy
  , fullZetaStrategy
  , fullIotaStrategy
  , fullDeltaStrategy
  , reductionWithStrategy
  , fullBZIDStrategySet
  , fullBZIDReduction
  , fullBZIReduction
  , fullBZDReduction
  , fullBZReduction
  , fullBIDReduction
  , fullBIReduction
  , fullBDReduction
  , fullBReduction
  , fullZIDReduction
  , fullZIReduction
  , fullZDReduction
  , fullZReduction
  , fullIDReduction
  , fullIReduction
  , fullDReduction
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import MiniProver.Core.Context
import Data.Bits
import Debug.Trace
import GHC.Stack

-- not context sensitive
betaReduction :: Term -> Term
betaReduction (TmAppl [TmLambda _ _ tm, tm1]) =
  tmSubstTop tm1 tm
betaReduction (TmAppl (TmLambda _ _ tm:tm1:xs)) =
  TmAppl $ tmSubstTop tm1 tm : xs
betaReduction (TmAppl [TmProd _ _ tm, tm1]) =
  tmSubstTop tm1 tm
betaReduction (TmAppl (TmProd _ _ tm:tm1:xs)) =
  TmAppl $ tmSubstTop tm1 tm : xs
-- fixpoint function shoule only be applied to variables and values and must be falling on one value
-- need checking
betaReduction (TmAppl (TmFix decpos tm:tm1:xs)) =
  betaReduction $ betaReduction (TmAppl (tm:TmFix decpos tm:tm1:xs))
betaReduction _ = error "beta reduction can only be applied to application"

zetaReduction :: Term -> Term
zetaReduction (TmLetIn _ _ tm bdy) =
  tmSubstTop tm bdy
zetaReduction _ = error "zeta reduction can only be applied to local definition(letin)"

iotaReduction :: Term -> Term
iotaReduction (TmMatch i (TmConstr name lst) _ _ _ equlist) = go equlist
  where
    go :: [Equation] -> Term
    go [] = error "Pattern matching shouldn't fail in well-typed term"
    go (x:xs) =
      case x of
        Equation names tm ->
          if name == head names
            then
              snd $ foldl (\(n,acc) tm1 -> (n - 1, tmSubstInsideN n tm1 acc))
                (length lst - i, tm) (drop i lst)
            else go xs

-- should only be applied to global definitions
deltaReduction :: Context -> Term -> Term
deltaReduction ctx tmold@(TmRel _ idx) =
  case getBinding ctx idx of
    Right (TmAbbBind _ (Just tm)) -> tm
    Right (TmAbbBind _ Nothing) -> tmold
    Right (VarBind _) -> tmold
    Right NameBind -> tmold
    Left _ -> error "This should not happen in well-typed term"
    _ -> error "delta reduction can only be applied to definitions"
deltaReduction _ _ = error "delta reduction can only be applied to variables"

-- tm : forall x:ity, ty2
etaExpansion :: Term -> Name -> Term -> Term
etaExpansion tm iname ity = TmLambda iname ity (TmAppl [tmShift 1 tm, TmRel iname 0])

type BetaStrategySet = Int
type ZetaStrategySet = Int
type IotaStrategySet = Int
type DeltaStrategySet = Int

data BetaStrategy =
    BetaAppl
  | BetaInAppl
  | BetaProd
  | BetaInProdTy
  | BetaInProdTm
  | BetaLambda
  | BetaInLambdaTy
  | BetaInLambdaTm
  | BetaFix
  | BetaInFix
  | BetaInLetInTy
  | BetaInLetInTm
  | BetaInLetInBdy
  | BetaInIndType
  | BetaInConstr
  | BetaInMatchTm
  | BetaInMatchBranch
  deriving (Eq, Show, Enum)

data ZetaStrategy =
    ZetaInAppl
  | ZetaInProdTy
  | ZetaInProdTm
  | ZetaInLambdaTy
  | ZetaInLambdaTm
  | ZetaInFix
  | ZetaLetIn
  | ZetaInIndType
  | ZetaInConstr
  | ZetaInMatchTm
  | ZetaInMatchBranch
  deriving (Eq, Show, Enum)

data IotaStrategy =
    IotaInAppl
  | IotaInProdTy
  | IotaInProdTm
  | IotaInLambdaTy
  | IotaInLambdaTm
  | IotaInFix
  | IotaInLetInTy
  | IotaInLetInTm
  | IotaInLetInBdy
  | IotaInIndType
  | IotaInConstr
  | IotaMatch
  | IotaInMatchTm
  | IotaInMatchBranch
  deriving (Eq, Show, Enum)

data DeltaStrategy =
    DeltaRel
  | DeltaInAppl
  | DeltaInProdTy
  | DeltaInProdTm
  | DeltaInLambdaTy
  | DeltaInLambdaTm
  | DeltaInFix
  | DeltaInLetInTy
  | DeltaInLetInTm
  | DeltaInLetInBdy
  | DeltaInIndType
  | DeltaInConstr
  | DeltaInMatchTm
  | DeltaInMatchBranch
  | DeltaLeadingToIota
  | DeltaRestricted
  deriving (Eq, Show, Enum)

data StrategySet = StrategySet {
    getBetaStrategySet :: BetaStrategySet
  , getZetaStrategySet :: ZetaStrategySet
  , getIotaStrategySet :: IotaStrategySet
  , getDeltaStrategySet :: DeltaStrategySet
  } deriving (Eq, Show)

class (Enum a) => Strategy a where
  hasStrategyInSet :: StrategySet -> a -> Bool
  clearStrategyInSet :: StrategySet -> a -> StrategySet
  setStrategyInSet :: StrategySet -> a -> StrategySet

strategyToIntBits :: (Strategy a) => a -> Int
strategyToIntBits = bit . fromEnum

intBitsToStrategy :: (Strategy a) => Int -> a
intBitsToStrategy = toEnum . countTrailingZeros

strategyListToSet :: (Strategy a) => [a] -> Int
strategyListToSet = foldr ((.|.) . strategyToIntBits) 0

clearStrategyInSingleSet :: (Strategy a) => Int -> a -> Int
clearStrategyInSingleSet set s = set .&. complement (strategyToIntBits s)

hasStrategy :: (Strategy a) => Int -> a -> Bool
hasStrategy set strategy = strategyToIntBits strategy .&. set /= 0

instance Strategy BetaStrategy where
  hasStrategyInSet = hasStrategy . getBetaStrategySet
  clearStrategyInSet (StrategySet b z i d) bs =
    StrategySet (clearBit b $ fromEnum bs) z i d
  setStrategyInSet (StrategySet b z i d) bs =
    StrategySet (setBit b $ fromEnum bs) z i d

instance Strategy ZetaStrategy where
  hasStrategyInSet = hasStrategy . getZetaStrategySet
  clearStrategyInSet (StrategySet b z i d) zs =
    StrategySet b (clearBit z $ fromEnum zs) i d
  setStrategyInSet (StrategySet b z i d) zs =
    StrategySet b (setBit z $ fromEnum zs) i d

instance Strategy IotaStrategy where
  hasStrategyInSet = hasStrategy . getIotaStrategySet
  clearStrategyInSet (StrategySet b z i d) is =
    StrategySet b z (clearBit i $ fromEnum is) d
  setStrategyInSet (StrategySet b z i d) is =
    StrategySet b z (setBit i $ fromEnum is) d

instance Strategy DeltaStrategy where
  hasStrategyInSet = hasStrategy . getDeltaStrategySet
  clearStrategyInSet (StrategySet b z i d) ds =
    StrategySet b z i (clearBit d $ fromEnum ds)
  setStrategyInSet (StrategySet b z i d) ds =
    StrategySet b z i (setBit d $ fromEnum ds)

clearBetaSet :: StrategySet -> StrategySet
clearBetaSet (StrategySet _ z i d) = StrategySet 0 z i d

clearZetaSet :: StrategySet -> StrategySet
clearZetaSet (StrategySet b _ i d) = StrategySet b 0 i d

clearIotaSet :: StrategySet -> StrategySet
clearIotaSet (StrategySet b z _ d) = StrategySet b z 0 d

clearDeltaSet :: StrategySet -> StrategySet
clearDeltaSet (StrategySet b z i _) = StrategySet b z i 0

clearBetaIfUnset :: BetaStrategy -> StrategySet -> StrategySet
clearBetaIfUnset a set =
  if hasStrategyInSet set a then set else clearBetaSet set

clearZetaIfUnset :: ZetaStrategy -> StrategySet -> StrategySet
clearZetaIfUnset a set =
  if hasStrategyInSet set a then set else clearZetaSet set

clearIotaIfUnset :: IotaStrategy -> StrategySet -> StrategySet
clearIotaIfUnset a set =
  if hasStrategyInSet set a then set else clearIotaSet set

clearDeltaIfUnset :: DeltaStrategy -> StrategySet -> StrategySet
clearDeltaIfUnset a set =
  if hasStrategyInSet set a then set else clearDeltaSet set

clearIfUnSet :: BetaStrategy -> ZetaStrategy -> IotaStrategy -> DeltaStrategy
             -> StrategySet -> StrategySet
clearIfUnSet b z i d s =
  clearBetaIfUnset b $
  clearZetaIfUnset z $
  clearIotaIfUnset i $
  clearDeltaIfUnset d
  s

-- beta strategies
fullBetaStrategy :: BetaStrategySet
fullBetaStrategy = strategyListToSet $ enumFrom BetaAppl

-- zeta strategies
fullZetaStrategy :: ZetaStrategySet
fullZetaStrategy = strategyListToSet $ enumFrom ZetaInAppl

-- iota strategies
fullIotaStrategy :: IotaStrategySet
fullIotaStrategy = strategyListToSet $ enumFrom IotaInAppl

-- delta strategies
fullDeltaStrategy :: DeltaStrategySet
fullDeltaStrategy = (strategyListToSet $ enumFrom DeltaRel)
                    `clearStrategyInSingleSet` DeltaRestricted

reductionWithStrategy :: StrategySet -> Context -> Term -> Term
reductionWithStrategy strategy@(StrategySet bs zs is ds) = go
  where
    goIfUnequal :: Context -> Term -> Term -> Term
    goIfUnequal ctx tmold tmnew =
      if tmold == tmnew
        then tmold
        else go ctx tmnew
    go :: HasCallStack => Context -> Term -> Term
    -- can evaluate
    go ctx tmold@TmRel{}
      | hasStrategyInSet strategy DeltaRel = 
          goIfUnequal ctx tmold $ deltaReduction ctx tmold
    go ctx tmold@TmRel{}
      | hasStrategyInSet strategy DeltaRestricted = 
          goIfUnequal ctx tmold $ deltaReduction ctx tmold
    go ctx tmold@TmRel{}
      | hasStrategyInSet strategy DeltaLeadingToIota &&
        (case deltaReduction ctx tmold of
          TmConstr{} -> True
          _ -> False) = go ctx $ deltaReduction ctx tmold
    go ctx (TmAppl [t]) =  go ctx t
    go ctx (TmAppl (TmAppl lst:tl)) = go ctx (TmAppl (lst ++ tl))
    go ctx tmold@(TmAppl (TmProd{}:_))
      | hasStrategyInSet strategy BetaProd = goIfUnequal ctx tmold $ betaReduction tmold
    go ctx tmold@(TmAppl (TmLambda{}:_))
      | hasStrategyInSet strategy BetaLambda = goIfUnequal ctx tmold $ betaReduction tmold
    go ctx tmold@(TmAppl (TmFix{}:_))
      | hasStrategyInSet strategy BetaFix = goIfUnequal ctx tmold $ betaReduction tmold 
    go ctx tmold@(TmAppl (r@TmRel{}:lst))
      | hasStrategyInSet strategy DeltaLeadingToIota &&
        case reductionWithStrategy fullBZIDStrategySet ctx r of
          TmFix i _ -> length lst >= i &&
            case reductionWithStrategy fullBZIDStrategySet ctx (lst !! (i-1)) of
              TmConstr{} -> True
              _ -> False
          l@TmLambda{} ->
            let
              getAbsNum (TmLambda _ _ tm) = 1 + getAbsNum tm
              getAbsNum _ = 0
            in
              getAbsNum l == length lst &&
              case reductionWithStrategy (StrategySet (strategyToIntBits BetaLambda) 0 0 0) ctx (TmAppl (l:lst)) of
                t@(TmMatch _ r@(TmRel _ _) _ _ _ _) ->
                  case reductionWithStrategy fullBZIDStrategySet ctx r of
                    TmConstr{} -> True
                    _ -> False
                _ -> False
          _ -> False =
            let
              maskedStrategySet =
                clearIfUnSet BetaInAppl ZetaInAppl
                  IotaInAppl DeltaInAppl strategy
            in
              goIfUnequal ctx tmold
              (TmAppl (reductionWithStrategy (setStrategyInSet strategy DeltaRestricted) ctx r
                      :map (reductionWithStrategy maskedStrategySet ctx) lst))
    go ctx tmold@(TmAppl (x:xs))
      | hasStrategyInSet strategy DeltaRestricted = goIfUnequal ctx tmold (TmAppl (go ctx x:xs))
    go ctx tmold@TmLetIn{}
      | hasStrategyInSet strategy ZetaLetIn = goIfUnequal ctx tmold $ zetaReduction tmold
    go ctx tmold@(TmMatch _ TmConstr{} _ _ _ _)
      | hasStrategyInSet strategy IotaMatch = goIfUnequal ctx tmold $ iotaReduction tmold
    -- no evaluation rule, go into the subterm
    go ctx tmold@(TmAppl tmlst) =
      let
        maskedStrategySet =
          clearIfUnSet BetaInAppl ZetaInAppl
            IotaInAppl DeltaInAppl strategy
        reducedTm = TmAppl 
          (map (reductionWithStrategy maskedStrategySet ctx) tmlst)
      in
        goIfUnequal ctx tmold reducedTm
    go ctx tmold@(TmProd name ty tm) =
      let
        maskedStrategySetTy =
          clearIfUnSet BetaInProdTy ZetaInProdTy
            IotaInProdTy DeltaInProdTy strategy
        maskedStrategySetTm =
          clearIfUnSet BetaInProdTm ZetaInProdTm
            IotaInProdTm DeltaInProdTm strategy
        reducedTm = 
          TmProd name 
            (reductionWithStrategy maskedStrategySetTy ctx ty)
            (reductionWithStrategy maskedStrategySetTm (addName ctx name) tm)
      in
        goIfUnequal ctx tmold reducedTm
    go ctx tmold@(TmLambda name ty tm) =
      let
        maskedStrategySetTy =
          clearIfUnSet BetaInLambdaTy ZetaInLambdaTy
            IotaInLambdaTy DeltaInLambdaTy strategy
        maskedStrategySetTm =
          clearIfUnSet BetaInLambdaTm ZetaInLambdaTm
            IotaInLambdaTm DeltaInLambdaTm strategy
        reducedTm = 
          TmLambda name 
            (reductionWithStrategy maskedStrategySetTy ctx ty)
            (reductionWithStrategy maskedStrategySetTm (addName ctx name) tm)
      in
        goIfUnequal ctx tmold reducedTm
    go ctx tmold@(TmFix decpos tm) =
      let
        maskedStrategySet =
          clearIfUnSet BetaInFix ZetaInFix
            IotaInFix DeltaInFix strategy
        reducedTm = TmFix decpos $ reductionWithStrategy maskedStrategySet ctx tm
      in
        goIfUnequal ctx tmold reducedTm
    go ctx tmold@(TmLetIn name tm ty bdy) =
      let
        maskedStrategySetTy =
          clearIfUnSet BetaInLetInTy ZetaLetIn
            IotaInLetInTy DeltaInLetInTy strategy
        maskedStrategySetTm =
          clearIfUnSet BetaInLetInTm ZetaLetIn
            IotaInLetInTm DeltaInLetInTm strategy
        maskedStrategySetBdy =
          clearIfUnSet BetaInLetInBdy ZetaLetIn
            IotaInLetInBdy DeltaInLetInBdy strategy
        reducedTm = TmLetIn name
          (reductionWithStrategy maskedStrategySetTy ctx ty)
          (reductionWithStrategy maskedStrategySetTm ctx tm)
          (reductionWithStrategy maskedStrategySetBdy (addName ctx name) bdy)
      in
        goIfUnequal ctx tmold reducedTm
    go ctx tmold@(TmIndType name tmlst) =
      let
        maskedStrategySet =
          clearIfUnSet BetaInIndType ZetaInIndType
            IotaInIndType DeltaInIndType strategy
        reducedTm = TmIndType name $
          map (reductionWithStrategy maskedStrategySet ctx) tmlst
      in
        goIfUnequal ctx tmold reducedTm
    go ctx tmold@(TmConstr name tmlst) =
      let
        maskedStrategySet =
          clearIfUnSet BetaInConstr ZetaInConstr
            IotaInConstr DeltaInConstr strategy
        reducedTm = TmConstr name $
          map (reductionWithStrategy maskedStrategySet ctx) tmlst
      in
        goIfUnequal ctx tmold reducedTm
    -- used in simpl tactic
    go ctx tmold@(TmMatch i r@TmRel{} name namelst retty equlst)
      | hasStrategyInSet strategy DeltaLeadingToIota &&
        (case reductionWithStrategy fullBZIDStrategySet ctx r of
          TmConstr{} -> True
          _ -> False) =
            goIfUnequal ctx tmold
            (TmMatch i
              (reductionWithStrategy (setStrategyInSet strategy DeltaRestricted) ctx r)
              name namelst retty equlst)
    go ctx tmold@(TmMatch i tm name namelst ty equlst) =
      let
        maskedStrategySetTm =
          clearIfUnSet BetaInMatchTm ZetaInMatchTm
            IotaInMatchTm DeltaInMatchTm strategy
        maskedStrategySetBranch =
          -- beta in match branch may make the application of fixpoint function diverge
          clearStrategyInSet
          ( clearIfUnSet BetaInMatchBranch ZetaInMatchBranch
              IotaInMatchBranch DeltaInMatchBranch strategy )
            BetaFix
        reducedTm = TmMatch i
          (reductionWithStrategy maskedStrategySetTm ctx tm)
          name
          namelst
          ty
          (map
            (\case
              Equation namelsteq term ->
                Equation namelsteq
                  (reductionWithStrategy
                    maskedStrategySetBranch
                    (foldl addName ctx (drop (i+1) namelsteq))
                    term
                  ))
            equlst)
      in
        goIfUnequal ctx tmold reducedTm
    go _ tmold = tmold
 
fullBZIDStrategySet :: StrategySet
fullBZIDStrategySet = StrategySet fullBetaStrategy fullZetaStrategy fullIotaStrategy fullDeltaStrategy

fullBZIDReduction :: Context -> Term -> Term
fullBZIDReduction = reductionWithStrategy fullBZIDStrategySet

fullBZIStrategySet :: StrategySet
fullBZIStrategySet = StrategySet fullBetaStrategy fullZetaStrategy fullIotaStrategy 0

fullBZIReduction :: Context -> Term -> Term
fullBZIReduction = reductionWithStrategy fullBZIStrategySet

fullBZDStrategySet :: StrategySet
fullBZDStrategySet = StrategySet fullBetaStrategy fullZetaStrategy 0 fullDeltaStrategy

fullBZDReduction :: Context -> Term -> Term
fullBZDReduction = reductionWithStrategy fullBZDStrategySet

fullBZStrategySet :: StrategySet
fullBZStrategySet = StrategySet fullBetaStrategy fullZetaStrategy 0 0

fullBZReduction :: Context -> Term -> Term
fullBZReduction = reductionWithStrategy fullBZStrategySet

fullBIDStrategySet :: StrategySet
fullBIDStrategySet = StrategySet fullBetaStrategy 0 fullIotaStrategy fullDeltaStrategy

fullBIDReduction :: Context -> Term -> Term
fullBIDReduction = reductionWithStrategy fullBIDStrategySet

fullBIStrategySet :: StrategySet
fullBIStrategySet = StrategySet fullBetaStrategy 0 fullIotaStrategy 0

fullBIReduction :: Context -> Term -> Term
fullBIReduction = reductionWithStrategy fullBIStrategySet

fullBDStrategySet :: StrategySet
fullBDStrategySet = StrategySet fullBetaStrategy 0 0 fullDeltaStrategy

fullBDReduction :: Context -> Term -> Term
fullBDReduction = reductionWithStrategy fullBDStrategySet

fullBStrategySet :: StrategySet
fullBStrategySet = StrategySet fullBetaStrategy 0 0 0

fullBReduction :: Context -> Term -> Term
fullBReduction = reductionWithStrategy fullBStrategySet

fullZIDStrategySet :: StrategySet
fullZIDStrategySet = StrategySet 0 fullZetaStrategy fullIotaStrategy fullDeltaStrategy

fullZIDReduction :: Context -> Term -> Term
fullZIDReduction = reductionWithStrategy fullZIDStrategySet

fullZIStrategySet :: StrategySet
fullZIStrategySet = StrategySet 0 fullZetaStrategy fullIotaStrategy 0

fullZIReduction :: Context -> Term -> Term
fullZIReduction = reductionWithStrategy fullZIStrategySet

fullZDStrategySet :: StrategySet
fullZDStrategySet = StrategySet 0 fullZetaStrategy 0 fullDeltaStrategy

fullZDReduction :: Context -> Term -> Term
fullZDReduction = reductionWithStrategy fullZDStrategySet

fullZStrategySet :: StrategySet
fullZStrategySet = StrategySet 0 fullZetaStrategy 0 0

fullZReduction :: Context -> Term -> Term
fullZReduction = reductionWithStrategy fullZStrategySet

fullIDStrategySet :: StrategySet
fullIDStrategySet = StrategySet 0 0 fullIotaStrategy fullDeltaStrategy

fullIDReduction :: Context -> Term -> Term
fullIDReduction = reductionWithStrategy fullIDStrategySet

fullIStrategySet :: StrategySet
fullIStrategySet = StrategySet 0 0 fullIotaStrategy 0

fullIReduction :: Context -> Term -> Term
fullIReduction = reductionWithStrategy fullIStrategySet

fullDStrategySet :: StrategySet
fullDStrategySet = StrategySet 0 0 0 fullDeltaStrategy

fullDReduction :: Context -> Term -> Term
fullDReduction = reductionWithStrategy fullDStrategySet


