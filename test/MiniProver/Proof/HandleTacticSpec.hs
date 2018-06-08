{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.HandleTacticSpec where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Proof.HandleTactic
import MiniProver.Proof.ProofDef
import MiniProver.Utils.ContextForTesting
import Data.Either (fromRight)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "exact" $ do
    let
      goal = Goal 0 realEqContext $
        TmProd "T"
          TmType
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))
      allinoneAns = fromRight undefined $ handleTactic goal
        ( Exact
          ( TmLambda "T"
            TmType
          ( TmLambda "x1"
            ( TmRel "T" 0 )
            ( TmLambda "x2"
              ( TmRel "T" 1 )
              ( TmAppl
                [ TmLambda "T"
                    TmType
                  ( TmLambda "x"
                    ( TmRel "T" 0 )
                    ( TmConstr "eq_refl"
                      [ TmRel "T" 1
                      , TmRel "x" 0 ]))
                , TmRel "T" 2
                , TmRel "x2" 0 ])))))
    it "all in one -- goal" $
      getGoalList allinoneAns `shouldBe` []
    it "all in one -- func" $
      getResultFunc allinoneAns [] `shouldBe`
      TmLambda "T"
        TmType
      ( TmLambda "x1"
        ( TmRel "T" 0 )
        ( TmLambda "x2"
          ( TmRel "T" 1 )
          ( TmConstr "eq_refl"
            [ TmRel "T" 2
            , TmRel "x2" 0 ])))
  describe "intro" $ do
    let
      goal = Goal 0 realEqContext $
        TmProd "T"
          TmType
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))
      nonameAns = fromRight undefined $ handleTactic goal (Intro [])
    it "no name -- goal" $
      getGoalList nonameAns `shouldBe`
      [ Goal 1 (("T",VarBind TmType):realEqContext)
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))]
    it "no name -- func" $
      getResultFunc nonameAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T" TmType (TmVar "Goal1")
    let onenameAns = fromRight undefined $ handleTactic goal (Intro ["T1"])
    it "one name -- goal" $
      getGoalList onenameAns `shouldBe`
      [ Goal 1 (("T1",VarBind TmType):realEqContext)
        ( TmProd "_"
          ( TmRel "T1" 0 )
          ( TmProd "m"
            ( TmRel "T1" 1 )
            ( TmIndType "eq"
              [ TmRel "T1" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))]
    it "one name -- func" $
      getResultFunc onenameAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T1" TmType (TmVar "Goal1")
    let twonamesAns = fromRight undefined $ handleTactic goal (Intro ["T1","m"])
    it "two names -- goal" $
      getGoalList twonamesAns `shouldBe`
      [ Goal 2 (("m",VarBind (TmRel "T1" 0)):("T1",VarBind TmType):realEqContext)
        ( TmProd "m0"
          ( TmRel "T1" 1 )
          ( TmIndType "eq"
            [ TmRel "T1" 2
            , TmRel "m0" 0
            , TmRel "m0" 0 ]))]
    it "two names -- func" $
      getResultFunc twonamesAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T1" TmType (TmLambda "m" (TmRel "T1" 0) (TmVar "Goal1"))
    it "four names -- should fail" $
      handleTactic goal (Intro ["a","b","c","d"]) `shouldSatisfy`
      (\case
        Left (TacticError str) -> str == "No enough products"
        Right _ -> False)
  describe "intros" $ do
    let
      goal = Goal 0 realEqContext $
        TmProd "T"
          TmType
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))
      allinoneAns = fromRight undefined $ handleTactic goal Intros
    it "all in one -- goal" $
      getGoalList allinoneAns `shouldBe`
      [ Goal 3 (("m",VarBind (TmRel "T" 1)):("t",VarBind (TmRel "T" 0)):("T",VarBind TmType):realEqContext)
        ( TmIndType "eq"
          [ TmRel "T" 2
          , TmRel "m" 0
          , TmRel "m" 0 ])]
    it "all in one -- func" $
      getResultFunc allinoneAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T" TmType (TmLambda "t" (TmRel "T" 0) (TmLambda "m" (TmRel "T" 1) (TmVar "Goal1")))
  describe "destruct" $ do
    let
      eqmgoal = Goal 2
        ( ("m",VarBind (TmIndType "nat" []))
        : ("n",VarBind (TmIndType "nat" []))
        : realNatContext)
        ( TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmRel "plus" 2
            , TmRel "n" 1
            , TmRel "m" 0 ]
          , TmAppl
            [ TmRel "plus" 2
            , TmRel "n" 1
            , TmRel "m" 0 ]])
      eqmfParam = 
        [ TmAppl
          [ TmConstr "eq_refl"
            [ TmIndType "nat" []
            , TmAppl
              [ TmRel "plus" 1
              , TmRel "n" 0
              , TmConstr "O" []]]]
        , TmMatch 0
          ( TmRel "n" 1 )
          "n0"
          ["nat"]
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmAppl
              [ TmRel "plus" 3
              , TmRel "n0" 0
              , TmConstr "S"
                [ TmRel "m0" 1 ]]
            , TmAppl
              [ TmRel "plus" 3
              , TmRel "n0" 0
              , TmConstr "S"
                [ TmRel "m0" 1 ]]])
          [ Equation
            [ "O" ]
            ( TmConstr "eq_refl"
              [ TmIndType "nat" []
              , TmAppl
                [ TmRel "plus" 2
                , TmConstr "O" []
                , TmConstr "S"
                  [ TmRel "m0" 0 ]]])
          , Equation
            [ "S", "n0" ]
            ( TmConstr "eq_refl"
              [ TmIndType "nat" []
              , TmAppl
                [ TmRel "plus" 3
                , TmConstr "S"
                  [ TmRel "n0" 0]
                , TmConstr "S"
                  [ TmRel "m0" 1]]])]]
      eqmResultTerm = TmMatch 0
        ( TmRel "m" 0 )
        "n0"
        ["nat"]
        ( TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmRel "plus" 3
            , TmRel "n" 2
            , TmRel "n0" 0 ]
          , TmAppl
            [ TmRel "plus" 3
            , TmRel "n" 2
            , TmRel "n0" 0 ]])
        [ Equation
          [ "O" ]
          ( TmAppl
            [ TmConstr "eq_refl"
              [ TmIndType "nat" []
              , TmAppl
                [ TmRel "plus" 2
                , TmRel "n" 1
                , TmConstr "O" []]]])
        , Equation
          [ "S", "m0" ]
          ( TmMatch 0
            ( TmRel "n" 2 )
            "n0"
            ["nat"]
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmAppl
                [ TmRel "plus" 4
                , TmRel "n0" 0
                , TmConstr "S"
                  [ TmRel "m0" 1 ]]
              , TmAppl
                [ TmRel "plus" 4
                , TmRel "n0" 0
                , TmConstr "S"
                  [ TmRel "m0" 1 ]]])
            [ Equation
              [ "O" ]
              ( TmConstr "eq_refl"
                [ TmIndType "nat" []
                , TmAppl
                  [ TmRel "plus" 3
                  , TmConstr "O" []
                  , TmConstr "S"
                    [ TmRel "m0" 0 ]]])
            , Equation
              [ "S", "n0" ]
              ( TmConstr "eq_refl"
                [ TmIndType "nat" []
                , TmAppl
                  [ TmRel "plus" 4
                  , TmConstr "S"
                    [ TmRel "n0" 0]
                  , TmConstr "S"
                    [ TmRel "m0" 1]]])])]
      eqmAns = fromRight undefined $ handleTactic eqmgoal (Destruct (TmRel "m" 0))
    it "eq m -- goal" $
      getGoalList eqmAns `shouldBe`
      [ Goal 1 (("n",VarBind (TmIndType "nat" [])):realPlusContext)
        ( TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmRel "plus" 2
            , TmRel "n" 1
            , TmConstr "O" [] ]
          , TmAppl
            [ TmRel "plus" 2
            , TmRel "n" 1
            , TmConstr "O" [] ]])
      , Goal 2 (("m0",VarBind (TmIndType "nat" [])):("n",VarBind (TmIndType "nat" [])):realPlusContext)
        ( TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmRel "plus" 2
            , TmRel "n" 1
            , TmConstr "S"
              [ TmRel "m0" 0 ]]
          , TmAppl
          [ TmRel "plus" 2
          , TmRel "n" 1
          , TmConstr "S"
            [ TmRel "m0" 0 ]]])]
            
