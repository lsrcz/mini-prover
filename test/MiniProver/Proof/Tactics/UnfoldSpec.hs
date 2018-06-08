module MiniProver.Proof.Tactics.UnfoldSpec where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Proof.HandleTactic
import MiniProver.Proof.ProofDef
import MiniProver.Utils.ContextForTesting
import Data.Either (fromRight)
import Debug.Trace

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "unfold" $ do
    let
      goal = Goal 2 
        (("b",VarBind $ TmIndType "nat" [])
        :("a",VarBind $ TmIndType "nat" [])
        :realPlusContext) $
        TmIndType "eq"
        [ TmIndType "nat" []
        , TmAppl
          [ TmRel "plus" 2
          , TmRel "a" 1
          , TmRel "b" 0]
        , TmAppl
          [ TmRel "plus" 2
          , TmRel "a" 1
          , TmRel "b" 0]]
      unfoldAns = fromRight undefined $ handleTactic goal (Unfold "plus" Nothing)
    it "plus -- goal" $
      getGoalList unfoldAns `shouldBe`
      [ Goal 2
        (("b",VarBind $ TmIndType "nat" [])
        :("a",VarBind $ TmIndType "nat" [])
        :realPlusContext) $
          TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmFix 1
              ( TmLambda "plus0"
                ( TmProd "a0"
                  ( TmIndType "nat" [])
                  ( TmProd "b0"
                    ( TmIndType "nat" [])
                    ( TmIndType "nat" [])))
                ( TmLambda "a0"
                  ( TmIndType "nat" [])
                  ( TmLambda "b0"
                    ( TmIndType "nat" [])
                    ( TmMatch 0
                      ( TmRel "a0" 1 )
                        "n"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "b0" 0 )
                      , Equation
                        [ "S"
                        , "n" ]
                        ( TmConstr "S"
                          [ TmAppl
                            [ TmRel "plus0" 3
                            , TmRel "n" 0
                            , TmRel "b0" 1 ]])]))))
            , TmRel "a" 1
            , TmRel "b" 0]
          , TmAppl
          [ TmFix 1
            ( TmLambda "plus0"
              ( TmProd "a0"
                ( TmIndType "nat" [])
                ( TmProd "b0"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))
              ( TmLambda "a0"
                ( TmIndType "nat" [])
                ( TmLambda "b0"
                  ( TmIndType "nat" [])
                  ( TmMatch 0
                    ( TmRel "a0" 1 )
                      "n"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "b0" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmConstr "S"
                        [ TmAppl
                          [ TmRel "plus0" 3
                          , TmRel "n" 0
                          , TmRel "b0" 1 ]])]))))
          , TmRel "a" 1
          , TmRel "b" 0]]]
    it "plus -- func" $
      getResultFunc unfoldAns
      [ TmConstr "eq_refl"
        [ TmIndType "nat" []
        , TmAppl
          [ TmFix 1
            ( TmLambda "plus0"
              ( TmProd "a0"
                ( TmIndType "nat" [])
                ( TmProd "b0"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))
              ( TmLambda "a0"
                ( TmIndType "nat" [])
                ( TmLambda "b0"
                  ( TmIndType "nat" [])
                  ( TmMatch 0
                    ( TmRel "a0" 1 )
                      "n"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "b0" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmConstr "S"
                        [ TmAppl
                          [ TmRel "plus0" 3
                          , TmRel "n" 0
                          , TmRel "b0" 1 ]])]))))
          , TmRel "a" 1
          , TmRel "b" 0]]]
      `shouldBe`
      TmConstr "eq_refl"
      [ TmIndType "nat" []
      , TmAppl
        [ TmFix 1
          ( TmLambda "plus0"
            ( TmProd "a0"
              ( TmIndType "nat" [])
              ( TmProd "b0"
                ( TmIndType "nat" [])
                ( TmIndType "nat" [])))
            ( TmLambda "a0"
              ( TmIndType "nat" [])
              ( TmLambda "b0"
                ( TmIndType "nat" [])
                ( TmMatch 0
                  ( TmRel "a0" 1 )
                    "n"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmRel "b0" 0 )
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmConstr "S"
                      [ TmAppl
                        [ TmRel "plus0" 3
                        , TmRel "n" 0
                        , TmRel "b0" 1 ]])]))))
        , TmRel "a" 1
        , TmRel "b" 0]]
    let
      goalplus1ctx = Goal 2 
        (("b",VarBind $ TmIndType "nat" [])
        :("a",VarBind $ TmIndType "nat" [])
        :realPlus1Context) $
        TmIndType "eq"
        [ TmIndType "nat" []
        , TmAppl
          [ TmRel "plus" 3
          , TmRel "a" 1
          , TmRel "b" 0]
        , TmAppl
          [ TmRel "plus" 3
          , TmRel "a" 1
          , TmRel "b" 0]]
      unfoldAns = fromRight undefined $ handleTactic goalplus1ctx (Unfold "plus" Nothing)
    it "plus in plus1ctx -- goal" $
      getGoalList unfoldAns `shouldBe`
      [ Goal 2
        (("b",VarBind $ TmIndType "nat" [])
        :("a",VarBind $ TmIndType "nat" [])
        :realPlus1Context) $
          TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmFix 1
              ( TmLambda "plus0"
                ( TmProd "a0"
                  ( TmIndType "nat" [])
                  ( TmProd "b0"
                    ( TmIndType "nat" [])
                    ( TmIndType "nat" [])))
                ( TmLambda "a0"
                  ( TmIndType "nat" [])
                  ( TmLambda "b0"
                    ( TmIndType "nat" [])
                    ( TmMatch 0
                      ( TmRel "a0" 1 )
                        "n"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "b0" 0 )
                      , Equation
                        [ "S"
                        , "n" ]
                        ( TmConstr "S"
                          [ TmAppl
                            [ TmRel "plus0" 3
                            , TmRel "n" 0
                            , TmRel "b0" 1 ]])]))))
            , TmRel "a" 1
            , TmRel "b" 0]
          , TmAppl
          [ TmFix 1
            ( TmLambda "plus0"
              ( TmProd "a0"
                ( TmIndType "nat" [])
                ( TmProd "b0"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))
              ( TmLambda "a0"
                ( TmIndType "nat" [])
                ( TmLambda "b0"
                  ( TmIndType "nat" [])
                  ( TmMatch 0
                    ( TmRel "a0" 1 )
                      "n"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "b0" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmConstr "S"
                        [ TmAppl
                          [ TmRel "plus0" 3
                          , TmRel "n" 0
                          , TmRel "b0" 1 ]])]))))
          , TmRel "a" 1
          , TmRel "b" 0]]]
    it "plus in plus1ctx -- func" $
      getResultFunc unfoldAns
      [ TmConstr "eq_refl"
        [ TmIndType "nat" []
        , TmAppl
          [ TmFix 1
            ( TmLambda "plus0"
              ( TmProd "a0"
                ( TmIndType "nat" [])
                ( TmProd "b0"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))
              ( TmLambda "a0"
                ( TmIndType "nat" [])
                ( TmLambda "b0"
                  ( TmIndType "nat" [])
                  ( TmMatch 0
                    ( TmRel "a0" 1 )
                      "n"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "b0" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmConstr "S"
                        [ TmAppl
                          [ TmRel "plus0" 3
                          , TmRel "n" 0
                          , TmRel "b0" 1 ]])]))))
          , TmRel "a" 1
          , TmRel "b" 0]]]
      `shouldBe`
      TmConstr "eq_refl"
      [ TmIndType "nat" []
      , TmAppl
        [ TmFix 1
          ( TmLambda "plus0"
            ( TmProd "a0"
              ( TmIndType "nat" [])
              ( TmProd "b0"
                ( TmIndType "nat" [])
                ( TmIndType "nat" [])))
            ( TmLambda "a0"
              ( TmIndType "nat" [])
              ( TmLambda "b0"
                ( TmIndType "nat" [])
                ( TmMatch 0
                  ( TmRel "a0" 1 )
                    "n"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmRel "b0" 0 )
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmConstr "S"
                      [ TmAppl
                        [ TmRel "plus0" 3
                        , TmRel "n" 0
                        , TmRel "b0" 1 ]])]))))
        , TmRel "a" 1
        , TmRel "b" 0]]
    let
      goalplus1 = Goal 2 
        (("b",VarBind $ TmIndType "nat" [])
        :("a",VarBind $ TmIndType "nat" [])
        :realPlus1Context) $
        TmIndType "eq"
        [ TmIndType "nat" []
        , TmAppl
          [ TmRel "plus1" 2
          , TmRel "a" 1
          , TmRel "b" 0]
        , TmAppl
          [ TmRel "plus1" 2
          , TmRel "a" 1
          , TmRel "b" 0]]
      unfoldAns = fromRight undefined $ handleTactic goalplus1ctx (Unfold "plus1" Nothing)
    it "plus1 -- goal" $
      getGoalList unfoldAns `shouldBe`
      [ Goal 2
        (("b",VarBind $ TmIndType "nat" [])
        :("a",VarBind $ TmIndType "nat" [])
        :realPlus1Context) $
          TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmRel "plus" 3
            , TmRel "a" 1
            , TmRel "b" 0]
          , TmAppl
          [ TmRel "plus" 3
          , TmRel "a" 1
          , TmRel "b" 0]]]
    it "plus -- func" $
      getResultFunc unfoldAns
      [ TmConstr "eq_refl"
        [ TmIndType "nat" []
        , TmAppl
          [ TmFix 1
            ( TmLambda "plus0"
              ( TmProd "a0"
                ( TmIndType "nat" [])
                ( TmProd "b0"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))
              ( TmLambda "a0"
                ( TmIndType "nat" [])
                ( TmLambda "b0"
                  ( TmIndType "nat" [])
                  ( TmMatch 0
                    ( TmRel "a0" 1 )
                      "n"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "b0" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmConstr "S"
                        [ TmAppl
                          [ TmRel "plus0" 3
                          , TmRel "n" 0
                          , TmRel "b0" 1 ]])]))))
          , TmRel "a" 1
          , TmRel "b" 0]]]
      `shouldBe`
      TmConstr "eq_refl"
      [ TmIndType "nat" []
      , TmAppl
        [ TmFix 1
          ( TmLambda "plus0"
            ( TmProd "a0"
              ( TmIndType "nat" [])
              ( TmProd "b0"
                ( TmIndType "nat" [])
                ( TmIndType "nat" [])))
            ( TmLambda "a0"
              ( TmIndType "nat" [])
              ( TmLambda "b0"
                ( TmIndType "nat" [])
                ( TmMatch 0
                  ( TmRel "a0" 1 )
                    "n"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmRel "b0" 0 )
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmConstr "S"
                      [ TmAppl
                        [ TmRel "plus0" 3
                        , TmRel "n" 0
                        , TmRel "b0" 1 ]])]))))
        , TmRel "a" 1
        , TmRel "b" 0]]
    let
      goalHypoPlus =
        Goal 3
        ( ( "H"
          , VarBind
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmAppl
                [ TmRel "plus" 3
                , TmRel "a" 1
                , TmRel "b" 0 ]
              , TmAppl
                [ TmRel "plus" 3
                , TmRel "a" 1
                , TmRel "b" 0 ]]))
        : ( "b"
          , VarBind
            ( TmIndType "nat" [] ))
        : ( "a"
          , VarBind
            ( TmIndType "nat" [] ))
        : realPlus1Context)
        ( TmIndType "nat" [] )
      hypoPlusAns = fromRight undefined $ handleTactic goalHypoPlus (Unfold "plus" (Just "H"))
    it "plus in H -- goal" $
      getGoalList hypoPlusAns
      `shouldBe`
      [ Goal 3
      ( ( "H"
          , VarBind
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmAppl
                [ TmFix 1
                ( TmLambda "plus0"
                  ( TmProd "a0"
                    ( TmIndType "nat" [])
                    ( TmProd "b0"
                      ( TmIndType "nat" [])
                      ( TmIndType "nat" [])))
                  ( TmLambda "a0"
                    ( TmIndType "nat" [])
                    ( TmLambda "b0"
                      ( TmIndType "nat" [])
                      ( TmMatch 0
                        ( TmRel "a0" 1 )
                          "n"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "b0" 0 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmConstr "S"
                            [ TmAppl
                              [ TmRel "plus0" 3
                              , TmRel "n" 0
                              , TmRel "b0" 1 ]])]))))
                , TmRel "a" 1
                , TmRel "b" 0 ]
              , TmAppl
                [ TmFix 1
                ( TmLambda "plus0"
                  ( TmProd "a0"
                    ( TmIndType "nat" [])
                    ( TmProd "b0"
                      ( TmIndType "nat" [])
                      ( TmIndType "nat" [])))
                  ( TmLambda "a0"
                    ( TmIndType "nat" [])
                    ( TmLambda "b0"
                      ( TmIndType "nat" [])
                      ( TmMatch 0
                        ( TmRel "a0" 1 )
                          "n"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "b0" 0 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmConstr "S"
                            [ TmAppl
                              [ TmRel "plus0" 3
                              , TmRel "n" 0
                              , TmRel "b0" 1 ]])]))))
                , TmRel "a" 1
                , TmRel "b" 0 ]]))
        : ( "b"
          , VarBind
            ( TmIndType "nat" [] ))
        : ( "a"
          , VarBind
            ( TmIndType "nat" [] ))
        : realPlus1Context)
        ( TmIndType "nat" [] )]
    it "plus in H -- func" $
      getResultFunc hypoPlusAns [TmConstr "O" []] `shouldBe` TmConstr "O" []
    let
      goalHypoPlusR =
        Goal 4
        ( ( "a0"
          , VarBind 
            ( TmIndType "nat" [] ))
        : ( "H"
          , VarBind
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmAppl
                [ TmRel "plus" 3
                , TmRel "a" 1
                , TmRel "b" 0 ]
              , TmAppl
                [ TmRel "plus" 3
                , TmRel "a" 1
                , TmRel "b" 0 ]]))
        : ( "b"
          , VarBind
            ( TmIndType "nat" [] ))
        : ( "a"
          , VarBind
            ( TmIndType "nat" [] ))
        : realPlus1Context)
        ( TmIndType "nat" [] )
      hypoPlusRAns = fromRight undefined $ handleTactic goalHypoPlusR (Unfold "plus" (Just "H"))
    it "plus in H with redundant head -- goal" $
      getGoalList hypoPlusRAns
      `shouldBe`
      [ Goal 4
      ( ( "a0"
        , VarBind 
          ( TmIndType "nat" [] ))
      : ( "H"
          , VarBind
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmAppl
                [ TmFix 1
                ( TmLambda "plus0"
                  ( TmProd "a1"
                    ( TmIndType "nat" [])
                    ( TmProd "b0"
                      ( TmIndType "nat" [])
                      ( TmIndType "nat" [])))
                  ( TmLambda "a1"
                    ( TmIndType "nat" [])
                    ( TmLambda "b0"
                      ( TmIndType "nat" [])
                      ( TmMatch 0
                        ( TmRel "a1" 1 )
                          "n"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "b0" 0 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmConstr "S"
                            [ TmAppl
                              [ TmRel "plus0" 3
                              , TmRel "n" 0
                              , TmRel "b0" 1 ]])]))))
                , TmRel "a" 1
                , TmRel "b" 0 ]
              , TmAppl
                [ TmFix 1
                ( TmLambda "plus0"
                  ( TmProd "a1"
                    ( TmIndType "nat" [])
                    ( TmProd "b0"
                      ( TmIndType "nat" [])
                      ( TmIndType "nat" [])))
                  ( TmLambda "a1"
                    ( TmIndType "nat" [])
                    ( TmLambda "b0"
                      ( TmIndType "nat" [])
                      ( TmMatch 0
                        ( TmRel "a1" 1 )
                          "n"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "b0" 0 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmConstr "S"
                            [ TmAppl
                              [ TmRel "plus0" 3
                              , TmRel "n" 0
                              , TmRel "b0" 1 ]])]))))
                , TmRel "a" 1
                , TmRel "b" 0 ]]))
        : ( "b"
          , VarBind
            ( TmIndType "nat" [] ))
        : ( "a"
          , VarBind
            ( TmIndType "nat" [] ))
        : realPlus1Context)
        ( TmIndType "nat" [] )]
    it "plus in H with redundant head -- func" $
      getResultFunc hypoPlusRAns [TmConstr "O" []] `shouldBe` TmConstr "O" []

