module MiniProver.Proof.Tactics.DestructSpec where

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
  describe "destruct" $ do
    let
      eqmgoal = Goal 2
        ( ("m",VarBind (TmIndType "nat" []))
        : ("n",VarBind (TmIndType "nat" []))
        : realPlusContext)
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
      eqmAns =  trace (show $ getGoalList <$> handleTactic eqmgoal (Destruct (TmRel "m" 0)))      fromRight undefined $ handleTactic eqmgoal (Destruct (TmRel "m" 0))
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
  
