module MiniProver.Core.BuildSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Build
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "buildTerm" $ do
    let ctx = simpleContext
    describe "TmVar" $ do
      it "top" $
        buildTerm (TmVar "A") ctx `shouldBe` TmRel "A" 0
      it "tail" $
        buildTerm (TmVar "D") ctx `shouldBe` TmRel "D" 3
      let ctxInd = ("nat", IndTypeBind 0 TmType (TmIndType "nat" [])
                           [ Constructor "O" (TmIndType "nat" []) (TmConstr "O" [])
                           , Constructor "S" 
                               (TmProd "_" (TmIndType "nat" []) (TmIndType "nat" []))
                               (TmLambda ".0" (TmIndType "nat" []) (TmConstr "S" [TmRel ".0" 0]))]) : ctx
      it "type constructor" $
        buildTerm (TmVar "nat") ctxInd `shouldBe` TmIndType "nat" []
      it "constructor" $
        buildTerm (TmVar "S") ctxInd `shouldBe` 
          TmLambda ".0"
            ( TmIndType "nat" [] )
            ( TmConstr "S" [ TmRel ".0" 0 ])
    describe "TmAppl" $ do
      it "simple" $
        buildTerm (TmAppl [TmVar "A", TmVar "B", TmVar "C", TmVar "D"]) ctx
        `shouldBe`
        TmAppl 
          [ TmRel "A" 0
          , TmRel "B" 1
          , TmRel "C" 2
          , TmRel "D" 3]
      it "flatten" $
        buildTerm 
        ( TmAppl 
          [ TmAppl 
            [ TmAppl 
              [ TmVar "A", 
                TmAppl 
                [ TmVar "B"
                , TmVar "A" ]
              , TmVar "C" ]
            , TmVar "D" ]]) ctx
        `shouldBe`
        TmAppl
        [ TmRel "A" 0
        , TmAppl
          [ TmRel "B" 1
          , TmRel "A" 0 ]
        , TmRel "C" 2
        , TmRel "D" 3 ]
    describe "TmProd" $
      it "all in one" $
        buildTerm 
          (TmProd "x" (TmVar "A") (TmAppl [TmVar "A", TmVar "x"]))
          ctx
        `shouldBe`
        TmProd "x" (TmRel "A" 0) (TmAppl [TmRel "A" 1, TmRel "x" 0])
    describe "TmLambda" $
      it "all in one" $
        buildTerm 
          (TmLambda "x" (TmVar "A") (TmAppl [TmVar "A", TmVar "x"]))
          ctx
        `shouldBe`
        TmLambda "x" (TmRel "A" 0) (TmAppl [TmRel "A" 1, TmRel "x" 0])
    describe "TmFix" $
      it "all in one" $
        buildTerm (TmFix (-1) (TmVar "A")) ctx
        `shouldBe`
        TmFix (-1) (TmRel "A" 0)
    describe "TmLetIn" $
      it "all in one" $
        buildTerm
          (TmLetIn "x"
            (TmVar "A")
            (TmVar "B")
            (TmAppl [TmVar "A", TmVar "x"]))
          ctx
        `shouldBe`
        TmLetIn "x"
          (TmRel "A" 0)
          (TmRel "B" 1)
          (TmAppl [TmRel "A" 1, TmRel "x" 0])
    describe "TmIndType" $
      it "inside" $
        buildTerm
          (TmIndType "name" [TmVar "A", TmVar "D"])
          ctx
          `shouldBe`
          TmIndType "name" [TmRel "A" 0, TmRel "D" 3]
    describe "TmConstr" $
      it "inside" $
        buildTerm
          (TmConstr "name" [TmVar "A", TmVar "D"])
          ctx
          `shouldBe`
          TmConstr "name" [TmRel "A" 0, TmRel "D" 3]
    describe "TmType" $
      it "Type" $
        buildTerm TmType ctx `shouldBe` TmType
    describe "TmMatch" $ do
      it "nat" $
        buildTerm
          (TmMatch (-1) (TmVar "one")
            "x0"
            [ "nat" ]
            (TmVar "nat")
            [ Equation ["O"] (TmVar "two")
            , Equation ["S", "n"]
              (TmAppl
                [ TmVar "plus"
                , TmAppl [TmVar "S", TmVar "O"], TmVar "n"])])
          natContextWithPredefinedNumbers
          `shouldBe`
          TmMatch 0 (TmRel "one" 1)
            "x0"
            [ "nat" ]
            (TmIndType "nat" [])
            [ Equation ["O"] (TmRel "two" 0)
            , Equation ["S", "n"]
              (TmAppl
                [ TmRel "plus" 4
                , TmAppl
                  [ TmLambda ".0"
                    ( TmIndType "nat" [] )
                    ( TmConstr "S" [ TmRel ".0" 0 ])
                  , TmConstr "O" []]
                , TmRel "n" 0])]
      it "eq" $
        buildTerm
          ( TmMatch (-1)
            ( TmAppl
              [ TmVar "eq"
              , TmVar "nat"
              , TmVar "one"
              , TmVar "one" ])
            "H0"
            [ "eq", "_", "a", "b" ]
            ( TmAppl
              [ TmVar "eq"
              , TmVar "nat"
              , TmAppl
                [ TmVar "S"
                , TmVar "a"]
              , TmAppl
                [ TmVar "S"
                , TmVar "b" ]])
            [ Equation ["eqrefl", "_", "t"]
              ( TmAppl
                [ TmVar "eqrefl"
                , TmVar "nat"
                , TmAppl
                  [ TmVar "S"
                  , TmVar "t" ]])])
          natContextWithPredefinedNumbers
          `shouldBe`
          TmMatch 1
            ( TmAppl
              [ TmLambda "a"
                  TmType
                ( TmLambda ".0"
                  ( TmRel "a" 0 )
                  ( TmLambda ".1" 
                    ( TmRel "a" 1 )
                    ( TmIndType "eq"
                      [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ])))
              , TmIndType "nat" []
              , TmRel "one" 1
              , TmRel "one" 1 ])
            "H0"
            [ "eq", "_", "a", "b" ]
            ( TmAppl
              [ TmLambda "a"
                  TmType
                  ( TmLambda ".0"
                    ( TmRel "a" 0 )
                    ( TmLambda ".1" 
                      ( TmRel "a" 1 )
                      ( TmIndType "eq"
                      [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ])))
              , TmIndType "nat" []
              , TmAppl
                [ TmLambda ".0"
                  ( TmIndType "nat" [] )
                  ( TmConstr "S" [ TmRel ".0" 0 ])
                , TmRel "a" 2 ]
              , TmAppl
                [ TmLambda ".0"
                  ( TmIndType "nat" [] )
                  ( TmConstr "S" [ TmRel ".0" 0 ])
                , TmRel "b" 1 ]])
            [ Equation ["eqrefl", "_", "t"]
              ( TmAppl
                [ TmLambda "a" 
                    TmType
                  ( TmLambda "x"
                    ( TmRel "a" 0 )
                    ( TmConstr "eqrefl"
                      [ TmRel "a" 1, TmRel "x" 0 ]))
                , TmIndType "nat" []
                , TmAppl
                  [ TmLambda ".0"
                    ( TmIndType "nat" [] )
                    ( TmConstr "S" [ TmRel ".0" 0 ])
                  , TmRel "t" 0 ]])]
      it "eqrefl" $
        buildTerm
        ( TmMatch (-1)
          ( TmAppl
            [ TmVar "eqrefl"
            , TmVar "nat"
            , TmVar "one" ])
          "x0"
          ["eq","_","b","c"]
          ( TmAppl
            [ TmVar "eq"
            , TmVar "nat"
            , TmVar "c"
            , TmVar "b" ])
          [ Equation ["eqrefl","_","t"]
            ( TmAppl [ TmVar "eqrefl", TmVar "nat", TmVar "t" ])])
        natContextWithPredefinedNumbers
        `shouldBe`
        TmMatch 1
        ( TmAppl
          [ TmLambda "a" 
              TmType
            ( TmLambda "x"
              ( TmRel "a" 0 )
              ( TmConstr "eqrefl"
                [ TmRel "a" 1, TmRel "x" 0 ]))
          , TmIndType "nat" []
          , TmRel "one" 1 ])
        "x0"
        ["eq","_","b","c"]
        ( TmAppl
          [ TmLambda "a"
              TmType
            ( TmLambda ".0"
              ( TmRel "a" 0 )
              ( TmLambda ".1" 
                ( TmRel "a" 1 )
                ( TmIndType "eq"
                  [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ])))
          , TmIndType "nat" []
          , TmRel "c" 1
          , TmRel "b" 2 ])
        [ Equation ["eqrefl","_","t"]
          ( TmAppl
            [ TmLambda "a" 
                TmType
              ( TmLambda "x"
                ( TmRel "a" 0 )
                ( TmConstr "eqrefl"
                  [ TmRel "a" 1, TmRel "x" 0 ]))
            , TmIndType "nat" []
            , TmRel "t" 0 ])]
      it "dependent on term" $
        buildTerm
          ( TmMatch (-1)
            ( TmVar "one" )
            "x0"
            ["nat"]
            ( TmAppl
              [ TmVar "eq"
              , TmVar "nat"
              , TmVar "x0"
              , TmVar "x0" ])
            [ Equation ["O"]
              ( TmAppl
                [ TmVar "eqrefl"
                , TmVar "nat"
                , TmVar "O" ])
            , Equation ["S","n"]
              ( TmAppl
                [ TmVar "eqrefl"
                , TmVar "nat"
                , TmAppl
                  [ TmVar "S"
                  , TmVar "n" ]])])
          natContextWithPredefinedNumbers
          `shouldBe`
          TmMatch 0
          ( TmRel "one" 1 )
          "x0"
          ["nat"]
          ( TmAppl
            [ TmLambda "a"
                TmType
              ( TmLambda ".0"
                ( TmRel "a" 0 )
                ( TmLambda ".1" 
                  ( TmRel "a" 1 )
                  ( TmIndType "eq"
                    [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ])))
            , TmIndType "nat" []
            , TmRel "x0" 0
            , TmRel "x0" 0 ])
          [ Equation ["O"]
            ( TmAppl
              [ TmLambda "a" 
                  TmType
                ( TmLambda "x"
                  ( TmRel "a" 0 )
                  ( TmConstr "eqrefl"
                    [ TmRel "a" 1, TmRel "x" 0 ]))
              , TmIndType "nat" []
              , TmConstr "O" [] ])
          , Equation ["S","n"]
            ( TmAppl
              [ TmLambda "a" 
                  TmType
                ( TmLambda "x"
                  ( TmRel "a" 0 )
                  ( TmConstr "eqrefl"
                    [ TmRel "a" 1, TmRel "x" 0 ]))
              , TmIndType "nat" []
              , TmAppl
                [ TmLambda ".0"
                  ( TmIndType "nat" [] )
                  ( TmConstr "S" [ TmRel ".0" 0 ])
                , TmRel "n" 0 ]])]
  describe "buildCommand" $ do
    let ctx = natContext
    describe "Ax" $
      it "pluscomm" $
        buildCommand
          ( Ax "pluscomm"
            ( TmProd "a"
              ( TmVar "nat")
              ( TmProd "b"
                ( TmVar "nat")
                ( TmAppl
                  [ TmVar "eq"
                  , TmVar "nat"
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "a"
                    , TmVar "b" ]
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "b"
                    , TmVar "a" ]]))))
          ctx
          `shouldBe`
          Ax "pluscomm"
          ( TmProd "a"
            ( TmIndType "nat" [] )
            ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmAppl
                [ TmLambda "a"
                    TmType
                  ( TmLambda ".0"
                    ( TmRel "a" 0 )
                    ( TmLambda ".1" 
                      ( TmRel "a" 1 )
                      ( TmIndType "eq"
                        [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ])))
                , TmIndType "nat" []
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "a" 1
                  , TmRel "b" 0 ]
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "b" 0
                  , TmRel "a" 1 ]])))
    describe "Def" $
      it "pluscomm" $
        buildCommand
          ( Def "pluscomm"
            ( TmProd "a"
              ( TmVar "nat")
              ( TmProd "b"
                ( TmVar "nat")
                ( TmAppl
                  [ TmVar "eq"
                  , TmVar "nat"
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "a"
                    , TmVar "b" ]
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "b"
                    , TmVar "a" ]])))
            ( TmLambda "a" 
              ( TmVar "nat" ) 
              ( TmLambda "b"
                ( TmVar "nat" )
                ( TmAppl
                  [ TmVar "eqrefl"
                  , TmVar "nat"
                  , TmAppl 
                    [ TmVar "plus"
                    , TmVar "a"
                    , TmVar "b" ]
                  , TmAppl 
                    [ TmVar "plus"
                    , TmVar "b"
                    , TmVar "a"]]))))
          ctx
          `shouldBe`
          Def "pluscomm"
          ( TmProd "a"
            ( TmIndType "nat" [] )
            ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmAppl
                [ TmLambda "a"
                    TmType
                  ( TmLambda ".0"
                    ( TmRel "a" 0 )
                    ( TmLambda ".1" 
                      ( TmRel "a" 1 )
                      ( TmIndType "eq"
                        [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ])))
                , TmIndType "nat" []
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "a" 1
                  , TmRel "b" 0 ]
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "b" 0
                  , TmRel "a" 1 ]])))
          ( TmLambda "a" 
            ( TmIndType "nat" [] )
            ( TmLambda "b"
              ( TmIndType "nat" [] )
              ( TmAppl
                [ TmLambda "a" 
                    TmType
                  ( TmLambda "x"
                    ( TmRel "a" 0 )
                    ( TmConstr "eqrefl"
                      [ TmRel "a" 1, TmRel "x" 0 ]))
                , TmIndType "nat" []
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "a" 1
                  , TmRel "b" 0 ]
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "b" 0
                  , TmRel "a" 1 ]])))
    describe "Ind" $ do
      it "btree" $
        buildCommand
          (Ind "btree" 1
            (TmProd "x"
              TmType
              TmType)
            (TmLambda "x"
              TmType
              (TmIndType "btree" [TmVar "x"]))
            [ ( "leaf"
              , TmProd "x"
                  TmType
                  (TmProd "_"
                    (TmVar "x")
                    (TmIndType "btree" [TmVar "x"]))
              , TmLambda "x"
                  TmType
                  (TmLambda ".0"
                    (TmVar "x")
                    (TmConstr "leaf" [TmVar "x", TmVar ".0"])))
            , ( "node"
              , TmProd "x"
                TmType
                ( TmProd "_"
                  ( TmVar "x" )
                  ( TmProd "_"
                    ( TmIndType "btree" [TmVar "x"] )
                    ( TmProd "_"
                      ( TmIndType "btree" [TmVar "x"] )
                      ( TmIndType "btree" [TmVar "x"] ))))
              , TmLambda "x"
                TmType
                ( TmLambda ".0"
                  ( TmVar "x" )
                  ( TmLambda ".1"
                    ( TmIndType "btree" [TmVar "x"] )
                    ( TmLambda ".2"
                      ( TmIndType "btree" [TmVar "x"] )
                      ( TmConstr "node" [TmVar "x", TmVar ".0", TmVar ".1", TmVar ".2"])))))])
          ctx
          `shouldBe`
          Ind "btree" 1
            (TmProd "x"
              TmType
              TmType)
            (TmLambda "x"
              TmType
              (TmIndType "btree" [TmRel "x" 0]))
            [ ( "leaf"
              , TmProd "x"
                  TmType
                  (TmProd "_"
                    (TmRel "x" 0)
                    (TmIndType "btree" [TmRel "x" 1]))
              , TmLambda "x"
                  TmType
                  (TmLambda ".0"
                    (TmRel "x" 0)
                    (TmConstr "leaf" [TmRel "x" 1, TmRel ".0" 0 ])))
            , ( "node"
              , TmProd "x"
                TmType
                ( TmProd "_"
                  ( TmRel "x" 0 )
                  ( TmProd "_"
                    ( TmIndType "btree" [TmRel "x" 1] )
                    ( TmProd "_"
                      ( TmIndType "btree" [TmRel "x" 2] )
                      ( TmIndType "btree" [TmRel "x" 3] ))))
              , TmLambda "x"
                TmType
                ( TmLambda ".0"
                  ( TmRel "x" 0 )
                  ( TmLambda ".1"
                    ( TmIndType "btree" [TmRel "x" 1] )
                    ( TmLambda ".2"
                      ( TmIndType "btree" [TmRel "x" 2] )
                      ( TmConstr "node" [TmRel "x" 3, TmRel ".0" 2, TmRel ".1" 1, TmRel ".2" 0])))))]
      it "le" $
        buildCommand
          (Ind "le" 1
            (TmProd "x"
              (TmVar "nat")
              (TmProd "_"
                (TmVar "nat")
                TmType))
            (TmLambda "x"
              (TmVar "nat")
              (TmLambda ".0"
                (TmVar "nat")
                (TmIndType "le" [TmVar "x", TmVar ".0"])))
            [ ( "lerefl"
              , TmProd "x"
                  (TmVar "nat")
                  (TmIndType "le" [TmVar "x", TmVar "x"])
              , TmLambda "x"
                  (TmVar "nat")
                  (TmConstr "lerefl" [TmVar "x"]))
            , ( "leS"
              , TmProd "x"
                  (TmVar "nat")
                  (TmProd "y"
                    (TmVar "nat")
                    (TmProd "_"
                      (TmIndType "le" [TmVar "x", TmVar "y"])
                      (TmIndType "le" [TmVar "x", TmAppl [TmVar "S", TmVar "y"]])))
              , TmLambda "x"
                  (TmVar "nat")
                  (TmLambda "y"
                    (TmVar "nat")
                    (TmLambda ".0"
                      (TmIndType "le" [TmVar "x", TmVar "y"])
                      (TmConstr "leS" [TmVar "x", TmVar "y", TmVar ".0"]))))])
          ctx
          `shouldBe`
          Ind "le" 1
            (TmProd "x"
              (TmIndType "nat" [])
              (TmProd "_"
                (TmIndType "nat" [])
                TmType))
            (TmLambda "x"
              (TmIndType "nat" [])
              (TmLambda ".0"
                (TmIndType "nat" [])
                (TmIndType "le" [TmRel "x" 1, TmRel ".0" 0])))
            [ ( "lerefl"
              , TmProd "x"
                  (TmIndType "nat" [])
                  (TmIndType "le" [TmRel "x" 0, TmRel "x" 0])
              , TmLambda "x"
                  (TmIndType "nat" [])
                  (TmConstr "lerefl" [TmRel "x" 0]))
            , ( "leS"
              , TmProd "x"
                  (TmIndType "nat" [])
                  (TmProd "y"
                    (TmIndType "nat" [])
                    (TmProd "_"
                      (TmIndType "le" [TmRel "x" 1, TmRel "y" 0])
                      (TmIndType "le" 
                        [ TmRel "x" 2
                        , TmAppl 
                          [ TmLambda ".0"
                            ( TmIndType "nat" [] )
                            ( TmConstr "S" [ TmRel ".0" 0 ])
                        , TmRel "y" 1]])))
              , TmLambda "x"
                  (TmIndType "nat" [])
                  (TmLambda "y"
                    (TmIndType "nat" [])
                    (TmLambda ".0"
                      (TmIndType "le" [TmRel "x" 1, TmRel "y" 0])
                      (TmConstr "leS" [TmRel "x" 2, TmRel "y" 1, TmRel ".0" 0]))))]
    describe "Fix" $
      it "plus" $
        buildCommand
        ( Fix "plus"
          ( TmFix (-1)
            ( TmLambda "plus"
              ( TmProd "x"
                ( TmVar "nat" )
                ( TmProd "y"
                  ( TmVar "nat" )
                  ( TmVar "nat" )))
              ( TmLambda "x"
                ( TmVar "nat" )
                ( TmLambda "y"
                  ( TmVar "nat" )
                  ( TmMatch (-1)
                    ( TmVar "x" )
                    "x0"
                    [ "nat" ]
                    ( TmVar "nat" )
                    [ Equation
                      [ "O" ]
                      ( TmVar "y" )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmAppl
                        [ TmVar "S"
                        , TmAppl
                          [ TmVar "plus"
                          , TmVar "n"
                          , TmVar "y" ]])]))))))
        natContext
        `shouldBe`
        Fix "plus"
          ( TmFix (-1)
            ( TmLambda "plus"
              ( TmProd "x"
                ( TmIndType "nat" [])
                ( TmProd "y"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))
              ( TmLambda "x"
                ( TmIndType "nat" [])
                ( TmLambda "y"
                  ( TmIndType "nat" [])
                  ( TmMatch 0
                    ( TmRel "x" 1 )
                    "x0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "y" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmAppl
                        [ TmLambda ".0"
                          ( TmIndType "nat" [])
                          ( TmConstr "S"
                            [ TmRel ".0" 0 ])
                        , TmAppl
                          [ TmRel "plus" 3
                          , TmRel "n" 0
                          , TmRel "y" 1 ]])])))))
      