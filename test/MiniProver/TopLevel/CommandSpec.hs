module MiniProver.TopLevel.CommandSpec (main,spec) where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.TopLevel.Command
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "addEnvCommand" $ do
    describe "Ax" $
      it "simple" $
        addEnvCommand []
          ( Ax "dummy"
            ( TmProd "x"
                TmType
                TmType ))
        `shouldBe`
        [ ( "dummy"
          , TmAbbBind
            ( TmProd "x"
              TmType
              TmType )
            Nothing )]
    describe "Def" $
      it "simple" $
        addEnvCommand []
          ( Def "dummy"
            ( TmProd "T"
                TmType 
              ( TmProd "x"
                ( TmRel "T" 0 )
                ( TmRel "T" 1 )))
            ( TmLambda "T"
                TmType
              ( TmLambda "x"
                ( TmRel "T" 0 )
                ( TmRel "x" 0 ))))
        `shouldBe`
        [ ( "dummy"
          , TmAbbBind
            ( TmProd "T"
                TmType 
              ( TmProd "x"
                ( TmRel "T" 0 )
                ( TmRel "T" 1 )))
            ( Just
              ( TmLambda "T"
                  TmType
                ( TmLambda "x"
                  ( TmRel "T" 0 )
                  ( TmRel "x" 0 )))))]
    describe "Fix" $
      it "simple" $
        addEnvCommand ilistContext
          ( Fix "pluss"
            ( TmFix 1
              ( TmLambda "pluss"
                ( TmProd "a"
                  ( TmIndType "nat" [])
                  ( TmProd "b"
                    ( TmIndType "nat" [])
                    ( TmIndType "nat" [])))
                ( TmLambda "a"
                  ( TmIndType "nat" [])
                  ( TmLambda "b"
                    ( TmIndType "nat" [])
                    ( TmMatch 0
                      ( TmRel "a" 1 )
                        "a0"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "b" 0 )
                      , Equation
                        [ "S"
                        , "n" ]
                        ( TmAppl
                          [ TmLambda ".0"
                            ( TmIndType "nat" [])
                            ( TmConstr "S"
                              [ TmRel ".0" 0 ])
                          , TmAppl
                            [ TmRel "pluss" 3
                            , TmRel "n" 0
                            , TmRel "b" 1 ]])]))))))
        `shouldBe`
        ( "pluss"
        , TmAbbBind
          ( TmProd "a"
            ( TmIndType "nat" [] )
            ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] )))
          ( Just
            ( TmFix 1
              ( TmLambda "pluss"
                ( TmProd "a"
                  ( TmIndType "nat" [])
                  ( TmProd "b"
                    ( TmIndType "nat" [])
                    ( TmIndType "nat" [])))
                ( TmLambda "a"
                  ( TmIndType "nat" [])
                  ( TmLambda "b"
                    ( TmIndType "nat" [])
                    ( TmMatch 0
                      ( TmRel "a" 1 )
                        "a0"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "b" 0 )
                      , Equation
                        [ "S"
                        , "n" ]
                        ( TmConstr "S"
                          [ TmAppl
                            [ TmRel "pluss" 3
                            , TmRel "n" 0
                            , TmRel "b" 1 ]])]))))))) : ilistContext
    describe "Ind" $ do
      it "True" $
        addEnvCommand []
          ( Ind "True" 0
              TmType
            ( TmIndType "True" [])
            [ ( "I"
              , TmIndType "True" []
              , TmConstr "I" [])])
        `shouldBe` realTrueContext
      it "False" $
        addEnvCommand realTrueContext
          ( Ind "False" 0
              TmType
            ( TmIndType "False" [])
            [  ])
        `shouldBe` realFalseContext
      it "eq" $
        addEnvCommand realFalseContext
          ( Ind "eq" 2
            ( TmProd "T"
                TmType
              ( TmProd "x"
                ( TmRel "T" 0 )
                ( TmProd "_"
                  ( TmRel "T" 1 )
                    TmType )))
            ( TmLambda "T"
                TmType
              ( TmLambda "x"
                ( TmRel "T" 0 )
                ( TmLambda ".0"
                  ( TmRel "T" 1 )
                  ( TmIndType "eq"
                    [ TmRel "T" 2
                    , TmRel "x" 1
                    , TmRel ".0" 0 ]))))
            [ ( "eq_refl"
              , TmProd "T"
                  TmType
                ( TmProd "x"
                  ( TmRel "T" 0 )
                  ( TmIndType "eq"
                    [ TmRel "T" 1
                    , TmRel "x" 0
                    , TmRel "x" 0 ]))
              , TmLambda "T"
                  TmType
                ( TmLambda "x"
                  ( TmRel "T" 0 )
                  ( TmConstr "eq_refl"
                    [ TmRel "T" 1
                    , TmRel "x" 0 ])))])
        `shouldBe` realEqContext
      it "and" $
        addEnvCommand realEqContext
        ( Ind "and" 2
          ( TmProd "A"
              TmType
            ( TmProd "B"
                TmType
                TmType ))
          ( TmLambda "A"
              TmType
            ( TmLambda "B"
                TmType
              ( TmIndType "and"
                [ TmRel "A" 1
                , TmRel "B" 0 ])))
          [ ( "conj"
            , TmProd "A"
                TmType
              ( TmProd "B"
                  TmType
                ( TmProd "_"
                  ( TmRel "A" 1 )
                  ( TmProd "_"
                    ( TmRel "B" 1 )
                    ( TmIndType "and"
                      [ TmRel "A" 3
                      , TmRel "B" 2 ]))))
            , TmLambda "A"
                TmType
              ( TmLambda "B"
                  TmType
                ( TmLambda ".0"
                  ( TmRel "A" 1 )
                  ( TmLambda ".1"
                    ( TmRel "B" 1 )
                    ( TmConstr "conj"
                      [ TmRel "A" 3
                      , TmRel "B" 2
                      , TmRel ".0" 1
                      , TmRel ".1" 0 ])))))])
        `shouldBe` realAndContext
      it "or" $
        addEnvCommand realAndContext
        ( Ind "or" 2
          ( TmProd "A"
              TmType
            ( TmProd "B"
                TmType
                TmType ))
          ( TmLambda "A"
              TmType
            ( TmLambda "B"
                TmType
              ( TmIndType "or"
                [ TmRel "A" 1
                , TmRel "B" 0 ])))
          [ ( "or_introl"
            , TmProd "A"
                TmType
              ( TmProd "B"
                  TmType
                ( TmProd "_"
                  ( TmRel "A" 1 )
                  ( TmIndType "or"
                    [ TmRel "A" 2
                    , TmRel "B" 1 ])))
            , TmLambda "A"
                TmType
              ( TmLambda "B"
                  TmType
                ( TmLambda ".0"
                  ( TmRel "A" 1 )
                  ( TmConstr "or_introl"
                    [ TmRel "A" 2
                    , TmRel "B" 1
                    , TmRel ".0" 0 ]))))
          , ( "or_intror"
            , TmProd "A"
                TmType
              ( TmProd "B"
                  TmType
                ( TmProd "_"
                  ( TmRel "B" 0 )
                  ( TmIndType "or"
                    [ TmRel "A" 2
                    , TmRel "B" 1 ])))
            , TmLambda "A"
                TmType
              ( TmLambda "B"
                  TmType
                ( TmLambda ".0"
                  ( TmRel "B" 0 )
                  ( TmConstr "or_intror"
                    [ TmRel "A" 2
                    , TmRel "B" 1
                    , TmRel ".0" 0 ]))))])
        `shouldBe` realOrContext
      it "nat" $
        addEnvCommand realOrContext
        ( Ind "nat" 0
          TmType
        ( TmIndType "nat" [])
        [ ( "O"
          , TmIndType "nat" []
          , TmConstr "O" [])
        , ( "S"
          , TmProd "_"
            ( TmIndType "nat" [])
            ( TmIndType "nat" [])
          , TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ]))])
        `shouldBe` realNatContext
      it "natlist" $
        addEnvCommand realNatContext
        ( Ind "natlist" 0
          TmType
        ( TmIndType "natlist" [])
        [ ( "natnil"
          , TmIndType "natlist" []
          , TmConstr "natnil" [])
        , ( "natcons"
          , TmProd "_"
            ( TmIndType "nat" [])
            ( TmProd "_"
              ( TmIndType "natlist" [])
              ( TmIndType "natlist" []))
          , TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmLambda ".1"
              ( TmIndType "natlist" [])
              ( TmConstr "natcons"
                [ TmRel ".0" 1
                , TmRel ".1" 0 ])))])
        `shouldBe` realNatlistContext
      it "list" $
        addEnvCommand realNatlistContext
        ( Ind "list" 1
          ( TmProd "T"
              TmType
              TmType )
          ( TmLambda "T"
              TmType
            ( TmIndType "list"
              [ TmRel "T" 0 ]))
          [ ( "nil"
            , TmProd "T"
                TmType
              ( TmIndType "list"
                [ TmRel "T" 0 ])
            , TmLambda "T"
                TmType
              ( TmConstr "nil"
                [ TmRel "T" 0 ]))
          , ( "cons"
            , TmProd "T"
                TmType
              ( TmProd "_"
                ( TmRel "T" 0 )
                ( TmProd "_"
                  ( TmIndType "list"
                    [ TmRel "T" 1 ])
                  ( TmIndType "list"
                    [ TmRel "T" 2 ])))
            , TmLambda "T"
                TmType
              ( TmLambda ".0"
                ( TmRel "T" 0 )
                ( TmLambda ".1"
                  ( TmIndType "list"
                    [ TmRel "T" 1 ])
                  ( TmConstr "cons"
                    [ TmRel "T" 2
                    , TmRel ".0" 1
                    , TmRel ".1" 0 ]))))])
        `shouldBe` realListContext
      it "ilist" $
        addEnvCommand realListContext
        ( Ind "ilist" 1
          ( TmProd "T"
              TmType
            ( TmProd "_"
              ( TmIndType "nat" [])
                TmType ))
          ( TmLambda "T"
              TmType
            ( TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmIndType "ilist"
                [ TmRel "T" 1
                , TmRel ".0" 0 ])))
          [ ( "inil"
            , TmProd "T"
                TmType
              ( TmIndType "ilist"
                [ TmRel "T" 0
                , TmConstr "O" []])
            , TmLambda "T"
                TmType
              ( TmConstr "inil"
                [ TmRel "T" 0 ]))
          , ( "icons"
            , TmProd "T"
                TmType
              ( TmProd "n"
                ( TmIndType "nat" [])
                ( TmProd "_"
                  ( TmRel "T" 1 )
                  ( TmProd "_"
                    ( TmIndType "ilist"
                      [ TmRel "T" 2
                      , TmRel "n" 1 ])
                    ( TmIndType "ilist"
                      [ TmRel "T" 3
                      , TmAppl
                        [ TmLambda "n"
                          ( TmIndType "nat" [])
                          ( TmConstr "S"
                            [ TmRel "n" 0 ])
                        , TmRel "n" 2 ]]))))
            , TmLambda "T"
                TmType
              ( TmLambda "n"
                ( TmIndType "nat" [])
                ( TmLambda ".0"
                  ( TmRel "T" 1 )
                  ( TmLambda ".1"
                    ( TmIndType "ilist"
                      [ TmRel "T" 2
                      , TmRel "n" 1 ])
                    ( TmConstr "icons"
                      [ TmRel "T" 3
                      , TmRel "n" 2
                      , TmRel ".0" 1
                      , TmRel ".1" 0 ])))))])
        `shouldBe` realIlistContext
      it "ex" $
        addEnvCommand realIlistContext
        ( Ind "ex" 2
          ( TmProd "A"
              TmType
            ( TmProd "P"
              ( TmProd "_"
                ( TmRel "A" 0 )
                  TmType )
                TmType ))
          ( TmLambda "A"
              TmType
            ( TmLambda "P"
              ( TmProd "_"
                ( TmRel "A" 0 )
                  TmType )
              ( TmIndType "ex"
                [ TmRel "A" 1
                , TmRel "P" 0 ])))
          [ ( "ex_intro"
            , TmProd "A"
                TmType
              ( TmProd "P"
                ( TmProd "_"
                  ( TmRel "A" 0 )
                    TmType )
                ( TmProd "x"
                  ( TmRel "A" 1 )
                  ( TmProd "_"
                    ( TmAppl
                      [ TmRel "P" 1
                      , TmRel "x" 0 ])
                    ( TmIndType "ex"
                      [ TmRel "A" 3
                      , TmRel "P" 2 ]))))
            , TmLambda "A"
                TmType
              ( TmLambda "P"
                ( TmProd "_"
                  ( TmRel "A" 0 )
                    TmType )
                ( TmLambda "x"
                  ( TmRel "A" 1 )
                  ( TmLambda ".0"
                    ( TmAppl
                      [ TmRel "P" 1
                      , TmRel "x" 0 ])
                    ( TmConstr "ex_intro"
                      [ TmRel "A" 3
                      , TmRel "P" 2
                      , TmRel "x" 1
                      , TmRel ".0" 0 ])))))])
        `shouldBe` realExContext
      it "ex2" $
        addEnvCommand realExContext
        ( Ind "ex2" 3
        ( TmProd "A"
            TmType
          ( TmProd "P"
            ( TmProd "_"
              ( TmRel "A" 0 )
                TmType )
            ( TmProd "Q"
              ( TmProd "_"
                ( TmRel "A" 1 )
                  TmType )
                TmType )))
        ( TmLambda "A"
            TmType
          ( TmLambda "P"
            ( TmProd "_"
              ( TmRel "A" 0 )
                TmType )
            ( TmLambda "Q"
              ( TmProd "_"
                ( TmRel "A" 1 )
                  TmType )
              ( TmIndType "ex2"
                [ TmRel "A" 2
                , TmRel "P" 1
                , TmRel "Q" 0 ]))))
        [ ( "ex_intro2"
          , TmProd "A"
              TmType
            ( TmProd "P"
              ( TmProd "_"
                ( TmRel "A" 0 )
                  TmType )
              ( TmProd "Q"
                ( TmProd "_"
                  ( TmRel "A" 1 )
                    TmType )
                ( TmProd "x"
                  ( TmRel "A" 2 )
                  ( TmProd "_"
                    ( TmAppl
                      [ TmRel "P" 2
                      , TmRel "x" 0 ])
                    ( TmProd "_"
                      ( TmAppl
                        [ TmRel "Q" 2
                        , TmRel "x" 1 ])
                      ( TmIndType "ex2"
                        [ TmRel "A" 5
                        , TmRel "P" 4
                        , TmRel "Q" 3 ]))))))
          , TmLambda "A"
              TmType
            ( TmLambda "P"
              ( TmProd "_"
                ( TmRel "A" 0 )
                  TmType )
              ( TmLambda "Q"
                ( TmProd "_"
                  ( TmRel "A" 1 )
                    TmType )
                ( TmLambda "x"
                  ( TmRel "A" 2 )
                  ( TmLambda ".0"
                    ( TmAppl
                      [ TmRel "P" 2
                      , TmRel "x" 0 ])
                    ( TmLambda ".1"
                      ( TmAppl
                        [ TmRel "Q" 2
                        , TmRel "x" 1 ])
                      ( TmConstr "ex_intro2"
                        [ TmRel "A" 5
                        , TmRel "P" 4
                        , TmRel "Q" 3
                        , TmRel "x" 2
                        , TmRel ".0" 1
                        , TmRel ".1" 0 ])))))))])
        `shouldBe` realEx2Context
