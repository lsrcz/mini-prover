module MiniProver.Core.BuildSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Build

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "buildTerm" $ do
    let ctx = [("A", NameBind), ("B", NameBind), ("C", NameBind), ("D", NameBind)]
    describe "TmVar" $ do
      it "top" $
        buildTerm (TmVar "A") ctx `shouldBe` TmRel "A" 0
      it "tail" $
        buildTerm (TmVar "D") ctx `shouldBe` TmRel "D" 3
      let ctxInd = ("nat", IndTypeBind 0 (TmSort Set) (TmIndType "nat" [])
                           [ Constructor "O" (TmIndType "nat" []) (TmConstr "O" [])
                           , Constructor "S" 
                               (TmProd "_" (TmIndType "nat" []) (TmIndType "nat" []))
                               (TmLambda ".0" (TmIndType "nat" []) (TmConstr "S" [TmRel ".0" 0]))]) : ctx
      it "type constructor" $
        buildTerm (TmVar "nat") ctxInd `shouldBe` TmIndTypeRef "nat"
      it "constructor" $
        buildTerm (TmVar "S") ctxInd `shouldBe` TmConstrRef "S"
    describe "TmAppl" $
      it "all in one" $
        buildTerm (TmAppl [TmVar "A", TmVar "B", TmVar "C", TmVar "D"]) ctx
        `shouldBe`
        TmAppl 
          [ TmRel "A" 0
          , TmRel "B" 1
          , TmRel "C" 2
          , TmRel "D" 3]
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
        buildTerm (TmFix (TmVar "A")) ctx
        `shouldBe`
        TmFix (TmRel "A" 0)
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
    describe "TmSort" $
      it "Set" $
        buildTerm (TmSort Set) ctx `shouldBe` TmSort Set
    describe "TmMatch" $
      it "all in one" $
        buildTerm
          (TmMatch (TmVar "A")
            [ "a", "b", "c" ]
            (TmAppl [TmVar "A", TmVar "b", TmVar "c"])
            [ Equation ["a"] (TmVar "A")
            , Equation ["a", "b"] (TmAppl [TmVar "A", TmVar "D", TmVar "b"])
            , Equation ["a", "b", "c"] (TmAppl [TmVar "A", TmVar "b", TmVar "c"])])
          ctx
          `shouldBe`
          TmMatch (TmRel "A" 0)
            [ "a", "b", "c" ]
            (TmAppl [TmRel "A" 2, TmRel "b" 1, TmRel "c" 0])
            [ Equation ["a"] (TmRel "A" 0)
            , Equation ["a", "b"]
                (TmAppl [TmRel "A" 1, TmRel "D" 4, TmRel "b" 0])
            , Equation ["a", "b", "c"]
                (TmAppl [TmRel "A" 2, TmRel "b" 1, TmRel "c" 0])]
  describe "buildCommand" $ do
    let ctx = [ ( "plus"
                , TmAbbBind
                  ( TmProd "a"
                    ( TmIndType "nat" [] )
                    ( TmProd "b"
                      ( TmIndType "nat" [] )
                      ( TmIndType "nat" [] )))
                  ( Just
                    ( TmFix
                      ( TmLambda "plus"
                        ( TmProd "a"
                          ( TmIndType "nat" [] )
                          ( TmProd "b"
                            ( TmIndType "nat" [] )
                            ( TmIndType "nat" [] )))
                        ( TmLambda "a"
                          ( TmIndType "nat" [] )
                          ( TmLambda "b"
                            ( TmIndType "nat" [] )
                            ( TmMatch
                              ( TmRel "a" 1 )
                              [ "nat" ]
                              ( TmIndType "nat" [] )
                              [ Equation
                                [ "O" ]
                                ( TmRel "b" 0 )
                              , Equation
                                [ "S", "n" ]
                                ( TmAppl
                                  [ TmVar "plus"
                                  , TmVar "n"
                                  , TmAppl
                                    [ TmVar "S"
                                    , TmVar "b"]])])))))))
              , ( "nat"
                , IndTypeBind 0
                  ( TmSort Set )
                  ( TmIndType "nat" [] )
                  [ Constructor "O"
                    ( TmIndType "nat" [] )
                    ( TmConstr "O" [] )
                  , Constructor "S"
                    ( TmProd "_"
                      ( TmIndType "nat" [] )
                      ( TmIndType "nat" [] ))
                    (TmLambda ".0"
                      ( TmIndType "nat" [] )
                      ( TmConstr "S" [ TmRel ".0" 0 ]))])
              , ( "eq"
                , IndTypeBind 1
                  ( TmProd "a"
                    ( TmSort Type )
                    ( TmProd "_"
                      ( TmRel "a" 0 )
                      ( TmProd "_"
                        ( TmRel "a" 1 )
                        ( TmSort Prop ))))
                  ( TmLambda "a"
                    ( TmSort Type )
                    ( TmLambda ".0"
                      ( TmRel "a" 0 )
                      ( TmLambda ".1" 
                        ( TmRel "a" 1 )
                        ( TmIndType "eq"
                          [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ]))))
                  [ Constructor "eqrefl"
                    ( TmProd "a"
                      ( TmSort Type )
                      ( TmProd "x"
                        ( TmVar "a" )
                        ( TmIndType "eq"
                          [ TmRel "a" 1, TmRel "x" 0, TmRel "x" 0 ])))
                    ( TmLambda "a" 
                      ( TmSort Type )
                      ( TmLambda "x"
                        ( TmVar "a" )
                        ( TmConstr "eqrefl"
                          [ TmRel "a" 1, TmRel "x" 0 ])))])]
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
            ( TmIndTypeRef "nat")
            ( TmProd "b"
              ( TmIndTypeRef "nat")
              ( TmAppl
                [ TmIndTypeRef "eq"
                , TmIndTypeRef "nat"
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
            ( TmIndTypeRef "nat")
            ( TmProd "b"
              ( TmIndTypeRef "nat")
              ( TmAppl
                [ TmIndTypeRef "eq"
                , TmIndTypeRef "nat"
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "a" 1
                  , TmRel "b" 0 ]
                , TmAppl
                  [ TmRel "plus" 2
                  , TmRel "b" 0
                  , TmRel "a" 1 ]])))
          ( TmLambda "a" 
            ( TmIndTypeRef "nat" )
            ( TmLambda "b"
              ( TmIndTypeRef "nat" )
              ( TmAppl
                [ TmConstrRef "eqrefl"
                , TmIndTypeRef "nat"
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
              (TmSort Type)
              (TmSort Type))
            (TmLambda "x"
              (TmSort Type)
              (TmIndType "btree" [TmVar "x"]))
            [ ( "leaf"
              , TmProd "x"
                  (TmSort Type)
                  (TmProd "_"
                    (TmVar "x")
                    (TmIndType "btree" [TmVar "x"]))
              , TmLambda "x"
                  (TmSort Type)
                  (TmLambda ".0"
                    (TmVar "x")
                    (TmConstr "leaf" [TmVar "x", TmVar ".0"])))
            , ( "node"
              , TmProd "x"
                ( TmSort Type )
                ( TmProd "_"
                  ( TmVar "x" )
                  ( TmProd "_"
                    ( TmIndType "btree" [TmVar "x"] )
                    ( TmProd "_"
                      ( TmIndType "btree" [TmVar "x"] )
                      ( TmIndType "btree" [TmVar "x"] ))))
              , TmLambda "x"
                ( TmSort Type )
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
              (TmSort Type)
              (TmSort Type))
            (TmLambda "x"
              (TmSort Type)
              (TmIndType "btree" [TmRel "x" 0]))
            [ ( "leaf"
              , TmProd "x"
                  (TmSort Type)
                  (TmProd "_"
                    (TmRel "x" 0)
                    (TmIndType "btree" [TmRel "x" 1]))
              , TmLambda "x"
                  (TmSort Type)
                  (TmLambda ".0"
                    (TmRel "x" 0)
                    (TmConstr "leaf" [TmRel "x" 1, TmRel ".0" 0 ])))
            , ( "node"
              , TmProd "x"
                ( TmSort Type )
                ( TmProd "_"
                  ( TmRel "x" 0 )
                  ( TmProd "_"
                    ( TmIndType "btree" [TmRel "x" 1] )
                    ( TmProd "_"
                      ( TmIndType "btree" [TmRel "x" 2] )
                      ( TmIndType "btree" [TmRel "x" 3] ))))
              , TmLambda "x"
                ( TmSort Type )
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
                (TmSort Prop)))
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
              (TmIndTypeRef "nat")
              (TmProd "_"
                (TmIndTypeRef "nat")
                (TmSort Prop)))
            (TmLambda "x"
              (TmIndTypeRef "nat")
              (TmLambda ".0"
                (TmIndTypeRef "nat")
                (TmIndType "le" [TmRel "x" 1, TmRel ".0" 0])))
            [ ( "lerefl"
              , TmProd "x"
                  (TmIndTypeRef "nat")
                  (TmIndType "le" [TmRel "x" 0, TmRel "x" 0])
              , TmLambda "x"
                  (TmIndTypeRef "nat")
                  (TmConstr "lerefl" [TmRel "x" 0]))
            , ( "leS"
              , TmProd "x"
                  (TmIndTypeRef "nat")
                  (TmProd "y"
                    (TmIndTypeRef "nat")
                    (TmProd "_"
                      (TmIndType "le" [TmRel "x" 1, TmRel "y" 0])
                      (TmIndType "le" [TmRel "x" 2, TmAppl [TmConstrRef "S", TmRel "y" 1]])))
              , TmLambda "x"
                  (TmIndTypeRef "nat")
                  (TmLambda "y"
                    (TmIndTypeRef "nat")
                    (TmLambda ".0"
                      (TmIndType "le" [TmRel "x" 1, TmRel "y" 0])
                      (TmConstr "leS" [TmRel "x" 2, TmRel "y" 1, TmRel ".0" 0]))))]