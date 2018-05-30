module MiniProver.Core.ContextSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Utils.ContextForTesting
import Data.List (sort)

main :: IO ()
main = hspec spec

spec :: Spec
spec = 
  describe "context" $ do
    describe "emptyContext" $
      it "empty context should be empty" $
        emptyContext `shouldBe` []
    describe "ctxLength" $ do
      it "empty" $
        ctxLength emptyContext `shouldBe` 0
      it "some bindings" $
        ctxLength [("a", NameBind), ("b", NameBind)] `shouldBe` 2
    describe "addBinding" $ do
      it "empty" $
        addBinding emptyContext "a" NameBind `shouldBe` [("a", NameBind)]
      it "adding to the head" $
        addBinding [("a", NameBind)] "b" NameBind `shouldBe` [("b", NameBind), ("a", NameBind)]
    describe "addName" $ do
      it "empty" $
        addName emptyContext "a" `shouldBe` [("a", NameBind)]
      it "adding to the head" $
        addName [("a", NameBind)] "b" `shouldBe` [("b", NameBind), ("a", NameBind)]
    describe "isNameBound" $ do
      it "bounded head" $
        isNameBound [("a", NameBind), ("b", NameBind)] "a" `shouldBe` True
      it "bounded tail" $
        isNameBound [("a", NameBind), ("b", NameBind)] "b" `shouldBe` True
      it "unbounded" $
        isNameBound [("a", NameBind), ("b", NameBind)] "c" `shouldBe` False
      it "Induction type -- nat" $
        isNameBound natContext "nat" `shouldBe` True
      it "Induction type -- eq" $
        isNameBound natContext "eq" `shouldBe` True
      it "Constructor -- O" $
        isNameBound natContext "O" `shouldBe` True
      it "Constructor -- S" $
        isNameBound natContext "S" `shouldBe` True
      it "Constructor -- eqrefl" $
        isNameBound natContext "eqrefl" `shouldBe` True
    describe "pickFreshName" $ do
      it "unbounded" $
        pickFreshName emptyContext "a" `shouldBe` ([("a", NameBind)], "a")
      it "bounded-0" $
        pickFreshName [("a", NameBind)] "a" `shouldBe`
          ([("a0", NameBind), ("a", NameBind)], "a0")
      it "bounded-2" $
        pickFreshName [("a1", NameBind), ("a0", NameBind), ("a", NameBind)]
          "a" `shouldBe` 
          ([("a2", NameBind), ("a1", NameBind), ("a0", NameBind), ("a", NameBind)], "a2")
    describe "indexToName" $ do
      it "bounded" $
        indexToName [("a", NameBind)] 0 `shouldBe` Right "a"
      it "bounded tail" $
        indexToName [("a''", NameBind), ("a'", NameBind), ("a", NameBind)] 2 `shouldBe` Right "a"
      it "unbounded" $
        indexToName [("a''", NameBind), ("a'", NameBind), ("a", NameBind)] 3 `shouldBe` Left IndexOutOfBound
    describe "nameToIndex" $ do
      it "bounded single" $
        nameToIndex [("a", NameBind)] "a" `shouldBe` Right 0
      it "bounded multiple" $
        nameToIndex [("a", VarBind (TmRel "a" 1)), ("a", NameBind)] "a" `shouldBe` Right 0
      it "bounded tail" $
        nameToIndex [("a", VarBind (TmRel "a" 1)), ("a", NameBind), ("b", NameBind)] "b" `shouldBe` Right 2
      it "type constructor" $
        nameToIndex [("A", IndTypeBind 1 (TmRel "a" 1) (TmRel "b" 1) 
                           [ Constructor "B" (TmRel "a" 1) (TmRel "b" 1)
                           , Constructor "C" (TmRel "a" 1) (TmRel "b" 1)])] "A"
          `shouldBe`
          Left IsTypeConstructor
      it "constructor" $
        nameToIndex [("A", IndTypeBind 1 (TmRel "a" 1) (TmRel "b" 1) 
                           [ Constructor "B" (TmRel "a" 1) (TmRel "b" 1)
                           , Constructor "C" (TmRel "a" 1) (TmRel "b" 1)])] "C"
          `shouldBe`
          Left IsConstructor
    describe "getBinding" $ do
      it "0" $
        getBinding dependentContext 0 `shouldBe` Right (VarBind (TmRel "B" 1))
      it "1" $
        getBinding dependentContext 1 `shouldBe` Right (VarBind (TmRel "C" 3))
      it "2" $
        getBinding dependentContext 3 `shouldBe` Right (TmAbbBind (TmRel "D" 4) (Just $ TmRel "E" 5))
    describe "getBindingType" $
      it "simple" $
        getBindingType natContextWithAxiom 0
        `shouldBe`
        Right
        ( TmProd "x"
          ( TmIndType "nat" [] )
          ( TmProd "y"
            ( TmIndType "nat" [] )
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmAppl
                [ TmRel "plus" 3
                , TmRel "x" 1
                , TmRel "y" 0 ]
              , TmAppl
                [ TmRel "plus" 3
                , TmRel "y" 0
                , TmRel "x" 1 ]])))
    describe "getIndTypeTerm" $ do
      it "found" $
        getIndTypeTerm listContext "list" `shouldBe`
        Right
        ( TmLambda "T"
            TmType
            ( TmIndType "list"
              [ TmRel "T" 0 ]))
      it "not found" $
        getIndTypeTerm listContext "nil" `shouldBe`
        Left NotATypeConstructor
    describe "getIndTypeType" $ do
      it "found" $
        getIndTypeType listContext "list" `shouldBe`
        Right
        ( 1
        , TmProd "T"
            TmType
            TmType )
      it "not found" $
        getIndTypeType listContext "nil" `shouldBe`
        Left NotATypeConstructor
    describe "getConstrTerm" $ do
      it "found nil" $
        getConstrTerm listContext "nil" `shouldBe`
        Right 
        ( TmLambda "T"
          TmType
          ( TmConstr "nil"
            [ TmRel "T" 0 ]))
      it "found cons" $
        getConstrTerm listContext "cons" `shouldBe`
        Right
        ( TmLambda "T"
          TmType
          ( TmLambda ".0"
            ( TmRel "T" 0 )
            ( TmLambda ".1"
              ( TmIndType "list"
                [ TmRel "T" 1 ])
              ( TmConstr "cons"
                [ TmRel "T" 2, TmRel ".0" 1, TmRel ".1" 0 ]))))
      it "not found" $
        getConstrTerm listContext "list" `shouldBe`
        Left NotAConstructor
    describe "getConstrType" $ do
      it "found nil" $
        getConstrType listContext "nil" `shouldBe`
        Right 
        ( TmProd "T"
          TmType
          ( TmIndType "list"
            [ TmRel "T" 0 ]))
      it "found cons" $
        getConstrType listContext "cons" `shouldBe`
        Right
        ( TmProd "T"
          TmType
          ( TmProd "_"
            ( TmRel "T" 0 )
            ( TmProd "_"
              ( TmIndType "list"
                [ TmRel "T" 1 ])
              ( TmIndType "list"
                [ TmRel "T" 2 ]))))
      it "not found" $
        getConstrType listContext "list" `shouldBe`
        Left NotAConstructor
