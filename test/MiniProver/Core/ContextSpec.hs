module MiniProver.Core.ContextSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Context

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
    describe "pickFreshName" $ do
      it "unbounded" $
        pickFreshName emptyContext "a" `shouldBe` ([("a", NameBind)], "a")
      it "bounded-0" $
        pickFreshName [("a", NameBind)] "a" `shouldBe` 
          ([("a'", NameBind), ("a", NameBind)], "a'")
      it "bounded-2" $
        pickFreshName [("a''", NameBind), ("a'", NameBind), ("a", NameBind)] 
          "a" `shouldBe` 
          ([("a'''", NameBind), ("a''", NameBind), ("a'", NameBind), ("a", NameBind)], "a'''")
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
    describe "indexToBinding" $ do
      it "bounded" $
        indexToBinding [("a", NameBind)] 0 `shouldBe` Right NameBind
      it "bounded tail" $
        indexToBinding [("a''", NameBind), ("a'", NameBind), ("a", NameBind)] 2 `shouldBe` Right NameBind
      it "unbounded" $
        indexToBinding [("a''", NameBind), ("a'", NameBind), ("a", NameBind)] 3 `shouldBe` Left IndexOutOfBound
    describe "checkAllNameBounded" $ do
      let ctx = [("A", NameBind), ("B", NameBind), ("C", NameBind), ("D", NameBind)]
      describe "TmVar" $ do
        it "bounded" $
          checkAllNameBounded ctx (TmVar "A") `shouldBe` []
        it "unbounded" $
          checkAllNameBounded ctx (TmVar "a") `shouldBe` ["a"]
      describe "TmAppl" $ do
        it "bounded" $
          checkAllNameBounded ctx (TmAppl [TmVar "A", TmVar "D"]) `shouldBe` []
        it "unbounded" $
          checkAllNameBounded ctx (TmAppl [TmVar "A", TmVar "c"]) `shouldBe` ["c"]
      describe "TmProd" $ do
        it "bounded" $
          checkAllNameBounded ctx 
            (TmProd "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            []
        it "unbounded ty" $
          checkAllNameBounded ctx 
            (TmProd "a" 
              (TmAppl [TmVar "A", TmVar "a"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            ["a"]
        it "unbounded tm" $
          checkAllNameBounded ctx 
            (TmProd "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "b"]))
            `shouldBe`
            ["b"]
      describe "TmLambda" $ do
        it "bounded" $
          checkAllNameBounded ctx 
            (TmLambda "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            []
        it "unbounded ty" $
          checkAllNameBounded ctx 
            (TmLambda "a" 
              (TmAppl [TmVar "A", TmVar "a"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            ["a"]
        it "unbounded tm" $
          checkAllNameBounded ctx 
            (TmLambda "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "b"]))
            `shouldBe`
            ["b"]
      describe "TmFix" $ do
        it "bounded" $
          checkAllNameBounded ctx (TmFix (TmVar "A")) `shouldBe` []
        it "unbounded" $
          checkAllNameBounded ctx (TmFix (TmVar "a")) `shouldBe` ["a"]
      describe "TmLetIn" $ do
        it "bounded" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "A")
              (TmVar "B")
              (TmAppl [TmVar "A", TmVar "x"]))
          `shouldBe`
          []
        it "unbounded ty" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "x")
              (TmVar "B")
              (TmAppl [TmVar "A", TmVar "x"]))
          `shouldBe`
          ["x"]
        it "unbounded tm" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "A")
              (TmVar "x")
              (TmAppl [TmVar "A", TmVar "x"]))
          `shouldBe`
          ["x"]
        it "unbounded bdy" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "A")
              (TmVar "B")
              (TmAppl [TmVar "A", TmVar "y"]))
          `shouldBe`
          ["y"]
      describe "TmSort" $
        it "bounded" $ checkAllNameBounded ctx (TmSort Prop) `shouldBe` []
      describe "TmMatch" $ do
        it "bounded" $
          checkAllNameBounded ctx
            (TmMatch (TmVar "A") ["t","r"] (TmAppl [TmVar "A", TmVar "r"])
              [ Equation ["a"] (TmVar "A")
              , Equation ["a", "b"] (TmAppl [TmVar "A", TmVar "b"])])
          `shouldBe`
          []
        it "unbounded tm" $
          checkAllNameBounded ctx
            (TmMatch (TmVar "x") ["t","r"] (TmAppl [TmVar "A", TmVar "r"])
              [ Equation ["a"] (TmVar "A")
              , Equation ["a", "b"] (TmAppl [TmVar "A", TmVar "b"])])
          `shouldBe`
          ["x"]
        it "unbounded branch constr" $
          checkAllNameBounded ctx
            (TmMatch (TmVar "A") ["t","r"] (TmAppl [TmVar "A", TmVar "r"])
              [ Equation ["a"] (TmAppl [TmVar "A", TmVar "a"])
              , Equation ["a", "b"] (TmAppl [TmVar "A", TmVar "b"])])
          `shouldBe`
          ["a"]
        it "unbounded rty" $
          checkAllNameBounded ctx
            (TmMatch (TmVar "A") ["t","r"] (TmAppl [TmVar "A", TmVar "t"])
              [ Equation ["a"] (TmVar "A")
              , Equation ["a", "b"] (TmAppl [TmVar "A", TmVar "b"])])
          `shouldBe`
          ["t"]