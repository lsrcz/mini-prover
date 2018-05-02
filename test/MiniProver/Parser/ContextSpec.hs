module MiniProver.Parser.ContextSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Context

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "shift" $ do
    describe "tmShiftAbove" $ do
      describe "TmRel" $ do
        it "less than" $
          tmShiftAbove 2 0 (TmRel 1) `shouldBe` TmRel 3
        it "equal" $
          tmShiftAbove 2 1 (TmRel 1) `shouldBe` TmRel 3
        it "greater than" $
          tmShiftAbove 2 2 (TmRel 1) `shouldBe` TmRel 1
      describe "TmVar" $
        it "nothing happens" $
          tmShiftAbove 2 0 (TmVar "a") `shouldBe` TmVar "a"
      describe "TmAppl" $ do
        it "single-1" $
          tmShiftAbove 2 0 (TmAppl [TmRel 1]) `shouldBe` TmAppl [TmRel 3]
        it "single-2" $
          tmShiftAbove 2 1 (TmAppl [TmRel 1]) `shouldBe` TmAppl [TmRel 3]
        it "single-3" $
          tmShiftAbove 2 2 (TmAppl [TmRel 1]) `shouldBe` TmAppl [TmRel 1]
        it "multiple" $
          tmShiftAbove 2 2 (TmAppl [TmRel 0, TmRel 1, TmRel 2, TmRel 3]) `shouldBe`
            TmAppl [TmRel 0, TmRel 1, TmRel 4, TmRel 5]
      describe "TmProd" $ do
        describe "Type" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmProd "lt1" (TmRel 1) (TmRel 0)) `shouldBe` 
              TmProd "lt1" (TmRel 1) (TmRel 0)
          it "equal" $
            tmShiftAbove 2 2 (TmProd "eq1" (TmRel 2) (TmRel 0)) `shouldBe`
              TmProd "eq1" (TmRel 4) (TmRel 0)
          it "greater than" $
            tmShiftAbove 2 2 (TmProd "gt1" (TmRel 3) (TmRel 0)) `shouldBe`
              TmProd "gt1" (TmRel 5) (TmRel 0)
        describe "Term" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmProd "lt2" (TmRel 0) (TmRel 2)) `shouldBe` 
              TmProd "lt2" (TmRel 0) (TmRel 2)
          it "equal" $
            tmShiftAbove 2 2 (TmProd "eq2" (TmRel 0) (TmRel 3)) `shouldBe`
              TmProd "eq2" (TmRel 0) (TmRel 5)
          it "greater than" $
            tmShiftAbove 2 2 (TmProd "gt2" (TmRel 0) (TmRel 4)) `shouldBe`
              TmProd "gt2" (TmRel 0) (TmRel 6)
      describe "TmLambda" $ do
        describe "Type" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmLambda "lt1" (TmRel 1) (TmRel 0)) `shouldBe` 
              TmLambda "lt1" (TmRel 1) (TmRel 0)
          it "equal" $
            tmShiftAbove 2 2 (TmLambda "eq1" (TmRel 2) (TmRel 0)) `shouldBe`
              TmLambda "eq1" (TmRel 4) (TmRel 0)
          it "greater than" $
            tmShiftAbove 2 2 (TmLambda "gt1" (TmRel 3) (TmRel 0)) `shouldBe`
              TmLambda "gt1" (TmRel 5) (TmRel 0)
        describe "Term" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmLambda "lt2" (TmRel 0) (TmRel 2)) `shouldBe` 
              TmLambda "lt2" (TmRel 0) (TmRel 2)
          it "equal" $
            tmShiftAbove 2 2 (TmLambda "eq2" (TmRel 0) (TmRel 3)) `shouldBe`
              TmLambda "eq2" (TmRel 0) (TmRel 5)
          it "greater than" $
            tmShiftAbove 2 2 (TmLambda "gt2" (TmRel 0) (TmRel 4)) `shouldBe`
              TmLambda "gt2" (TmRel 0) (TmRel 6)
      describe "TmFix" $ do
        it "less than" $
          tmShiftAbove 2 2 (TmFix (TmLambda "f" (TmRel 1) (TmLambda "a" (TmRel 2) (TmRel 3))))
            `shouldBe` TmFix (TmLambda "f" (TmRel 1) (TmLambda "a" (TmRel 2) (TmRel 3)))
        it "equal" $
          tmShiftAbove 2 2 (TmFix (TmLambda "f" (TmRel 2) (TmLambda "a" (TmRel 3) (TmRel 4))))
            `shouldBe` TmFix (TmLambda "f" (TmRel 4) (TmLambda "a" (TmRel 5) (TmRel 6)))
        it "greater than" $
          tmShiftAbove 2 2 (TmFix (TmLambda "f" (TmRel 3) (TmLambda "a" (TmRel 4) (TmRel 5))))
            `shouldBe` TmFix (TmLambda "f" (TmRel 5) (TmLambda "a" (TmRel 6) (TmRel 7)))
      describe "TmLetIn" $ do
        it "less than" $
          tmShiftAbove 2 2 (TmLetIn "x" (TmRel 1) (TmRel 1) (TmRel 2)) `shouldBe`
            TmLetIn "x" (TmRel 1) (TmRel 1) (TmRel 2)
        it "equal" $
          tmShiftAbove 2 2 (TmLetIn "x" (TmRel 2) (TmRel 2) (TmRel 3)) `shouldBe`
            TmLetIn "x" (TmRel 4) (TmRel 4) (TmRel 5)
        it "greater than" $
          tmShiftAbove 2 2 (TmLetIn "x" (TmRel 3) (TmRel 3) (TmRel 4)) `shouldBe`
            TmLetIn "x" (TmRel 5) (TmRel 5) (TmRel 6)
      describe "TmIndType" $ 
        it "simple" $
          tmShiftAbove 2 2 (TmIndType "tuplethree" [TmRel 1, TmRel 2, TmRel 3])
            `shouldBe` TmIndType "tuplethree" [TmRel 1, TmRel 4, TmRel 5]
      describe "TmSort" $ do
        it "Prop" $
          tmShiftAbove 2 2 (TmSort Prop) `shouldBe` TmSort Prop
        it "Set" $
          tmShiftAbove 2 2 (TmSort Set) `shouldBe` TmSort Set
        it "Type" $
          tmShiftAbove 2 2 (TmSort Type) `shouldBe` TmSort Type
      describe "TmMatch" $
        it "all in one" $ 
          tmShiftAbove 2 2 
            (TmMatch (TmAppl [TmRel 1, TmRel 2, TmRel 3])
              [ Equation ["a"] (TmAppl [TmRel 1, TmRel 2, TmRel 3])
              , Equation ["a", "b"] (TmAppl [TmRel 2, TmRel 3, TmRel 4])
              , Equation ["a", "b", "c"] (TmAppl [TmRel 3, TmRel 4, TmRel 5])])
            `shouldBe`
            TmMatch (TmAppl [TmRel 1, TmRel 4, TmRel 5])
              [ Equation ["a"] (TmAppl [TmRel 1, TmRel 4, TmRel 5])
              , Equation ["a", "b"] (TmAppl [TmRel 2, TmRel 5, TmRel 6])
              , Equation ["a", "b", "c"] (TmAppl [TmRel 3, TmRel 6, TmRel 7])]
    describe "tmShift" $ do
      describe "TmRel" $ do
        it "0" $
          tmShift 2 (TmRel 0) `shouldBe` TmRel 2
        it "1" $
          tmShift 2 (TmRel 1) `shouldBe` TmRel 3
      describe "TmVar" $
        it "nothing happens" $
          tmShift 2 (TmVar "a") `shouldBe` TmVar "a"
      describe "TmAppl" $
        it "all in one" $
          tmShift 2 (TmAppl [TmRel 0, TmRel 1]) `shouldBe` TmAppl [TmRel 2, TmRel 3]
      describe "TmProd" $
        it "all in one" $
          tmShift 2 (TmProd "aio" (TmAppl [TmRel 0, TmRel 1]) (TmAppl [TmRel 0, TmRel 1, TmRel 2]))
            `shouldBe` TmProd "aio" (TmAppl [TmRel 2, TmRel 3]) (TmAppl [TmRel 0, TmRel 3, TmRel 4])
      describe "TmLambda" $
        it "all in one" $
          tmShift 2 (TmLambda "aio" (TmAppl [TmRel 0, TmRel 1]) (TmAppl [TmRel 0, TmRel 1, TmRel 2]))
            `shouldBe` TmLambda "aio" (TmAppl [TmRel 2, TmRel 3]) (TmAppl [TmRel 0, TmRel 3, TmRel 4])
      describe "TmFix" $
        it "all in one" $
          tmShift 2
            (TmFix 
              (TmLambda "f" (TmAppl [TmRel 0, TmRel 1]) 
                (TmLambda "a" 
                  (TmAppl [TmRel 0, TmRel 1, TmRel 2]) 
                  (TmAppl [TmRel 1, TmRel 2, TmRel 3]))))
            `shouldBe`
            TmFix 
              (TmLambda "f" (TmAppl [TmRel 2, TmRel 3]) 
                (TmLambda "a" 
                  (TmAppl [TmRel 0, TmRel 3, TmRel 4]) 
                  (TmAppl [TmRel 1, TmRel 4, TmRel 5])))
      describe "TmLetIn" $
        it "all in one" $
          tmShift 2
            (TmLetIn "x" 
              (TmAppl [TmRel 0, TmRel 1]) 
              (TmAppl [TmRel 0, TmRel 1]) 
              (TmAppl [TmRel 0, TmRel 1, TmRel 2])) 
            `shouldBe`
            TmLetIn "x" 
              (TmAppl [TmRel 2, TmRel 3]) 
              (TmAppl [TmRel 2, TmRel 3]) 
              (TmAppl [TmRel 0, TmRel 3, TmRel 4])
      describe "TmIndType" $ 
        it "simple" $
          tmShift 2 (TmIndType "tuplethree" [TmRel 0, TmRel 1])
            `shouldBe` TmIndType "tuplethree" [TmRel 2, TmRel 3]
      describe "TmSort" $ do
        it "Prop" $
          tmShift 2 (TmSort Prop) `shouldBe` TmSort Prop
        it "Set" $
          tmShift 2 (TmSort Set) `shouldBe` TmSort Set
        it "Type" $
          tmShift 2 (TmSort Type) `shouldBe` TmSort Type
      describe "TmMatch" $
        it "all in one" $ 
          tmShift 2
            (TmMatch (TmAppl [TmRel 0, TmRel 1])
              [ Equation ["a"] (TmAppl [TmRel 0, TmRel 1])
              , Equation ["a", "b"] (TmAppl [TmRel 0, TmRel 1, TmRel 2])
              , Equation ["a", "b", "c"] (TmAppl [TmRel 1, TmRel 2, TmRel 3])])
            `shouldBe`
            TmMatch (TmAppl [TmRel 2, TmRel 3])
              [ Equation ["a"] (TmAppl [TmRel 2, TmRel 3])
              , Equation ["a", "b"] (TmAppl [TmRel 0, TmRel 3, TmRel 4])
              , Equation ["a", "b", "c"] (TmAppl [TmRel 1, TmRel 4, TmRel 5])]
  describe "substitude" $
    describe "tmSubstTop" $ do
      describe "TmRel" $ do
        it "equal" $
          -- (lambda. 0)(0 1) => 0 1
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmRel 0)
            `shouldBe` TmAppl [TmRel 0, TmRel 1]
        it "greater than" $
          -- (lambda. 1)(0 1) => 0
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmRel 1)
            `shouldBe` TmRel 0
      describe "TmVar" $
        it "nothing happens" $
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmVar "a") `shouldBe` TmVar "a"
      describe "TmAppl" $
        it "all in one" $
          -- (lambda. 0 1)(0 1) => (0 1) 0
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmAppl [TmRel 0, TmRel 1]) `shouldBe`
            TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0]
      describe "TmProd" $
        it "all in one" $
          -- (lambda. pi aio:0 1. 0 1 2)(0 1) => pi aio:(0 1) 0. 0 (1 2) 1
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmProd "aio" (TmAppl [TmRel 0, TmRel 1]) (TmAppl [TmRel 0, TmRel 1, TmRel 2]))
            `shouldBe` TmProd "aio" (TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0]) (TmAppl [TmRel 0, TmAppl [TmRel 1, TmRel 2], TmRel 1])
      describe "TmLambda" $
        it "all in one" $
          -- (lambda. lambda aio:0 1. 0 1 2)(0 1) => lambda aio:(0 1) 0. 0 (1 2) 1
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmLambda "aio" (TmAppl [TmRel 0, TmRel 1]) (TmAppl [TmRel 0, TmRel 1, TmRel 2]))
            `shouldBe` TmLambda "aio" (TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0]) (TmAppl [TmRel 0, TmAppl [TmRel 1, TmRel 2], TmRel 1])
      describe "TmFix" $
        it "all in one" $
          -- (lambda. fix lambda f:0 1.lambda a:0 1 2.1 2 3)(0 1) => fix lambda f:(0 1) 0.lambda a:0 (1 2) 1.1 (2 3) 2
          tmSubstTop (TmAppl [TmRel 0, TmRel 1])
            (TmFix 
              (TmLambda "f" (TmAppl [TmRel 0, TmRel 1]) 
                (TmLambda "a" 
                  (TmAppl [TmRel 0, TmRel 1, TmRel 2]) 
                  (TmAppl [TmRel 1, TmRel 2, TmRel 3]))))
            `shouldBe`
            TmFix 
              (TmLambda "f" (TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0]) 
                (TmLambda "a" 
                  (TmAppl [TmRel 0, TmAppl [TmRel 1, TmRel 2], TmRel 1]) 
                  (TmAppl [TmRel 1, TmAppl [TmRel 2, TmRel 3], TmRel 2])))
      describe "TmLetIn" $
        it "all in one" $
          -- (lambda. let x:0 1:=0 1 in 0 1 2)(0 1) => let x:(0 1) 0:=(0 1) 0 in 0 (1 2) 1
          tmSubstTop (TmAppl [TmRel 0, TmRel 1])
            (TmLetIn "x" 
              (TmAppl [TmRel 0, TmRel 1]) 
              (TmAppl [TmRel 0, TmRel 1]) 
              (TmAppl [TmRel 0, TmRel 1, TmRel 2])) 
            `shouldBe`
            TmLetIn "x" 
              (TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0]) 
              (TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0]) 
              (TmAppl [TmRel 0, TmAppl [TmRel 1, TmRel 2], TmRel 1])
      describe "TmIndType" $ 
        it "simple" $
          -- (lambda. tuplethree 0 1)(0 1) => tuplethree (0 1) 0
          tmSubstTop (TmAppl [TmRel 0, TmRel 1])
            (TmIndType "tuplethree" [TmRel 0, TmRel 1])
            `shouldBe` TmIndType "tuplethree" [TmAppl [TmRel 0, TmRel 1], TmRel 0]
      describe "TmSort" $ do
        it "Prop" $
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmSort Prop) `shouldBe` TmSort Prop
        it "Set" $
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmSort Set) `shouldBe` TmSort Set
        it "Type" $
          tmSubstTop (TmAppl [TmRel 0, TmRel 1]) (TmSort Type) `shouldBe` TmSort Type
      describe "TmMatch" $
        it "all in one" $
          -- (lambda. match 0 1 with |a => 0 1|a b => 0 1 2|a b c => 1 2 3 end)(0 1) => 
          -- match (0 1) 0 with |a => (0 1) 0|a b => 0 (1 2) 1|a b c => 1 (2 3) 2
          tmSubstTop (TmAppl [TmRel 0, TmRel 1])
            (TmMatch (TmAppl [TmRel 0, TmRel 1])
              [ Equation ["a"] (TmAppl [TmRel 0, TmRel 1])
              , Equation ["a", "b"] (TmAppl [TmRel 0, TmRel 1, TmRel 2])
              , Equation ["a", "b", "c"] (TmAppl [TmRel 1, TmRel 2, TmRel 3])])
            `shouldBe`
            TmMatch (TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0])
              [ Equation ["a"] (TmAppl [TmAppl [TmRel 0, TmRel 1], TmRel 0])
              , Equation ["a", "b"] (TmAppl [TmRel 0, TmAppl [TmRel 1, TmRel 2], TmRel 1])
              , Equation ["a", "b", "c"] (TmAppl [TmRel 1, TmAppl [TmRel 2, TmRel 3], TmRel 2])]
        