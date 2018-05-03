module MiniProver.Core.SubstSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Subst

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "shift" $ do
    describe "tmShiftAbove" $ do
      describe "TmRel" $ do
        it "less than" $
          tmShiftAbove 2 0 (TmRel "a" 1) `shouldBe` TmRel "a" 3
        it "equal" $
          tmShiftAbove 2 1 (TmRel "a" 1) `shouldBe` TmRel "a" 3
        it "greater than" $
          tmShiftAbove 2 2 (TmRel "a" 1) `shouldBe` TmRel "a" 1
      describe "TmVar" $
        it "nothing happens" $
          tmShiftAbove 2 0 (TmVar "a") `shouldBe` TmVar "a"
      describe "TmAppl" $ do
        it "single-1" $
          tmShiftAbove 2 0 (TmAppl [TmRel "a" 1]) `shouldBe` TmAppl [TmRel "a" 3]
        it "single-2" $
          tmShiftAbove 2 1 (TmAppl [TmRel "a" 1]) `shouldBe` TmAppl [TmRel "a" 3]
        it "single-3" $
          tmShiftAbove 2 2 (TmAppl [TmRel "a" 1]) `shouldBe` TmAppl [TmRel "a" 1]
        it "multiple" $
          tmShiftAbove 2 2 (TmAppl [TmRel "a" 0, TmRel "b" 1, TmRel "c" 2, TmRel "d" 3]) `shouldBe`
            TmAppl [TmRel "a" 0, TmRel "b" 1, TmRel "c" 4, TmRel "d" 5]
      describe "TmProd" $ do
        describe "Type" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmProd "lt1" (TmRel "a" 1) (TmRel "b" 0)) `shouldBe` 
              TmProd "lt1" (TmRel "a" 1) (TmRel "b" 0)
          it "equal" $
            tmShiftAbove 2 2 (TmProd "eq1" (TmRel "a" 2) (TmRel "b" 0)) `shouldBe`
              TmProd "eq1" (TmRel "a" 4) (TmRel "b" 0)
          it "greater than" $
            tmShiftAbove 2 2 (TmProd "gt1" (TmRel "a" 3) (TmRel "b" 0)) `shouldBe`
              TmProd "gt1" (TmRel "a" 5) (TmRel "b" 0)
        describe "Term" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmProd "lt2" (TmRel "a" 0) (TmRel "b" 2)) `shouldBe` 
              TmProd "lt2" (TmRel "a" 0) (TmRel "b" 2)
          it "equal" $
            tmShiftAbove 2 2 (TmProd "eq2" (TmRel "a" 0) (TmRel "b" 3)) `shouldBe`
              TmProd "eq2" (TmRel "a" 0) (TmRel "b" 5)
          it "greater than" $
            tmShiftAbove 2 2 (TmProd "gt2" (TmRel "a" 0) (TmRel "b" 4)) `shouldBe`
              TmProd "gt2" (TmRel "a" 0) (TmRel "b" 6)
      describe "TmLambda" $ do
        describe "Type" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmLambda "lt1" (TmRel "a" 1) (TmRel "b" 0)) `shouldBe` 
              TmLambda "lt1" (TmRel "a" 1) (TmRel "b" 0)
          it "equal" $
            tmShiftAbove 2 2 (TmLambda "eq1" (TmRel "a" 2) (TmRel "b" 0)) `shouldBe`
              TmLambda "eq1" (TmRel "a" 4) (TmRel "b" 0)
          it "greater than" $
            tmShiftAbove 2 2 (TmLambda "gt1" (TmRel "a" 3) (TmRel "b" 0)) `shouldBe`
              TmLambda "gt1" (TmRel "a" 5) (TmRel "b" 0)
        describe "Term" $ do
          it "less than" $
            tmShiftAbove 2 2 (TmLambda "lt2" (TmRel "a" 0) (TmRel "b" 2)) `shouldBe` 
              TmLambda "lt2" (TmRel "a" 0) (TmRel "b" 2)
          it "equal" $
            tmShiftAbove 2 2 (TmLambda "eq2" (TmRel "a" 0) (TmRel "b" 3)) `shouldBe`
              TmLambda "eq2" (TmRel "a" 0) (TmRel "b" 5)
          it "greater than" $
            tmShiftAbove 2 2 (TmLambda "gt2" (TmRel "a" 0) (TmRel "b" 4)) `shouldBe`
              TmLambda "gt2" (TmRel "a" 0) (TmRel "b" 6)
      describe "TmFix" $ do
        it "less than" $
          tmShiftAbove 2 2 (TmFix (TmLambda "f" (TmRel "A" 1) (TmLambda "a" (TmRel "B" 2) (TmRel "B" 3))))
            `shouldBe` TmFix (TmLambda "f" (TmRel "A" 1) (TmLambda "a" (TmRel "B" 2) (TmRel "B" 3)))
        it "equal" $
          tmShiftAbove 2 2 (TmFix (TmLambda "f" (TmRel "A" 2) (TmLambda "a" (TmRel "B" 3) (TmRel "B" 4))))
            `shouldBe` TmFix (TmLambda "f" (TmRel "A" 4) (TmLambda "a" (TmRel "B" 5) (TmRel "B" 6)))
        it "greater than" $
          tmShiftAbove 2 2 (TmFix (TmLambda "f" (TmRel "A" 3) (TmLambda "a" (TmRel "B" 4) (TmRel "B" 5))))
            `shouldBe` TmFix (TmLambda "f" (TmRel "A" 5) (TmLambda "a" (TmRel "B" 6) (TmRel "B" 7)))
      describe "TmLetIn" $ do
        it "less than" $
          tmShiftAbove 2 2 (TmLetIn "x" (TmRel "A" 1) (TmRel "A" 1) (TmRel "A" 2)) `shouldBe`
            TmLetIn "x" (TmRel "A" 1) (TmRel "A" 1) (TmRel "A" 2)
        it "equal" $
          tmShiftAbove 2 2 (TmLetIn "x" (TmRel "A" 2) (TmRel "A" 2) (TmRel "A" 3)) `shouldBe`
            TmLetIn "x" (TmRel "A" 4) (TmRel "A" 4) (TmRel "A" 5)
        it "greater than" $
          tmShiftAbove 2 2 (TmLetIn "x" (TmRel "A" 3) (TmRel "A" 3) (TmRel "A" 4)) `shouldBe`
            TmLetIn "x" (TmRel "A" 5) (TmRel "A" 5) (TmRel "A" 6)
      describe "TmIndType" $ 
        it "simple" $
          tmShiftAbove 2 2 (TmIndType "tuplethree" [TmRel "A" 1, TmRel "B" 2, TmRel "C" 3])
            `shouldBe` TmIndType "tuplethree" [TmRel "A" 1, TmRel "B" 4, TmRel "C" 5]
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
            (TmMatch (TmAppl [TmRel "A" 1, TmRel "B" 2, TmRel "C" 3])
              ["a", "b", "c"]
              (TmAppl [TmRel "A" 3, TmRel "B" 4, TmRel "C" 5])
              [ Equation ["a"] (TmAppl [TmRel "A" 1, TmRel "B" 2, TmRel "C" 3])
              , Equation ["a", "b"] (TmAppl [TmRel "A" 2, TmRel "B" 3, TmRel "C" 4])
              , Equation ["a", "b", "c"] (TmAppl [TmRel "A" 3, TmRel "B" 4, TmRel "C" 5])])
            `shouldBe`
            TmMatch (TmAppl [TmRel "A" 1, TmRel "B" 4, TmRel "C" 5])
              ["a", "b", "c"]
              (TmAppl [TmRel "A" 3, TmRel "B" 6, TmRel "C" 7])
              [ Equation ["a"] (TmAppl [TmRel "A" 1, TmRel "B" 4, TmRel "C" 5])
              , Equation ["a", "b"] (TmAppl [TmRel "A" 2, TmRel "B" 5, TmRel "C" 6])
              , Equation ["a", "b", "c"] (TmAppl [TmRel "A" 3, TmRel "B" 6, TmRel "C" 7])]
    describe "tmShift" $ do
      describe "TmRel" $ do
        it "0" $
          tmShift 2 (TmRel "a" 0) `shouldBe` TmRel "a" 2
        it "1" $
          tmShift 2 (TmRel "a" 1) `shouldBe` TmRel "a" 3
      describe "TmVar" $
        it "nothing happens" $
          tmShift 2 (TmVar "a") `shouldBe` TmVar "a"
      describe "TmAppl" $
        it "all in one" $
          tmShift 2 (TmAppl [TmRel "a" 0, TmRel "b" 1]) `shouldBe` 
            TmAppl [TmRel "a" 2, TmRel "b" 3]
      describe "TmProd" $
        it "all in one" $
          -- [b c] pi aio:b c. aio b c
          tmShift 2 
            (TmProd "aio" 
              (TmAppl [TmRel "b" 0, TmRel "c" 1]) 
              (TmAppl [TmRel "aio" 0, TmRel "b" 1, TmRel "c" 2]))
            `shouldBe` 
            TmProd "aio" 
              (TmAppl [TmRel "b" 2, TmRel "c" 3]) 
              (TmAppl [TmRel "aio" 0, TmRel "b" 3, TmRel "c" 4])
      describe "TmLambda" $
        it "all in one" $
          -- [b c] lambda aio:b c. aio b c
          tmShift 2 
            (TmLambda "aio" 
              (TmAppl [TmRel "b" 0, TmRel "c" 1]) 
              (TmAppl [TmRel "aio" 0, TmRel "b" 1, TmRel "c" 2]))
            `shouldBe` 
            TmLambda "aio" 
              (TmAppl [TmRel "b" 2, TmRel "c" 3]) 
              (TmAppl [TmRel "aio" 0, TmRel "b" 3, TmRel "c" 4])
      describe "TmFix" $
        it "all in one" $
          -- [A B] fix (lambda f:A B.lambda a:f A B.f A B)
          tmShift 2
            (TmFix 
              (TmLambda "f" (TmAppl [TmRel "A" 0, TmRel "B" 1]) 
                (TmLambda "a" 
                  (TmAppl [TmRel "f" 0, TmRel "A" 1, TmRel "B" 2]) 
                  (TmAppl [TmRel "f" 1, TmRel "A" 2, TmRel "B" 3]))))
            `shouldBe`
            TmFix 
              (TmLambda "f" (TmAppl [TmRel "A" 2, TmRel "B" 3]) 
                (TmLambda "a" 
                  (TmAppl [TmRel "f" 0, TmRel "A" 3, TmRel "B" 4]) 
                  (TmAppl [TmRel "f" 1, TmRel "A" 4, TmRel "B" 5])))
      describe "TmLetIn" $
        it "all in one" $
          -- [A B] let x:A B:=A B in x A B
          tmShift 2
            (TmLetIn "x" 
              (TmAppl [TmRel "A" 0, TmRel "B" 1]) 
              (TmAppl [TmRel "A" 0, TmRel "B" 1]) 
              (TmAppl [TmRel "x" 0, TmRel "A" 1, TmRel "B" 2])) 
            `shouldBe`
            TmLetIn "x" 
              (TmAppl [TmRel "A" 2, TmRel "B" 3]) 
              (TmAppl [TmRel "A" 2, TmRel "B" 3]) 
              (TmAppl [TmRel "x" 0, TmRel "A" 3, TmRel "B" 4])
      describe "TmIndType" $ 
        it "simple" $
          -- [A B] pair A B
          tmShift 2 (TmIndType "pair" [TmRel "A" 0, TmRel "B" 1])
            `shouldBe` TmIndType "pair" [TmRel "A" 2, TmRel "B" 3]
      describe "TmSort" $ do
        it "Prop" $
          tmShift 2 (TmSort Prop) `shouldBe` TmSort Prop
        it "Set" $
          tmShift 2 (TmSort Set) `shouldBe` TmSort Set
        it "Type" $
          tmShift 2 (TmSort Type) `shouldBe` TmSort Type
      describe "TmMatch" $
        it "all in one" $ 
          -- [A B] match A B in a b c return A B b c with |a => A B |a b => b A B |a b c => b A B end
          tmShift 2
            (TmMatch (TmAppl [TmRel "A" 0, TmRel "B" 1])
              ["a", "b", "c"]
              (TmAppl [TmRel "A" 2, TmRel "B" 3, TmRel "b" 1, TmRel "c" 0])
              [ Equation ["a"] (TmAppl [TmRel "A" 0, TmRel "B" 1])
              , Equation ["a", "b"] (TmAppl [TmRel "b" 0, TmRel "A" 1, TmRel "B" 2])
              , Equation ["a", "b", "c"] (TmAppl [TmRel "b" 1, TmRel "A" 2, TmRel "B" 3])])
            `shouldBe`
            TmMatch (TmAppl [TmRel "A" 2, TmRel "B" 3])
              ["a", "b", "c"]
              (TmAppl [TmRel "A" 4, TmRel "B" 5, TmRel "b" 1, TmRel "c" 0])
              [ Equation ["a"] (TmAppl [TmRel "A" 2, TmRel "B" 3])
              , Equation ["a", "b"] (TmAppl [TmRel "b" 0, TmRel "A" 3, TmRel "B" 4])
              , Equation ["a", "b", "c"] (TmAppl [TmRel "b" 1, TmRel "A" 4, TmRel "B" 5])]
  describe "substitude" $
    describe "tmSubstTop" $ do
      describe "TmRel" $ do
        it "equal" $
          -- (lambda. 0)(0 1) => 0 1
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) (TmRel "x" 0)
            `shouldBe` TmAppl [TmRel "a" 0, TmRel "b" 1]
        it "greater than" $
          -- (lambda. 1)(0 1) => 0
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) (TmRel "a" 1)
            `shouldBe` TmRel "a" 0
      describe "TmVar" $
        it "nothing happens" $
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) (TmVar "a") `shouldBe` TmVar "a"
      describe "TmAppl" $
        it "all in one" $
          -- (lambda. 0 1)(0 1) => (0 1) 0
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) 
            (TmAppl [TmRel "x" 0, TmRel "a" 1]) `shouldBe`
            TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0]
      describe "TmProd" $
        it "all in one" $
          -- (lambda. pi aio:0 1. 0 1 2)(0 1) => pi aio:(0 1) 0. 0 (1 2) 1
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) 
            (TmProd "aio" 
              (TmAppl [TmRel "x" 0, TmRel "a" 1]) 
              (TmAppl [TmRel "aio" 0, TmRel "x" 1, TmRel "a" 2]))
            `shouldBe` 
            TmProd "aio" 
              (TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0]) 
              (TmAppl [TmRel "aio" 0, TmAppl [TmRel "a" 1, TmRel "b" 2], TmRel "a" 1])
      describe "TmLambda" $
        it "all in one" $
          -- (lambda. lambda aio:0 1. 0 1 2)(0 1) => lambda aio:(0 1) 0. 0 (1 2) 1
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) 
            (TmLambda "aio" 
              (TmAppl [TmRel "x" 0, TmRel "a" 1]) 
              (TmAppl [TmRel "aio" 0, TmRel "x" 1, TmRel "a" 2]))
            `shouldBe` 
            TmLambda "aio" 
              (TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0]) 
              (TmAppl [TmRel "aio" 0, TmAppl [TmRel "a" 1, TmRel "b" 2], TmRel "a" 1])
      describe "TmFix" $
        it "all in one" $
          -- (lambda. fix lambda f:0 1.lambda a:0 1 2.1 2 3)(0 1) => fix lambda f:(0 1) 0.lambda a:0 (1 2) 1.1 (2 3) 2
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1])
            (TmFix 
              (TmLambda "f" (TmAppl [TmRel "x" 0, TmRel "a" 1]) 
                (TmLambda "y" 
                  (TmAppl [TmRel "f" 0, TmRel "x" 1, TmRel "a" 2]) 
                  (TmAppl [TmRel "f" 1, TmRel "x" 2, TmRel "a" 3]))))
            `shouldBe`
            TmFix 
              (TmLambda "f" (TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0]) 
                (TmLambda "y"
                  (TmAppl [TmRel "f" 0, TmAppl [TmRel "a" 1, TmRel "b" 2], TmRel "a" 1]) 
                  (TmAppl [TmRel "f" 1, TmAppl [TmRel "a" 2, TmRel "b" 3], TmRel "a" 2])))
      describe "TmLetIn" $
        it "all in one" $
          -- (lambda. let x:0 1:=0 1 in 0 1 2)(0 1) => let x:(0 1) 0:=(0 1) 0 in 0 (1 2) 1
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1])
            (TmLetIn "y" 
              (TmAppl [TmRel "x" 0, TmRel "a" 1]) 
              (TmAppl [TmRel "x" 0, TmRel "a" 1]) 
              (TmAppl [TmRel "y" 0, TmRel "x" 1, TmRel "a" 2])) 
            `shouldBe`
            TmLetIn "y" 
              (TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0]) 
              (TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0]) 
              (TmAppl [TmRel "y" 0, TmAppl [TmRel "a" 1, TmRel "b" 2], TmRel "a" 1])
      describe "TmIndType" $ 
        it "simple" $
          -- (lambda. tuplethree 0 1)(0 1) => tuplethree (0 1) 0
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1])
            (TmIndType "tuplethree" [TmRel "x" 0, TmRel "a" 1])
            `shouldBe` TmIndType "tuplethree" [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0]
      describe "TmSort" $ do
        it "Prop" $
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) (TmSort Prop) `shouldBe` TmSort Prop
        it "Set" $
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) (TmSort Set) `shouldBe` TmSort Set
        it "Type" $
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1]) (TmSort Type) `shouldBe` TmSort Type
      describe "TmMatch" $
        it "all in one" $
          -- (lambda. match 0 1 in r s t return 0 1 2 3 4 with |a => 0 1|a b => 0 1 2|a b c => 1 2 3 end)(0 1) => 
          -- match (0 1) 0 with |a => (0 1) 0|a b => 0 (1 2) 1|a b c => 1 (2 3) 2
          tmSubstTop (TmAppl [TmRel "a" 0, TmRel "b" 1])
            (TmMatch (TmAppl [TmRel "x" 0, TmRel "a" 1])
              ["r", "s", "t"]
              (TmAppl [TmRel "t" 0, TmRel "s" 1, TmRel "x" 2, TmRel "a" 3, TmRel "b" 4])
              [ Equation ["A"] (TmAppl [TmRel "x" 0, TmRel "a" 1])
              , Equation ["A", "B"] (TmAppl [TmRel "B" 0, TmRel "x" 1, TmRel "a" 2])
              , Equation ["A", "B", "c"] (TmAppl [TmRel "B" 1, TmRel "x" 2, TmRel "a" 3])])
            `shouldBe`
            TmMatch (TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0])
              ["r", "s", "t"]
              (TmAppl [TmRel "t" 0, TmRel "s" 1, TmAppl [TmRel "a" 2, TmRel "b" 3], TmRel "a" 2, TmRel "b" 3])
              [ Equation ["A"] 
                (TmAppl [TmAppl [TmRel "a" 0, TmRel "b" 1], TmRel "a" 0])
              , Equation ["A", "B"] 
                (TmAppl [TmRel "B" 0, TmAppl [TmRel "a" 1, TmRel "b" 2], TmRel "a" 1])
              , Equation ["A", "B", "c"] 
                (TmAppl [TmRel "B" 1, TmAppl [TmRel "a" 2, TmRel "b" 3], TmRel "a" 2])]
        