module MiniProver.Core.NameBoundingSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Utils.ContextForTesting
import MiniProver.Core.NameBounding
import Data.List (sort)

main :: IO ()
main = hspec spec

spec :: Spec
spec = 
  describe "name bounding check" $ do
    describe "checkAllNameBounded" $ do
      let ctx = simpleContext
      describe "TmVar" $ do
        it "bounded" $
          checkAllNameBounded ctx (TmVar "A") `shouldBe` AllNameBounded
        it "unbounded" $
          checkAllNameBounded ctx (TmVar "a") `shouldBe` UnboundNameInTerm ["a"]
        it "Induction types -- nat" $
          checkAllNameBounded natContext (TmVar "nat") `shouldBe` AllNameBounded
        it "Induction types -- eq" $
          checkAllNameBounded natContext (TmVar "eq") `shouldBe` AllNameBounded
        it "Constructor -- O" $
          checkAllNameBounded natContext (TmVar "O") `shouldBe` AllNameBounded
        it "Constructor -- S" $
          checkAllNameBounded natContext (TmVar "S") `shouldBe` AllNameBounded
        it "Constructor -- eqrefl" $
          checkAllNameBounded natContext (TmVar "eqrefl") `shouldBe` AllNameBounded
      describe "TmAppl" $ do
        it "bounded" $
          checkAllNameBounded ctx (TmAppl [TmVar "A", TmVar "D"]) `shouldBe` AllNameBounded
        it "unbounded" $
          checkAllNameBounded ctx (TmAppl [TmVar "A", TmVar "c"]) `shouldBe` UnboundNameInTerm ["c"]
      describe "TmProd" $ do
        it "bounded" $
          checkAllNameBounded ctx 
            (TmProd "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            AllNameBounded
        it "unbounded ty" $
          checkAllNameBounded ctx 
            (TmProd "a" 
              (TmAppl [TmVar "A", TmVar "a"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            UnboundNameInTerm ["a"]
        it "unbounded tm" $
          checkAllNameBounded ctx 
            (TmProd "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "b"]))
            `shouldBe`
            UnboundNameInTerm ["b"]
      describe "TmLambda" $ do
        it "bounded" $
          checkAllNameBounded ctx 
            (TmLambda "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            AllNameBounded
        it "unbounded ty" $
          checkAllNameBounded ctx 
            (TmLambda "a" 
              (TmAppl [TmVar "A", TmVar "a"]) 
              (TmAppl [TmVar "A", TmVar "a"]))
            `shouldBe`
            UnboundNameInTerm ["a"]
        it "unbounded tm" $
          checkAllNameBounded ctx 
            (TmLambda "a" 
              (TmAppl [TmVar "A", TmVar "B"]) 
              (TmAppl [TmVar "A", TmVar "b"]))
            `shouldBe`
            UnboundNameInTerm ["b"]
      describe "TmFix" $ do
        it "bounded" $
          checkAllNameBounded ctx (TmFix (-1) (TmVar "A")) `shouldBe` AllNameBounded
        it "unbounded" $
          checkAllNameBounded ctx (TmFix (-1) (TmVar "a")) `shouldBe` UnboundNameInTerm ["a"]
      describe "TmLetIn" $ do
        it "bounded" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "A")
              (TmVar "B")
              (TmAppl [TmVar "A", TmVar "x"]))
          `shouldBe`
          AllNameBounded
        it "unbounded ty" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "x")
              (TmVar "B")
              (TmAppl [TmVar "A", TmVar "x"]))
          `shouldBe`
          UnboundNameInTerm ["x"]
        it "unbounded tm" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "A")
              (TmVar "x")
              (TmAppl [TmVar "A", TmVar "x"]))
          `shouldBe`
          UnboundNameInTerm ["x"]
        it "unbounded bdy" $
          checkAllNameBounded ctx
            (TmLetIn "x" 
              (TmVar "A")
              (TmVar "B")
              (TmAppl [TmVar "A", TmVar "y"]))
          `shouldBe`
          UnboundNameInTerm ["y"]
      describe "TmType" $
        it "bounded" $ checkAllNameBounded ctx TmType `shouldBe` AllNameBounded
      describe "TmMatch (-1)" $ do
        it "Bounded" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "n"])])
          `shouldBe`
          AllNameBounded
        it "Bounded-2" $
          checkAllNameBounded natContextWithPredefinedNumbers
            (TmMatch (-1) (TmVar "plus") "x0" ["eq","_","b","c"] (TmVar "nat")
              [ Equation ["eqrefl","_","a"] (TmVar "a")])
          `shouldBe`
          AllNameBounded
        it "NoIndTypeProvided" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" [] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "n"])])
          `shouldBe`
          NoIndTypeProvided
            (TmMatch (-1) (TmVar "plus") "x0" [] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "n"])])
        it "UnknownIndType" $
          checkAllNameBounded natContextWithPredefinedNumbers
            (TmMatch (-1) (TmVar "one") "x0" ["t","r"] (TmAppl [TmVar "A", TmVar "t"])
              [ Equation ["a"] (TmVar "A")
              , Equation ["a", "b"] (TmAppl [TmVar "A", TmVar "b"])])
          `shouldBe`
          UnknownIndType
            (TmMatch (-1) (TmVar "one") "x0" ["t","r"] (TmAppl [TmVar "A", TmVar "t"])
              [ Equation ["a"] (TmVar "A")
              , Equation ["a", "b"] (TmAppl [TmVar "A", TmVar "b"])]) "t"
        it "WrongNumParamsInTypeMatching" $
          checkAllNameBounded natContextWithPredefinedNumbers
            (TmMatch (-1) (TmVar "plus") "x0" ["nat", "p"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "n"])])
          `shouldBe`
          WrongNumParamsInTypeMatching
            (TmMatch (-1) (TmVar "plus") "x0" ["nat", "p"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "n"])]) ["nat", "p"]
        it "WrongNumParamsInTypeMatching-2" $
          checkAllNameBounded natContextWithPredefinedNumbers
            (TmMatch (-1) (TmVar "v") "x0" ["eq"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")])
          `shouldBe`
          WrongNumParamsInTypeMatching
            (TmMatch (-1) (TmVar "v") "x0" ["eq"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")]) ["eq"]
        it "WrongNumParamsInTypeMatching-3" $
          checkAllNameBounded natContextWithPredefinedNumbers
            (TmMatch (-1) (TmVar "v") "x0" ["eq","_","b"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")])
          `shouldBe`
          WrongNumParamsInTypeMatching
            (TmMatch (-1) (TmVar "v") "x0" ["eq","_","b"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")]) ["eq","_","b"]
        it "UnusedNameInTypeMatching" $
          checkAllNameBounded natContextWithPredefinedFunctions
            (TmMatch (-1) (TmVar "plus") "x0" ["eq", "a", "b", "c"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")])
          `shouldBe`
          UnusedNameInTypeMatching
            (TmMatch (-1) (TmVar "plus") "x0" ["eq", "a", "b", "c"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")]) ["a"]
        it "DuplicateNameInTypeMatching" $
          checkAllNameBounded natContextWithPredefinedFunctions
            (TmMatch (-1) (TmVar "plus") "x0" ["eq", "_", "b", "b"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")])
          `shouldBe`
          DuplicateNameInTypeMatching
            (TmMatch (-1) (TmVar "plus") "x0" ["eq", "_", "b", "b"] (TmVar "nat")
              [ Equation ["eq_refl","_","a","b"] (TmVar "a")]) ["b"]
        it "UnknownConstr" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["SS", "n"] (TmAppl [TmVar "S", TmVar "n"])])
          `shouldBe`
          UnknownConstr
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["SS", "n"] (TmAppl [TmVar "S", TmVar "n"])]) ["SS"]
        it "DuplicateConstr" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["O"] (TmVar "O")])
          `shouldBe`
          DuplicateConstr
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["O"] (TmVar "O")]) ["O"]
        it "InsufficientConstrs" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")])
          `shouldBe`
          InsufficientConstrs
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")]) ["S"]
        it "InsufficientConstrs-2" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [])
          `shouldBe`
          InsufficientConstrs
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              []) (sort ["S", "O"])
        it "WrongNumParamsInConstrMatching" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n", "b"] (TmAppl [TmVar "S", TmVar "n"])])
          `shouldBe`
          WrongNumParamsInConstrMatching
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n", "b"] (TmAppl [TmVar "S", TmVar "n"])]) ["S", "n", "b"]
        it "UnusedNameInConstrMatching" $
          checkAllNameBounded natContextWithPredefinedNumbers
            (TmMatch (-1) (TmVar "plus") "x0" ["eq","_","b","c"] (TmVar "nat")
              [ Equation ["eqrefl","nat","a"] (TmVar "a")])
          `shouldBe`
          UnusedNameInConstrMatching
            (TmMatch (-1) (TmVar "plus") "x0" ["eq","_","b","c"] (TmVar "nat")
              [ Equation ["eqrefl","nat","a"] (TmVar "a")]) ["eqrefl","nat","a"] ["nat"]
        it "DuplicateNameInConstrMatching" $
          checkAllNameBounded natListContext
            (TmMatch (-1) (TmVar "plus") "x0" ["natList"] (TmVar "natList")
              [ Equation ["natNil"] (TmVar "plus")
              , Equation ["natCons", "t", "t"] (TmVar "t")])
          `shouldBe`
          DuplicateNameInConstrMatching
            (TmMatch (-1) (TmVar "plus") "x0" ["natList"] (TmVar "natList")
            [ Equation ["natNil"] (TmVar "plus")
            , Equation ["natCons", "t", "t"] (TmVar "t")]) ["natCons", "t", "t"] ["t"]
        it "unbounded tm" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "x") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "n"])])
          `shouldBe`
          UnboundNameInTerm ["x"]
        it "unbounded branch constr" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "nat")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "x"])])
          `shouldBe`
          UnboundNameInTerm ["x"]
        it "unbounded rty" $
          checkAllNameBounded natContext
            (TmMatch (-1) (TmVar "plus") "x0" ["nat"] (TmVar "x")
              [ Equation ["O"] (TmVar "O")
              , Equation ["S", "n"] (TmAppl [TmVar "S", TmVar "n"])])
          `shouldBe`
          UnboundNameInTerm ["x"]
    describe "checkAllNameBoundedCommand" $ do
      describe "Ax" $ do
        it "bounded" $
          checkAllNameBoundedCommand natContext
          ( Ax "pluscomm"
            ( TmProd "x"
              ( TmVar "nat" )
              ( TmProd "y"
                ( TmVar "nat" )
                ( TmAppl
                  [ TmVar "eq"
                  , TmVar "nat"
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "x"
                    , TmVar "y" ]
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "y"
                    , TmVar "x" ]]))))
          `shouldBe` AllNameBounded
        it "unbounded" $
          checkAllNameBoundedCommand natContext
          ( Ax "pluscomm"
            ( TmProd "x"
              ( TmVar "nat1" )
              ( TmProd "y"
                ( TmVar "nat" )
                ( TmAppl
                  [ TmVar "eq"
                  , TmVar "nat"
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "x"
                    , TmVar "y" ]
                  , TmAppl
                    [ TmVar "plus"
                    , TmVar "y"
                    , TmVar "z" ]]))))
          `shouldBe` UnboundNameInTerm ["nat1","z"]
      describe "Def" $ do
        it "bounded" $
          checkAllNameBoundedCommand natContext
          ( Def "plus2"
            ( TmProd "x"
              ( TmVar "nat" )
              ( TmProd "y"
                ( TmVar "nat" )
                ( TmVar "nat" )))
            ( TmLambda "x"
              ( TmVar "nat" )
              ( TmLambda "y"
                ( TmVar "nat" )
                ( TmAppl
                  [ TmVar "plus"
                  , TmVar "x"
                  , TmVar "y" ]))))
          `shouldBe` AllNameBounded
        it "unbounded" $
          checkAllNameBoundedCommand natContext
          ( Def "minus"
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
                    ( TmVar "O" )
                  , Equation
                    [ "S"
                    , "xx" ]
                    ( TmMatch (-1)
                      ( TmVar "y" )
                      "y0"
                      [ "nat" ]
                      ( TmVar "nat" )
                      [ Equation
                        [ "O" ]
                        ( TmVar "x" )
                      , Equation
                        [ "S"
                        , "yy" ]
                        ( TmAppl
                          [ TmVar "minus"
                          , TmVar "xx"
                          , TmVar "yy" ])])]))))
          `shouldBe` UnboundNameInTerm ["minus"]
      describe "Ind" $ do
        it "bounded" $
          checkAllNameBoundedCommand natContext
          ( Ind "natlist" 0
              TmType
            ( TmIndType "natlist" [])
            [ ( "nil"
              , TmIndType "natlist" []
              , TmConstr "nil" [])
            , ( "cons"
              , TmProd "_"
                ( TmVar "nat" )
                ( TmProd "_"
                  ( TmIndType "natlist" [])
                  ( TmIndType "natlist" []))
              , TmLambda ".0"
                ( TmVar "nat" )
                ( TmLambda ".1"
                  ( TmIndType "natlist" [])
                  ( TmConstr "cons"
                    [ TmVar ".0"
                    , TmVar ".1" ])))])
          `shouldBe` AllNameBounded
        it "unbounded" $
          checkAllNameBoundedCommand natContext
          ( Ind "natlist" 0
              TmType
            ( TmIndType "natlist" [])
            [ ( "nil"
              , TmIndType "natlist1" []
              , TmConstr "nil" [])
            , ( "cons"
              , TmProd "_"
                ( TmVar "nat" )
                ( TmProd "_"
                  ( TmIndType "natlist" [])
                  ( TmIndType "natlist" []))
              , TmLambda ".0"
                ( TmVar "nat" )
                ( TmLambda ".1"
                  ( TmIndType "natlist" [])
                  ( TmConstr "cons1"
                    [ TmVar ".0"
                    , TmVar ".11" ])))])
          `shouldBe` UnboundNameInTerm (sort [".11", "cons1", "natlist1"])
      describe "Fix" $ do
        it "bounded" $
          checkAllNameBoundedCommand natContext
          ( Fix "plus1"
            ( TmLambda "plus1"
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
                      , "xx" ]
                      ( TmAppl
                        [ TmVar "S"
                        , TmAppl
                          [ TmVar "plus1"
                          , TmVar "xx"
                          , TmVar "y" ]])])))))
          `shouldBe` AllNameBounded
        it "unbounded" $
          checkAllNameBoundedCommand natContext
          ( Fix "plus1"
            ( TmLambda "plus1"
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
                    ( TmVar "nat2" )
                    [ Equation
                      [ "O" ]
                      ( TmVar "y2" )
                    , Equation
                      [ "S"
                      , "xx" ]
                      ( TmAppl
                        [ TmVar "S"
                        , TmAppl
                          [ TmVar "plus2"
                          , TmVar "xx2"
                          , TmVar "y2" ]])])))))
          `shouldBe` UnboundNameInTerm (sort ["nat2", "y2", "xx2", "plus2"])