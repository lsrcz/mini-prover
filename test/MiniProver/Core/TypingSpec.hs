module MiniProver.Core.TypingSpec (main, spec) where

import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Utils.ContextForTesting
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = 
  describe "typeof" $ do
    describe "TmRel" $
      it "plus" $
        typeof natContext (TmRel "plus" 0) `shouldBe` 
          Right
          ( TmProd "a"
            ( TmIndType "nat" [] )
            ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] )))
    describe "TmAppl" $ do
      it "plus 1 2" $
        typeof natContextWithPredefinedNumbers 
          ( TmAppl
            [ TmRel "plus" 3
            , TmRel "one" 1
            , TmRel "two" 2 ])
          `shouldBe`
          Right
            ( TmIndType "nat" [] )
      it "partial -- plus 1" $
        typeof natContextWithPredefinedNumbers 
          ( TmAppl
            [ TmRel "plus" 3
            , TmRel "one" 1 ])
          `shouldBe`
          Right
          ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] ))
    describe "TmProd" $
      it "simple" $
        typeof natContextWithPredefinedNumbers
          ( TmProd "a"
            ( TmIndType "nat" [] )
            ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] )))
        `shouldBe`
        Right TmType
    describe "TmLambda" $ do
      it "simple" $
        typeof natContextWithPredefinedNumbers
          ( TmLambda "x"
            ( TmIndType "nat" [] )
            ( TmAppl 
              [ TmRel "plus" 4
              , TmRel "one" 2
              , TmRel "x" 0 ]))
        `shouldBe`
        Right
        ( TmProd "x"
          ( TmIndType "nat" [] )
          ( TmIndType "nat" [] ))
      it "simple-2" $
        -- Definition cons2 (T:Type) (a:T) (b:T) (ls:list T) := cons T a (cons T b ls).
        typeof listContext
          ( TmLambda "T"
            TmType
            ( TmLambda "a"
              ( TmRel "T" 0 )
              ( TmLambda "b"
                ( TmRel "T" 1 )
                ( TmLambda "ls"
                  ( TmIndType "list"
                    [ TmRel "T" 2 ])
                  ( TmConstr "cons"
                    [ TmRel "T" 3
                    , TmRel "a" 2
                    , TmConstr "cons"
                      [ TmRel "T" 3
                      , TmRel "b" 1
                      , TmRel "ls" 0 ]])))))
        `shouldBe`
        Right
        ( TmProd "T"
            TmType
            ( TmProd "a"
              ( TmRel "T" 0 )
              ( TmProd "b"
                ( TmRel "T" 1 )
                ( TmProd "ls"
                  ( TmIndType "list"
                    [ TmRel "T" 2 ])
                  ( TmIndType "list"
                    [ TmRel "T" 3 ])))))
    describe "TmFix" $
      it "fix plus" $
      -- fix plus (x:nat) (y:nat):nat:=
      --   match x in nat return nat with
      --   | O => y
      --   | S xx => plus xx (S y) 
      --   end
        typeof natContext
          ( TmFix
            ( TmLambda "plus"
              ( TmProd "x"
                ( TmIndType "nat" [] )
                ( TmProd "y"
                  ( TmIndType "nat" [] )
                  ( TmIndType "nat" [] )))
              (TmLambda "x"
                ( TmIndType "nat" [] )
                (TmLambda "y"
                  ( TmIndType "nat" [] )
                  (TmMatch
                    ( TmRel "x" 1 )
                    [ "nat" ]
                    ( TmIndType "nat" [] )
                    [ Equation ["O"]
                        ( TmRel "y" 0 )
                    , Equation ["S", "xx"]
                        (TmAppl
                          [ TmRel "plus" 3
                          , TmRel "xx" 0
                          , TmConstr "S"
                            [ TmRel "y" 1 ]])])))))
          `shouldBe`
          Right
          ( TmProd "x"
            ( TmIndType "nat" [] )
            ( TmProd "y"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] )))
    describe "TmLetIn" $
      it "simple" $
        typeof natContextWithPredefinedNumbers
          (TmLetIn "f" 
            ( TmProd "x"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] ))
            ( TmLambda "x"
              ( TmIndType "nat" [] )
              ( TmAppl
                [ TmRel "plus" 4
                , TmRel "x" 0
                , TmRel "one" 2 ]))
            ( TmAppl
              [ TmRel "plus" 4
              , TmRel "two" 3
              , TmAppl
                [ TmRel "f" 0
                , TmRel "one" 2 ]]))
          `shouldBe`
          Right
          ( TmIndType "nat" [] )
    describe "TmIndType" $
      it "simple" $
        typeof natContextWithPredefinedNumbers
          ( TmIndType "nat" [] )
        `shouldBe`
        Right TmType
    describe "TmConstr" $ do
      it "simple-1" $
        typeof natContextWithPredefinedNumbers
          ( TmConstr "O" [] )
        `shouldBe`
        Right ( TmIndType "nat" [] )
      it "simple-2" $
        typeof natContextWithPredefinedNumbers
          ( TmConstr "S"
            [ TmConstr "O" [] ])
        `shouldBe`
        Right ( TmIndType "nat" [] )
    describe "TmMatch" $ do
      it "non-dependent" $
        typeof natContextWithPredefinedNumbers
        ( TmMatch
          ( TmRel "one" 1 )
          [ "nat" ]
          ( TmIndType "nat" [] )
          [ Equation ["O"]
              ( TmRel "zero" 0 )
          , Equation ["S", "xx"]
              ( TmRel "xx" 0 )])
        `shouldBe`
        Right ( TmIndType "nat" [] )
      it "dependent" $
        typeof natContextWithPredefinedNumbers
        ( TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmMatch
            ( TmRel "x" 0 )
            [ "nat" ]
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmRel "x" 0
              , TmRel "x" 0 ])
            [ Equation ["O"]
              ( TmConstr "eqrefl"
                [ TmIndType "nat" []
                , TmRel "x" 0 ])
            , Equation ["S", "n"]
              ( TmConstr "eqrefl"
                [ TmIndType "nat" []
                , TmRel "n" 0 ])]))
        `shouldBe`
        Right 
        ( TmProd "x"
          ( TmIndType "nat" [] )
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmRel "x" 0
            , TmRel "x" 0 ]))
      it "f_equal" $
        typeof natContextWithPredefinedNumbers
        ( TmLambda "A"
          TmType
          ( TmLambda "B"
            TmType
            ( TmLambda "f"
              ( TmProd "_"
                ( TmRel "A" 1 )
                ( TmRel "B" 1 ))
              ( TmLambda "x"
                ( TmRel "A" 2 )
                ( TmLambda "y"
                  ( TmRel "A" 3 )
                  ( TmLambda "H"
                    ( TmIndType "eq"
                      [ TmRel "A" 4, TmRel "x" 1, TmRel "y" 0 ])
                    ( TmMatch
                      ( TmRel "H" 0 )
                      [ "eq1", "t", "x0", "y0" ]
                      ( TmIndType "eq1"
                        [ TmRel "B" 7
                        , TmAppl
                          [ TmRel "f" 6
                          , TmRel "x0" 1 ]
                        , TmAppl
                          [ TmRel "f" 6
                          , TmRel "y0" 0 ]])
                      [ Equation ["eqrefl", "t", "x0"]
                        ( TmConstr "eqrefl"
                          [ TmRel "B" 6
                          , TmAppl
                            [ TmRel "f" 5
                            , TmRel "x0" 0 ]])])))))))
        `shouldBe`
        Right
        ( TmProd "A"
          TmType
          ( TmProd "B"
            TmType
            ( TmProd "f"
              ( TmProd "_"
                ( TmRel "A" 1 )
                ( TmRel "B" 1 ))
              ( TmProd "x"
                ( TmRel "A" 2 )
                ( TmProd "y"
                  ( TmRel "A" 3 )
                  ( TmProd "H"
                    ( TmIndType "eq"
                      [ TmRel "A" 4, TmRel "x" 1, TmRel "y" 0 ])
                    ( TmIndType "eq"
                      [ TmRel "B" 4
                      , TmAppl
                        [ TmRel "f" 3
                        , TmRel "x" 2 ]
                      , TmAppl
                        [ TmRel "f" 3
                        , TmRel "y" 1 ]])))))))
