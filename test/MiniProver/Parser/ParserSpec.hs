module MiniProver.Parser.ParserSpec (main, spec) where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Parser.Parser
import Text.Megaparsec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "simple" $ do
    describe "binder" $ 
      describe "type" $ 
        it "Type" $
          parse pbinder "" "(name:Type)" `shouldParse` ("name",TmType)
    describe "tmtype" $
      it "Type" $
        parse ptmtype "" "Type" `shouldParse` TmType
    describe "tmprod" $ do
      it "single" $
        parse pforall "" "forall (x:Type), Type" `shouldParse` 
          TmProd "x" TmType TmType
      it "multiple" $
        parse pforall "" "forall (x:Type) (y:Type) (z:Type), Type" `shouldParse`
          TmProd "x" TmType 
          (TmProd "y" TmType
          (TmProd "z" TmType TmType))
    describe "tmfun" $ do
      it "zero" $
        parse pfun "" "fun => Type" `shouldParse` TmType
      it "single" $
        parse pfun "" "fun (x:Type) => Type" `shouldParse` 
          TmLambda "x" TmType TmType
      it "multiple" $
        parse pfun "" "fun (x:Type) (y:Type) (z:Type) => Type" `shouldParse`
          TmLambda "x" TmType 
          (TmLambda "y" TmType
          (TmLambda "z" TmType TmType))
    describe "tmfix" $
      it "single" $
        parse pfix "" "fix plus (x:nat) (y:nat):nat:=match x as x0 in nat return nat with |O => y|S xx => plus xx (S y) end" `shouldParse`
          TmFix (-1)
            (TmLambda "plus"
              (TmProd "x"
                (TmVar "nat")
                (TmProd "y"
                  (TmVar "nat")
                  (TmVar "nat")))
              (TmLambda "x"
                (TmVar "nat")
                (TmLambda "y"
                  (TmVar "nat")
                  (TmMatch (-1)
                    (TmVar "x")
                    "x0"
                    [ "nat" ]
                    (TmVar "nat")
                    [ Equation ["O"]
                        (TmVar "y")
                    , Equation ["S", "xx"]
                        (TmAppl
                          [ TmVar "plus"
                          , TmVar "xx"
                          , TmAppl
                              [ TmVar "S"
                              , TmVar "y"]])]))))
    describe "tmletin" $ do
      it "zero" $
        parse pletin "" "let f:Type:=Type in Type" `shouldParse`
          TmLetIn "f" TmType TmType TmType
      it "single" $
        parse pletin "" "let f (x:Type):Type:=Type in Type" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" TmType TmType) 
            (TmLambda "x" TmType TmType)
            TmType
      it "multiple" $
        parse pletin "" "let f (x:Type) (y:Type) (z:Type):Type:=Type in Type" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" TmType
              (TmProd "y" TmType
                (TmProd "z" TmType
                  TmType)))
            (TmLambda "x" TmType
              (TmLambda "y" TmType
                (TmLambda "z" TmType
                  TmType)))
            TmType
    describe "arrow(tmprod)" $ do
      it "single" $
        parse parrow "" "Type -> Type" `shouldParse` TmProd "_" TmType TmType
      it "multiple" $
        parse parrow "" "Type -> Type -> Type" `shouldParse` 
          TmProd "_" TmType
            (TmProd "_" TmType
              TmType)
      describe "parens" $ do
        it "(A->B)->C" $
          parse parrow "" "(Type -> Type) -> Type" `shouldParse`
            TmProd "_" (TmProd "_" TmType TmType) TmType
        it "A->(B->C)" $
          parse parrow "" "Type -> (Type -> Type)" `shouldParse` 
            TmProd "_" TmType
              (TmProd "_" TmType
                TmType)
        it "complex" $
          parse parrow "" "Type -> (((Type -> Type)) -> ((Type -> (Type -> Type)))) -> Type" `shouldParse`
            TmProd "_"
              TmType
              (TmProd "_"
                (TmProd "_"
                  (TmProd "_"
                    TmType
                    TmType)
                  (TmProd "_"
                    TmType
                    (TmProd "_"
                      TmType
                      TmType)))
                TmType)
      describe "app" $ do
        it "single" $
          parse papp "" "Type Type" `shouldParse` 
            TmAppl [TmType, TmType]
        it "multiple" $
          parse papp "" "Type Type Type" `shouldParse` 
            TmAppl [TmType, TmType, TmType]
      describe "equation" $
        it "equation" $
          parse pequation "" "|a b c => Type" `shouldParse` 
            Equation ["a","b","c"] TmType
      describe "match" $ do
        it "empty" $
          parse pmatch "" "match Type as t in x return x with end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x"] (TmVar "x") []
        it "single" $
          parse pmatch "" "match Type as t in x return x with |a => Type end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x"] (TmVar "x") [Equation ["a"] TmType]
        it "multiple" $
          parse pmatch "" "match Type as t in x return x with |a => Type |b c=>Type|c=>Type end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x"] (TmVar "x") [
                Equation ["a"] TmType
              , Equation ["b", "c"] TmType
              , Equation ["c"] TmType
              ]
        it "long type" $
          parse pmatch "" "match Type as t in x y z return x y z with |a => Type end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x", "y", "z"] (TmAppl [TmVar "x", TmVar "y", TmVar "z"]) [Equation ["a"] TmType]
        it "underscore" $
          parse pmatch "" "match e as e0 in eq _ _ y0 return P y0 e0 with | eqrefl _ _ => f end" `shouldParse`
            TmMatch (-1) (TmVar "e") "e0" ["eq", "_", "_", "y0"]
              (TmAppl [TmVar "P", TmVar "y0", TmVar "e0"])
              [Equation ["eqrefl", "_", "_"] (TmVar "f")]
  describe "simple term" $ do
    describe "tmtype" $
      it "Type" $
        parse pterm "" "Type" `shouldParse` TmType
    describe "tmprod" $ do
      it "single" $
        parse pterm "" "forall (x:Type), Type" `shouldParse` 
          TmProd "x" TmType TmType
      it "multiple" $
        parse pterm "" "forall (x:Type) (y:Type) (z:Type), Type" `shouldParse`
          TmProd "x" TmType 
          (TmProd "y" TmType
          (TmProd "z" TmType TmType))
    describe "tmfun" $ do
      it "zero" $
        parse pterm "" "fun => Type" `shouldParse` TmType
      it "single" $
        parse pterm "" "fun (x:Type) => Type" `shouldParse` 
          TmLambda "x" TmType TmType
      it "multiple" $
        parse pterm "" "fun (x:Type) (y:Type) (z:Type) => Type" `shouldParse`
          TmLambda "x" TmType 
          (TmLambda "y" TmType
          (TmLambda "z" TmType TmType))
    describe "tmletin" $ do
      it "zero" $
        parse pterm "" "let f:Type:=Type in Type" `shouldParse`
          TmLetIn "f" TmType TmType TmType
      it "single" $
        parse pterm "" "let f (x:Type):Type:=Type in Type" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" TmType TmType) 
            (TmLambda "x" TmType TmType)
            TmType
      it "multiple" $
        parse pterm "" "let f (x:Type) (y:Type) (z:Type):Type:=Type in Type" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" TmType
              (TmProd "y" TmType
                (TmProd "z" TmType
                  TmType)))
            (TmLambda "x" TmType
              (TmLambda "y" TmType
                (TmLambda "z" TmType
                  TmType)))
            TmType
    describe "arrow(tmprod)" $ do
      it "single" $
        parse pterm "" "Type -> Type" `shouldParse` TmProd "_" TmType TmType
      it "multiple" $
        parse pterm "" "Type -> Type -> Type" `shouldParse` 
          TmProd "_" TmType
            (TmProd "_" TmType
              TmType)
      describe "parens" $ do
        it "(A->B)->C" $
          parse pterm "" "(Type -> Type) -> Type" `shouldParse`
            TmProd "_" (TmProd "_" TmType TmType) TmType
        it "A->(B->C)" $
          parse pterm "" "Type -> (Type -> Type)" `shouldParse` 
            TmProd "_" TmType
              (TmProd "_" TmType
                TmType)
        it "complex" $
          parse pterm "" "Type -> (((Type -> Type)) -> ((Type -> (Type -> Type)))) -> Type" `shouldParse`
            TmProd "_"
              TmType
              (TmProd "_"
                (TmProd "_"
                  (TmProd "_"
                    TmType
                    TmType)
                  (TmProd "_"
                    TmType
                    (TmProd "_"
                      TmType
                      TmType)))
                TmType)
      describe "app" $ do
        it "single" $
          parse pterm "" "Type Type" `shouldParse` 
            TmAppl [TmType, TmType]
        it "multiple" $
          parse pterm "" "Type Type Type" `shouldParse` 
            TmAppl [TmType, TmType, TmType]
      describe "match" $ do
        it "empty" $
          parse pterm "" "match Type as t in x return x with end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x"] (TmVar "x") []
        it "single" $
          parse pterm "" "match Type as t in x return x with |a => Type end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x"] (TmVar "x") [Equation ["a"] TmType]
        it "multiple" $
          parse pterm "" "match Type as t in x return x with |a => Type |b c=>Type|c=>Type end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x"] (TmVar "x") [
                Equation ["a"] TmType
              , Equation ["b", "c"] TmType
              , Equation ["c"] TmType
              ]
        it "long type" $
          parse pterm "" "match Type as t in x y z return x y z with |a => Type end" `shouldParse` 
            TmMatch (-1) TmType "t" ["x", "y", "z"] (TmAppl [TmVar "x", TmVar "y", TmVar "z"]) [Equation ["a"] TmType]
        it "underscore" $
          parse pterm "" "match e as e0 in eq _ _ y0 return P y0 e0 with | eqrefl _ _ => f end" `shouldParse`
            TmMatch (-1) (TmVar "e") "e0" ["eq", "_", "_", "y0"]
              (TmAppl [TmVar "P", TmVar "y0", TmVar "e0"])
              [Equation ["eqrefl", "_", "_"] (TmVar "f")]
  describe "complex term" $ do
    it "var" $
      parse pterm "" "a" `shouldParse` TmVar "a"
    it "1" $
      parse pterm "" "(forall (a:A), a Type) b Type -> Type d" `shouldParse`
        TmProd "_"
          (TmAppl
            [ TmProd "a" (TmVar "A") 
                (TmAppl [TmVar "a", TmType])
            , TmVar "b"
            , TmType])
          (TmAppl [TmType, TmVar "d"])
    it "2" $
      parse pterm "" "a -> forall (b:c) (e:f),d -> e -> forall (b:c),d -> f" `shouldParse`
        TmProd "_"
          (TmVar "a")
          (TmProd "b"
            (TmVar "c")
            (TmProd "e"
              (TmVar "f")
              (TmProd "_"
                (TmVar "d")
                (TmProd "_"
                  (TmVar "e")
                  (TmProd "b"
                    (TmVar "c")
                    (TmProd "_"
                      (TmVar "d")
                      (TmVar "f")))))))
    it "3" $
      parse pterm "" ("fun (a:forall (b:Type) (c:d->e->forall (p:q),p->q), c b) (b:forall (c:d),e) =>"
        ++ "let a (b:c) : d := e in "
        ++ "match a Type as t in x return x with |b c => forall (c:d), e end")
        `shouldParse`
        TmLambda "a"
          (TmProd "b"
            TmType
            (TmProd "c"
              (TmProd "_"
                (TmVar "d")
                (TmProd "_"
                  (TmVar "e")
                  (TmProd "p"
                    (TmVar "q")
                    (TmProd "_"
                      (TmVar "p")
                      (TmVar "q")))))
              (TmAppl [TmVar "c", TmVar "b"])))
          (TmLambda "b"
            (TmProd "c"
              (TmVar "d")
              (TmVar "e"))
            (TmLetIn "a"
              (TmProd "b"
                (TmVar "c")
                (TmVar "d"))
              (TmLambda "b"
                (TmVar "c")
                (TmVar "e"))
              (TmMatch (-1)
                (TmAppl
                  [ TmVar "a"
                  , TmType ])
                "t"
                [ "x" ]
                (TmVar "x")
                [ Equation ["b", "c"]
                    (TmProd "c"
                      (TmVar "d")
                      (TmVar "e"))])))
  describe "command" $ do
    it "axiom" $
      parse paxiom "" "Axiom a:b->c." `shouldParse`
        Ax "a" (TmProd "_" (TmVar "b") (TmVar "c"))
    it "definition" $
      parse pdefinition "" "Definition a (b:c) (d:e) : f -> g := a b c." `shouldParse`
        Def "a"
          (TmProd "b"
            (TmVar "c")
            (TmProd "d"
              (TmVar "e")
              (TmProd "_"
                (TmVar "f")
                (TmVar "g"))))
          (TmLambda "b"
            (TmVar "c")
            (TmLambda "d"
              (TmVar "e")
              (TmAppl
                [ TmVar "a"
                , TmVar "b"
                , TmVar "c"])))
    describe "inductive" $ do
      it "simple" $
        parse pinductive "" ("Inductive r1 (A:Type) (B:Type) : A -> A -> B -> B -> Type :="
          ++ "| p : forall (x:A),forall (y:B),forall (z:B), r1 A B x x y z "
          ++ "| q : forall (x:A),forall (y:A),forall (z:B),r1 A B x y z z.") `shouldParse`
          Ind "r1" 2
            (TmProd "A"
              TmType
              (TmProd "B"
                TmType
                (TmProd "_"
                  (TmVar "A")
                  (TmProd "_"
                    (TmVar "A")
                    (TmProd "_"
                      (TmVar "B")
                      (TmProd "_"
                        (TmVar "B")
                        TmType))))))
            (TmLambda "A"
              TmType
              (TmLambda "B"
                TmType
                (TmLambda ".0"
                  (TmVar "A")
                  (TmLambda ".1"
                    (TmVar "A")
                    (TmLambda ".2"
                      (TmVar "B")
                      (TmLambda ".3"
                        (TmVar "B")
                        (TmIndType "r1" 
                          [ TmVar "A", TmVar "B", TmVar ".0"
                          , TmVar ".1", TmVar ".2", TmVar ".3"])))))))
            [ ( "p"
              , TmProd "A"
                  TmType
                  (TmProd "B"
                    TmType
                    (TmProd "x"
                      (TmVar "A")
                      (TmProd "y"
                        (TmVar "B")
                        (TmProd "z"
                          (TmVar "B")
                          (TmIndType "r1"
                            [ TmVar "A"
                            , TmVar "B"
                            , TmVar "x"
                            , TmVar "x"
                            , TmVar "y"
                            , TmVar "z" ])))))
              , TmLambda "A"
                  TmType
                  (TmLambda "B"
                    TmType
                    (TmLambda "x"
                      (TmVar "A")
                      (TmLambda "y"
                        (TmVar "B")
                        (TmLambda "z"
                          (TmVar "B")
                          (TmConstr "p" 
                            [TmVar "A", TmVar "B", TmVar "x", TmVar "y", TmVar "z"]))))))
            , ( "q",
                TmProd "A"
                  TmType
                  (TmProd "B"
                    TmType
                    (TmProd "x"
                      (TmVar "A")
                      (TmProd "y"
                        (TmVar "A")
                        (TmProd "z"
                          (TmVar "B")
                          (TmIndType "r1"
                            [ TmVar "A"
                            , TmVar "B"
                            , TmVar "x"
                            , TmVar "y"
                            , TmVar "z"
                            , TmVar "z" ])))))
                , TmLambda "A"
                  TmType
                  (TmLambda "B"
                    TmType
                    (TmLambda "x"
                      (TmVar "A")
                      (TmLambda "y"
                        (TmVar "A")
                        (TmLambda "z"
                          (TmVar "B")
                          (TmConstr "q" 
                            [TmVar "A", TmVar "B", TmVar "x", TmVar "y", TmVar "z"]))))))]
      it "le" $
        parse pinductive "" ("Inductive le (x:nat):nat->Type:= "
          ++ "|lerefl:le x x|leS:forall (y:nat), (le x y) -> (le x (S y)).")
          `shouldParse`
          Ind "le" 1
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
                      (TmConstr "leS" [TmVar "x", TmVar "y", TmVar ".0"]))))]
      it "btree" $
        parse pinductive "" ("Inductive btree (x:Type) : Type :="
          ++ "| leaf : x -> btree x"
          ++ "| node : x -> btree x -> btree x -> btree x.") `shouldParse`
          Ind "btree" 1
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
                ( TmType )
                ( TmProd "_"
                  ( TmVar "x" )
                  ( TmProd "_"
                    ( TmIndType "btree" [TmVar "x"] )
                    ( TmProd "_"
                      ( TmIndType "btree" [TmVar "x"] )
                      ( TmIndType "btree" [TmVar "x"] ))))
              , TmLambda "x"
                ( TmType )
                ( TmLambda ".0"
                  ( TmVar "x" )
                  ( TmLambda ".1"
                    ( TmIndType "btree" [TmVar "x"] )
                    ( TmLambda ".2"
                      ( TmIndType "btree" [TmVar "x"] )
                      ( TmConstr "node" [TmVar "x", TmVar ".0", TmVar ".1", TmVar ".2"])))))]
    describe "fixpoint" $
      it "single" $
        parse pfixdefinition "" 
          ( "Fixpoint plus (x:nat) (y:nat):nat:="
          ++ "match x as x0 in t return t with |O => y|S xx => plus xx (S y) end.")
          `shouldParse`
          Fix "plus"
          ( TmFix (-1)
            (TmLambda "plus"
              (TmProd "x"
                (TmVar "nat")
                (TmProd "y"
                  (TmVar "nat")
                  (TmVar "nat")))
              (TmLambda "x"
                (TmVar "nat")
                (TmLambda "y"
                  (TmVar "nat")
                  (TmMatch (-1)
                    (TmVar "x")
                    "x0"
                    [ "t" ]
                    (TmVar "t")
                    [ Equation ["O"]
                        (TmVar "y")
                    , Equation ["S", "xx"]
                        (TmAppl
                          [ TmVar "plus"
                          , TmVar "xx"
                          , TmAppl
                              [ TmVar "S"
                              , TmVar "y"]])])))))
  describe "pcommand" $ do
    it "axiom" $
      parse pcommand "" "Axiom a:b->c." `shouldParse`
        Ax "a" (TmProd "_" (TmVar "b") (TmVar "c"))
    it "definition" $
      parse pcommand "" "Definition a (b:c) (d:e) : f -> g := a b c." `shouldParse`
        Def "a"
          (TmProd "b"
            (TmVar "c")
            (TmProd "d"
              (TmVar "e")
              (TmProd "_"
                (TmVar "f")
                (TmVar "g"))))
          (TmLambda "b"
            (TmVar "c")
            (TmLambda "d"
              (TmVar "e")
              (TmAppl
                [ TmVar "a"
                , TmVar "b"
                , TmVar "c"])))
    describe "inductive" $ do
      it "simple" $
        parse pcommand "" ("Inductive r1 (A:Type) (B:Type) : A -> A -> B -> B -> Type :="
          ++ "| p : forall (x:A),forall (y:B),forall (z:B), r1 A B x x y z "
          ++ "| q : forall (x:A),forall (y:A),forall (z:B),r1 A B x y z z.") `shouldParse`
          Ind "r1" 2
            (TmProd "A"
              TmType
              (TmProd "B"
                TmType
                (TmProd "_"
                  (TmVar "A")
                  (TmProd "_"
                    (TmVar "A")
                    (TmProd "_"
                      (TmVar "B")
                      (TmProd "_"
                        (TmVar "B")
                        TmType))))))
            (TmLambda "A"
              TmType
              (TmLambda "B"
                TmType
                (TmLambda ".0"
                  (TmVar "A")
                  (TmLambda ".1"
                    (TmVar "A")
                    (TmLambda ".2"
                      (TmVar "B")
                      (TmLambda ".3"
                        (TmVar "B")
                        (TmIndType "r1" 
                          [ TmVar "A", TmVar "B", TmVar ".0"
                          , TmVar ".1", TmVar ".2", TmVar ".3"])))))))
            [ ( "p"
              , TmProd "A"
                  TmType
                  (TmProd "B"
                    TmType
                    (TmProd "x"
                      (TmVar "A")
                      (TmProd "y"
                        (TmVar "B")
                        (TmProd "z"
                          (TmVar "B")
                          (TmIndType "r1"
                            [ TmVar "A"
                            , TmVar "B"
                            , TmVar "x"
                            , TmVar "x"
                            , TmVar "y"
                            , TmVar "z" ])))))
              , TmLambda "A"
                  TmType
                  (TmLambda "B"
                    TmType
                    (TmLambda "x"
                      (TmVar "A")
                      (TmLambda "y"
                        (TmVar "B")
                        (TmLambda "z"
                          (TmVar "B")
                          (TmConstr "p" 
                            [TmVar "A", TmVar "B", TmVar "x", TmVar "y", TmVar "z"]))))))
            , ( "q",
                TmProd "A"
                  TmType
                  (TmProd "B"
                    TmType
                    (TmProd "x"
                      (TmVar "A")
                      (TmProd "y"
                        (TmVar "A")
                        (TmProd "z"
                          (TmVar "B")
                          (TmIndType "r1"
                            [ TmVar "A"
                            , TmVar "B"
                            , TmVar "x"
                            , TmVar "y"
                            , TmVar "z"
                            , TmVar "z" ])))))
                , TmLambda "A"
                  TmType
                  (TmLambda "B"
                    TmType
                    (TmLambda "x"
                      (TmVar "A")
                      (TmLambda "y"
                        (TmVar "A")
                        (TmLambda "z"
                          (TmVar "B")
                          (TmConstr "q" 
                            [TmVar "A", TmVar "B", TmVar "x", TmVar "y", TmVar "z"]))))))]
      it "le" $
        parse pcommand "" ("Inductive le (x:nat):nat->Type:= "
          ++ "|lerefl:le x x|leS:forall (y:nat), (le x y) -> (le x (S y)).")
          `shouldParse`
          Ind "le" 1
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
                      (TmConstr "leS" [TmVar "x", TmVar "y", TmVar ".0"]))))]
      it "btree" $
        parse pcommand "" ("Inductive btree (x:Type) : Type :="
          ++ "| leaf : x -> btree x"
          ++ "| node : x -> btree x -> btree x -> btree x.") `shouldParse`
          Ind "btree" 1
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
                ( TmType )
                ( TmProd "_"
                  ( TmVar "x" )
                  ( TmProd "_"
                    ( TmIndType "btree" [TmVar "x"] )
                    ( TmProd "_"
                      ( TmIndType "btree" [TmVar "x"] )
                      ( TmIndType "btree" [TmVar "x"] ))))
              , TmLambda "x"
                ( TmType )
                ( TmLambda ".0"
                  ( TmVar "x" )
                  ( TmLambda ".1"
                    ( TmIndType "btree" [TmVar "x"] )
                    ( TmLambda ".2"
                      ( TmIndType "btree" [TmVar "x"] )
                      ( TmConstr "node" [TmVar "x", TmVar ".0", TmVar ".1", TmVar ".2"])))))]
      it "nattree" $
        parse pcommand "" ("Inductive nattree (A:Type) : Type :=" ++
          "| leaf : nattree A | node : A -> ((nat -> (nattree A)) -> (nattree A)).")
        `shouldParse`
        Ind "nattree" 1
        ( TmProd "A"
            TmType
            TmType )
        ( TmLambda "A"
            TmType
          ( TmIndType "nattree"
            [ TmVar "A" ]))
        [ ( "leaf"
          , TmProd "A"
              TmType
            ( TmIndType "nattree"
              [ TmVar "A" ])
          , TmLambda "A"
              TmType
            ( TmConstr "leaf"
              [ TmVar "A" ]))
        , ( "node"
          , TmProd "A"
              TmType
            ( TmProd "_"
              ( TmVar "A" )
              ( TmProd "_"
                ( TmProd "_"
                  ( TmVar "nat" )
                  ( TmIndType "nattree"
                    [ TmVar "A" ]))
                ( TmIndType "nattree"
                  [ TmVar "A" ])))
          , TmLambda "A"
              TmType
            ( TmLambda ".0"
              ( TmVar "A" )
              ( TmLambda ".1"
                ( TmProd "_"
                  ( TmVar "nat" )
                  ( TmIndType "nattree"
                    [ TmVar "A" ]))
                ( TmConstr "node"
                  [ TmVar "A"
                  , TmVar ".0"
                  , TmVar ".1" ]))))]
    describe "fixpoint" $
      it "single" $
        parse pcommand "" 
          ( "Fixpoint plus (x:nat) (y:nat):nat:="
          ++ "match x as x0 in t return t with |O => y|S xx => plus xx (S y) end.")
          `shouldParse`
          Fix "plus"
          ( TmFix (-1)
            (TmLambda "plus"
              (TmProd "x"
                (TmVar "nat")
                (TmProd "y"
                  (TmVar "nat")
                  (TmVar "nat")))
              (TmLambda "x"
                (TmVar "nat")
                (TmLambda "y"
                  (TmVar "nat")
                  (TmMatch (-1)
                    (TmVar "x")
                    "x0"
                    [ "t" ]
                    (TmVar "t")
                    [ Equation ["O"]
                        (TmVar "y")
                    , Equation ["S", "xx"]
                        (TmAppl
                          [ TmVar "plus"
                          , TmVar "xx"
                          , TmAppl
                              [ TmVar "S"
                              , TmVar "y"]])])))))