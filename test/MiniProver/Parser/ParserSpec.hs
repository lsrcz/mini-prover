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
      describe "sort" $ 
        it "Prop" $
          parse pbinder "" "(name:Prop)" `shouldParse` ("name",TmSort Prop)
    describe "sort" $ do 
      it "Prop" $ 
        parse psort "" "Prop" `shouldParse` Prop
      it "Set" $ 
        parse psort "" "Set" `shouldParse` Set
      it "Type" $ 
        parse psort "" "Type" `shouldParse` Type
    describe "tmsort" $ do
      it "Prop" $
        parse ptmsort "" "Prop" `shouldParse` TmSort Prop
      it "Set" $
        parse ptmsort "" "Set" `shouldParse` TmSort Set
      it "Type" $
        parse ptmsort "" "Type" `shouldParse` TmSort Type
    describe "tmprod" $ do
      it "single" $
        parse pforall "" "forall (x:Prop), Set" `shouldParse` 
          TmProd "x" (TmSort Prop) (TmSort Set)
      it "multiple" $
        parse pforall "" "forall (x:Prop) (y:Set) (z:Type), Set" `shouldParse`
          TmProd "x" (TmSort Prop) 
          (TmProd "y" (TmSort Set)
          (TmProd "z" (TmSort Type) (TmSort Set)))
    describe "tmfun" $ do
      it "zero" $
        parse pfun "" "fun => Set" `shouldParse` TmSort Set
      it "single" $
        parse pfun "" "fun (x:Prop) => Set" `shouldParse` 
          TmLambda "x" (TmSort Prop) (TmSort Set)
      it "multiple" $
        parse pfun "" "fun (x:Prop) (y:Set) (z:Type) => Set" `shouldParse`
          TmLambda "x" (TmSort Prop) 
          (TmLambda "y" (TmSort Set)
          (TmLambda "z" (TmSort Type) (TmSort Set)))
    describe "tmfix" $
      it "single" $
        parse pfix "" "fix plus (x:nat) (y:nat):nat:=match x in nat return nat with |O => y|S xx => plus xx (S y) end" `shouldParse`
          TmFix
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
                  (TmMatch
                    (TmVar "x")
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
        parse pletin "" "let f:Type:=Type in Set" `shouldParse`
          TmLetIn "f" (TmSort Type) (TmSort Type) (TmSort Set)
      it "single" $
        parse pletin "" "let f (x:Set):Type:=Type in Set" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" (TmSort Set) (TmSort Type)) 
            (TmLambda "x" (TmSort Set) (TmSort Type))
            (TmSort Set)
      it "multiple" $
        parse pletin "" "let f (x:Set) (y:Prop) (z:Type):Type:=Type in Set" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" (TmSort Set)
              (TmProd "y" (TmSort Prop)
                (TmProd "z" (TmSort Type)
                  (TmSort Type))))
            (TmLambda "x" (TmSort Set)
              (TmLambda "y" (TmSort Prop)
                (TmLambda "z" (TmSort Type)
                  (TmSort Type))))
            (TmSort Set)
    describe "arrow(tmprod)" $ do
      it "single" $
        parse parrow "" "Type -> Set" `shouldParse` TmProd "_" (TmSort Type) (TmSort Set)
      it "multiple" $
        parse parrow "" "Type -> Set -> Prop" `shouldParse` 
          TmProd "_" (TmSort Type)
            (TmProd "_" (TmSort Set)
              (TmSort Prop))
      describe "parens" $ do
        it "(A->B)->C" $
          parse parrow "" "(Set -> Prop) -> Type" `shouldParse`
            TmProd "_" (TmProd "_" (TmSort Set) (TmSort Prop)) (TmSort Type)
        it "A->(B->C)" $
          parse parrow "" "Type -> (Set -> Prop)" `shouldParse` 
            TmProd "_" (TmSort Type)
              (TmProd "_" (TmSort Set)
                (TmSort Prop))
        it "complex" $
          parse parrow "" "Type -> (((Set -> Prop)) -> ((Type -> (Set -> Prop)))) -> Set" `shouldParse`
            TmProd "_"
              (TmSort Type)
              (TmProd "_"
                (TmProd "_"
                  (TmProd "_"
                    (TmSort Set)
                    (TmSort Prop))
                  (TmProd "_"
                    (TmSort Type)
                    (TmProd "_"
                      (TmSort Set)
                      (TmSort Prop))))
                (TmSort Set))
      describe "app" $ do
        it "single" $
          parse papp "" "Type Set" `shouldParse` 
            TmAppl [TmSort Type, TmSort Set]
        it "multiple" $
          parse papp "" "Type Set Prop" `shouldParse` 
            TmAppl [TmSort Type, TmSort Set, TmSort Prop]
      describe "equation" $
        it "equation" $
          parse pequation "" "|a b c => Set" `shouldParse` 
            Equation ["a","b","c"] (TmSort Set)
      describe "match" $ do
        it "empty" $
          parse pmatch "" "match Set in x return x with end" `shouldParse` 
            TmMatch (TmSort Set) ["x"] (TmVar "x") []
        it "single" $
          parse pmatch "" "match Set in x return x with |a => Set end" `shouldParse` 
            TmMatch (TmSort Set) ["x"] (TmVar "x") [Equation ["a"] (TmSort Set)]
        it "multiple" $
          parse pmatch "" "match Set in x return x with |a => Set |b c=>Prop|c=>Type end" `shouldParse` 
            TmMatch (TmSort Set) ["x"] (TmVar "x") [
                Equation ["a"] (TmSort Set)
              , Equation ["b", "c"] (TmSort Prop)
              , Equation ["c"] (TmSort Type)
              ]
        it "long type" $
          parse pmatch "" "match Set in x y z return x y z with |a => Set end" `shouldParse` 
            TmMatch (TmSort Set) ["x", "y", "z"] (TmAppl [TmVar "x", TmVar "y", TmVar "z"]) [Equation ["a"] (TmSort Set)]
  describe "simple term" $ do
    describe "tmsort" $ do
      it "Prop" $
        parse pterm "" "Prop" `shouldParse` TmSort Prop
      it "Set" $
        parse pterm "" "Set" `shouldParse` TmSort Set
      it "Type" $
        parse pterm "" "Type" `shouldParse` TmSort Type
    describe "tmprod" $ do
      it "single" $
        parse pterm "" "forall (x:Prop), Set" `shouldParse` 
          TmProd "x" (TmSort Prop) (TmSort Set)
      it "multiple" $
        parse pterm "" "forall (x:Prop) (y:Set) (z:Type), Set" `shouldParse`
          TmProd "x" (TmSort Prop) 
          (TmProd "y" (TmSort Set)
          (TmProd "z" (TmSort Type) (TmSort Set)))
    describe "tmfun" $ do
      it "zero" $
        parse pterm "" "fun => Set" `shouldParse` TmSort Set
      it "single" $
        parse pterm "" "fun (x:Prop) => Set" `shouldParse` 
          TmLambda "x" (TmSort Prop) (TmSort Set)
      it "multiple" $
        parse pterm "" "fun (x:Prop) (y:Set) (z:Type) => Set" `shouldParse`
          TmLambda "x" (TmSort Prop) 
          (TmLambda "y" (TmSort Set)
          (TmLambda "z" (TmSort Type) (TmSort Set)))
    describe "tmletin" $ do
      it "zero" $
        parse pterm "" "let f:Type:=Type in Set" `shouldParse`
          TmLetIn "f" (TmSort Type) (TmSort Type) (TmSort Set)
      it "single" $
        parse pterm "" "let f (x:Set):Type:=Type in Set" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" (TmSort Set) (TmSort Type)) 
            (TmLambda "x" (TmSort Set) (TmSort Type))
            (TmSort Set)
      it "multiple" $
        parse pterm "" "let f (x:Set) (y:Prop) (z:Type):Type:=Type in Set" `shouldParse`
          TmLetIn "f" 
            (TmProd "x" (TmSort Set)
              (TmProd "y" (TmSort Prop)
                (TmProd "z" (TmSort Type)
                  (TmSort Type))))
            (TmLambda "x" (TmSort Set)
              (TmLambda "y" (TmSort Prop)
                (TmLambda "z" (TmSort Type)
                  (TmSort Type))))
            (TmSort Set)
    describe "arrow(tmprod)" $ do
      it "single" $
        parse pterm "" "Type -> Set" `shouldParse` TmProd "_" (TmSort Type) (TmSort Set)
      it "multiple" $
        parse pterm "" "Type -> Set -> Prop" `shouldParse` 
          TmProd "_" (TmSort Type)
            (TmProd "_" (TmSort Set)
              (TmSort Prop))
      describe "parens" $ do
        it "(A->B)->C" $
          parse pterm "" "(Set -> Prop) -> Type" `shouldParse`
            TmProd "_" (TmProd "_" (TmSort Set) (TmSort Prop)) (TmSort Type)
        it "A->(B->C)" $
          parse pterm "" "Type -> (Set -> Prop)" `shouldParse` 
            TmProd "_" (TmSort Type)
              (TmProd "_" (TmSort Set)
                (TmSort Prop))
        it "complex" $
          parse pterm "" "Type -> (((Set -> Prop)) -> ((Type -> (Set -> Prop)))) -> Set" `shouldParse`
            TmProd "_"
              (TmSort Type)
              (TmProd "_"
                (TmProd "_"
                  (TmProd "_"
                    (TmSort Set)
                    (TmSort Prop))
                  (TmProd "_"
                    (TmSort Type)
                    (TmProd "_"
                      (TmSort Set)
                      (TmSort Prop))))
                (TmSort Set))
      describe "app" $ do
        it "single" $
          parse pterm "" "Type Set" `shouldParse` 
            TmAppl [TmSort Type, TmSort Set]
        it "multiple" $
          parse pterm "" "Type Set Prop" `shouldParse` 
            TmAppl [TmSort Type, TmSort Set, TmSort Prop]
      describe "match" $ do
        it "empty" $
          parse pterm "" "match Set in x return x with end" `shouldParse` 
            TmMatch (TmSort Set) ["x"] (TmVar "x") []
        it "single" $
          parse pterm "" "match Set in x return x with |a => Set end" `shouldParse` 
            TmMatch (TmSort Set) ["x"] (TmVar "x") [Equation ["a"] (TmSort Set)]
        it "multiple" $
          parse pterm "" "match Set in x return x with |a => Set |b c=>Prop|c=>Type end" `shouldParse` 
            TmMatch (TmSort Set) ["x"] (TmVar "x") [
                Equation ["a"] (TmSort Set)
              , Equation ["b", "c"] (TmSort Prop)
              , Equation ["c"] (TmSort Type)
              ]
        it "long type" $
          parse pterm "" "match Set in x y z return x y z with |a => Set end" `shouldParse` 
            TmMatch (TmSort Set) ["x", "y", "z"] (TmAppl [TmVar "x", TmVar "y", TmVar "z"]) [Equation ["a"] (TmSort Set)]
  describe "complex term" $ do
    it "var" $
      parse pterm "" "a" `shouldParse` TmVar "a"
    it "1" $
      parse pterm "" "(forall (a:A), a Set) b Set -> Type d" `shouldParse`
        TmProd "_"
          (TmAppl
            [ TmProd "a" (TmVar "A") 
                (TmAppl [TmVar "a", TmSort Set])
            , TmVar "b"
            , TmSort Set])
          (TmAppl [TmSort Type, TmVar "d"])
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
      parse pterm "" ("fun (a:forall (b:Set) (c:d->e->forall (p:q),p->q), c b) (b:forall (c:d),e) =>"
        ++ "let a (b:c) : d := e in "
        ++ "match a Set in x return x with |b c => forall (c:d), e end")
        `shouldParse`
        TmLambda "a"
          (TmProd "b"
            (TmSort Set)
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
              (TmMatch
                (TmAppl
                  [ TmVar "a"
                  , TmSort Set ])
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
    it "inductive" $
      parse pinductive "" ("Inductive r1 (A:Set) (B:Type) : A -> A -> B -> B -> Prop :="
        ++ "| p : forall (x:A),forall (y:B),forall (z:B), r1 A B x x y z | q : forall (x:A),forall (y:A),forall (z:B),r1 A B x y z z.") `shouldParse`
        Ind "r1" 2
          (TmProd "A"
            (TmSort Set)
            (TmProd "B"
              (TmSort Type)
              (TmProd "_"
                (TmVar "A")
                (TmProd "_"
                  (TmVar "A")
                  (TmProd "_"
                    (TmVar "B")
                    (TmProd "_"
                      (TmVar "B")
                      (TmSort Prop)))))))
          [ ( "p",
              TmProd "A"
                (TmSort Set)
                (TmProd "B"
                  (TmSort Type)
                  (TmProd "x"
                    (TmVar "A")
                    (TmProd "y"
                      (TmVar "B")
                      (TmProd "z"
                        (TmVar "B")
                        (TmAppl
                          [ TmVar "r1"
                          , TmVar "A"
                          , TmVar "B"
                          , TmVar "x"
                          , TmVar "x"
                          , TmVar "y"
                          , TmVar "z" ]))))))
              
          , ( "q",
              TmProd "A"
                (TmSort Set)
                (TmProd "B"
                  (TmSort Type)
                  (TmProd "x"
                    (TmVar "A")
                    (TmProd "y"
                      (TmVar "A")
                      (TmProd "z"
                        (TmVar "B")
                        (TmAppl
                          [ TmVar "r1"
                          , TmVar "A"
                          , TmVar "B"
                          , TmVar "x"
                          , TmVar "y"
                          , TmVar "z"
                          , TmVar "z" ]))))))]
    describe "fixpoint" $
      it "single" $
        parse pfixdefinition "" "Fixpoint plus (x:nat) (y:nat):nat:=match x in t return t with |O => y|S xx => plus xx (S y) end." `shouldParse`
          Fix "plus"
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
                  (TmMatch
                    (TmVar "x")
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
                              , TmVar "y"]])]))))