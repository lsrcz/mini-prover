module MiniProver.Parser.LexerSpec (main, spec) where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.Parser.Lexer
import Text.Megaparsec

main :: IO ()
main = hspec spec

spec :: Spec
spec = 
  describe "Symbolic" $ do
    it "colon" $
      parse colon "" ":" `shouldParse` ":"
    it "coloneq" $
      parse coloneq "" ":=" `shouldParse` ":="
    it "arrow" $
      parse arrow "" "->" `shouldParse` "->"
    it "larrow" $
      parse larrow "" "<-" `shouldParse` "<-"
    it "darrow" $
      parse darrow "" "=>" `shouldParse` "=>"
    it "dot" $
      parse dot "" "." `shouldParse` "."
    it "underscore" $
      parse underscore "" "_" `shouldParse` "_"
    it "rws" $
      parse (rword "forall") "" "forall" `shouldParse` ()
    it "ident non-rws" $
      parse ident "" "abcd" `shouldParse` "abcd"
    it "ident rws" $
      parse ident "" `shouldFailOn` "Abort"
    it "ident underline" $
      parse ident "" "Abort_" `shouldParse` "Abort_"
      