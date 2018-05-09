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
  describe "typeof" $
    it "TmRel" $
      typeof natListContext (TmRel "a" 0) `shouldBe` Right DummyTm
