module MiniProver.Core.TypingSpec (main, spec) where

import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = 
  describe "dummy" $
    it "dummy" $
      typeof [] DummyTm `shouldBe` DummyTm
