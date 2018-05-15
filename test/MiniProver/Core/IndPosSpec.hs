module MiniProver.Core.IndPosSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Utils.ContextForTesting
import MiniProver.Core.IndPos

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "positivity" $
    it "dummy" $
      isPositive (Ind "dummy" 2 DummyTm DummyTm []) `shouldBe` True