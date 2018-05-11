module MiniProver.Core.TerminationSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Termination
import Data.List ( lookup )
import Data.Maybe ( fromJust )

main :: IO ()
main = hspec spec

spec :: Spec
spec = 
  describe "termination" $ 
    it "Dummy" $
      isTerminating DummyTm `shouldBe` True