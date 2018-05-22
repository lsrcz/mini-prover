module MiniProver.TopLevel.CommandSpec (main,spec) where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.TopLevel.Command

main :: IO ()
main = hspec spec

spec :: Spec
spec = it "simple" $ 1 + 1 `shouldBe` 2