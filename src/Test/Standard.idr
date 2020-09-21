module Test.Standard

import System
import Test.Unit.Generic

%default total
%access export

checkCI : IO Bool
checkCI = do
  ci <- getEnv "CI"
  pure $ case ci of
              Just v => toLower v == "true"
              Nothing => False

assertWithTitle : Show a => Eq a =>
  (title : String) -> (given : a) -> (expected : a) -> IO Bool
assertWithTitle title given expected =
  genericTest (Just title) given expected (==)
