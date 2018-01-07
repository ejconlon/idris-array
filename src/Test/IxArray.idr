module Test.IxArray

import Data.IxArray
import Data.IxRel

assertEq : Eq a => a -> a -> String -> IO ()
assertEq actual expected msg =
  if actual == expected
    then pure ()
    else do
      putStrLn ("Failed: " ++ msg)
      ?crash

testSimple : IO ()
testSimple = do
  arr <- replicate 1 "a"
  elem <- index 0 arr
  assertEq elem "a" "read what we write"

export
testAll : IO ()
testAll = do
  testSimple
  putStrLn "Succeeded"
