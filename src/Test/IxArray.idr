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

-- something : (Ord a, Num a) => (m : a) -> (n : a) -> {auto smaller : OrdLTE m n} -> a
-- something m n = m + n
--
-- checkSomething : Int
-- checkSomething = something 1 2
--
-- checkSomething2 : Ord a => (x : a) -> (y : a) -> Maybe (OrdLTE x y)
-- checkSomething2 x y with (relate (<=) x y)
--   | (True ** pf) = Just pf
--   | _ = Nothing
--
-- checkSomething3 : (x : Int) -> (y : Int) -> Maybe Int
-- checkSomething3 x y = do
--   pf <- decide (<=) True x y
--   pure (something x y {smaller = pf})
--
-- z : Maybe Int
-- z = checkSomething3 1 2
--
-- checkBounded : (Ord a, Num a) => (m : a) -> (n : a) -> (o : a) -> {auto bounded : OrdBounded m n o} -> a
-- checkBounded m n o = m + n + o
--
-- whatev : Ord a => (m : a) -> (n : a) -> OrdBounded m n m -> b
-- whatev _ _ = absurd
