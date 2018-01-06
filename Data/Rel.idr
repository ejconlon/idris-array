module Data.Rel

%access export

||| Indexed binary relations
data Rel : (a -> b -> c) -> c -> a -> b -> Type where
  MkRel : Rel p (p a b) a b

||| Proves a binary relation.
relate : (p : a -> b -> c) -> (x : a) -> (y : b) -> (q ** Rel p q x y)
relate p x y = (p x y ** MkRel)

||| Tests a binary relation.
unrelate : DecEq c => (p : a -> b -> c) -> (w: c) -> (x : a) -> (y : b) -> Maybe (Rel p w x y)
unrelate p w x y with (relate p x y)
  | (q ** pf) =
    case decEq w q of
      Yes pfe => Just (rewrite pfe in pf)
      _ => Nothing

||| Indexed ternary relations.
data Rel3 : (a -> b -> c -> d) -> d -> a -> b -> c -> Type where
  MkRel3 : Rel3 p (p a b c) a b c

||| Proves a ternary relation.
relate3 : (p : a -> b -> c -> d) -> (x : a) -> (y : b) -> (z : c) -> (q ** Rel3 p q x y z)
relate3 p x y z = (p x y z ** MkRel3)

||| Tests a binary relation.
unrelate3 : DecEq d => (p : a -> b -> c -> d) -> (w: d) -> (x : a) -> (y : b) -> (z: c) -> Maybe (Rel3 p w x y z)
unrelate3 p w x y z with (relate3 p x y z)
  | (q ** pf) =
    case decEq w q of
      Yes pfe => Just (rewrite pfe in pf)
      _ => Nothing

OrdLTE : Ord a => a -> a -> Type
OrdLTE = Rel (<=) True

bounded : Ord a => a -> a -> a -> Bool
bounded x y z = x <= y && y < z

OrdBounded : Ord a => a -> a -> a -> Type
OrdBounded = Rel3 bounded True

something : (Ord a, Num a) => (m : a) -> (n : a) -> {auto smaller : OrdLTE m n} -> a
something m n = m + n

checkSomething : Int
checkSomething = something 1 2

checkSomething2 : Ord a => (x : a) -> (y : a) -> Maybe (OrdLTE x y)
checkSomething2 x y with (relate (<=) x y)
  | (True ** pf) = Just pf
  | _ = Nothing

checkSomething3 : (x : Int) -> (y : Int) -> Maybe Int
checkSomething3 x y = do
  pf <- unrelate (<=) True x y
  pure (something x y {smaller = pf})

z : Maybe Int
z = checkSomething3 1 2

checkBounded : (Ord a, Num a) => (m : a) -> (n : a) -> (o : a) -> {auto bounded : OrdBounded m n o} -> a
checkBounded m n o = m + n + o
