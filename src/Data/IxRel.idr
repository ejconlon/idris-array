module Data.IxRel

%access public export
%default total

||| Indexed binary relations
data IxRel : (a -> b -> c) -> c -> a -> b -> Type where
  MkIxRel : IxRel p (p a b) a b

||| A binary boolean predicate
Predicate : (a -> b -> Bool) -> a -> b -> Type
Predicate p x y = IxRel p True x y

||| Given parameters, constructs the index and relation
relate : (p : a -> b -> c) -> (x : a) -> (y : b) -> (q ** IxRel p q x y)
relate p x y = (p x y ** MkIxRel)

||| Helper for decide
private
unique : IxRel p w x y -> IxRel p q x y -> w = q
unique MkIxRel MkIxRel = Refl

||| Given parameters and an index, decides if a relation exists for that index
decide : DecEq c => (p : a -> b -> c) -> (w : c) -> (x : a) -> (y : b) -> Dec (IxRel p w x y)
decide p w x y with (relate p x y)
  | (q ** pf) =
    case decEq w q of
      Yes pfe => Yes (rewrite pfe in pf)
      No contra => No (\r => contra (unique r pf))

||| Decide specialized to predicates
decidePredicate : (p : a -> b -> Bool) -> (x : a) -> (y : b) -> Dec (Predicate p x y)
decidePredicate p x y = decide p True x y
