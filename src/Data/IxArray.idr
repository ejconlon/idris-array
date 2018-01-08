module Data.IxArray

import Data.IOArray
import Data.IxRel

%access export

private
newArrayUninitialized : Int -> IO (IOArray elem)
newArrayUninitialized len = newArray {elem=elem} len (really_believe_me prim__null)

public export
CanResize : Int -> Int -> Type
CanResize = Predicate (<=)

public export
CanIndex : Int -> Int -> Type
CanIndex = Predicate (\ix, len => ix >= 0 && ix < len)

data IxArray : Int -> Type -> Type where
  MkIxArray : (len : Int) -> (parr : IOArray a) -> IxArray len a

length : IxArray len a -> Int
length (MkIxArray len parr) = len

fromList : List a -> IO (len ** IxArray len a)
fromList xs = do
  let len = cast $ length xs
  parr <- newArrayUninitialized len
  for_ {b = ()} (zip [0 .. len - 1] xs) $ \(ix, elem) => unsafeWriteArray parr ix elem
  pure $ (len ** MkIxArray len parr)

index : (ix: Int) -> IxArray len a -> {auto canIndex: CanIndex ix len} -> IO a
index ix (MkIxArray len parr) = unsafeReadArray parr ix

setAt : (ix: Int) -> a -> IxArray len a -> {auto canIndex: CanIndex ix len} -> IO ()
setAt ix elem (MkIxArray len parr) = unsafeWriteArray parr ix elem

replicate : (len: Int) -> a -> IO (IxArray len a)
replicate len fillElem = do
  parr <- newArray len fillElem
  pure $ MkIxArray len parr

imap : (a -> a) -> IxArray len a -> IO ()
imap f (MkIxArray len parr) =
  for_ {b = ()} [0 .. len - 1] $ \ix => do
    elem <- unsafeReadArray parr ix
    let newElem = f elem
    unsafeWriteArray parr ix newElem

itraverse : (a -> IO a) -> IxArray len a -> IO ()
itraverse f (MkIxArray len parr) =
  for_ {b = ()} [0 .. len - 1] $ \ix => do
    elem <- unsafeReadArray parr ix
    newElem <- f elem
    unsafeWriteArray parr ix newElem

resize : (newLen : Int) -> a -> IxArray len a -> {auto canResize : CanResize len newLen} -> IO (IxArray newLen a)
resize newLen fillElem (MkIxArray len parr) = do
  newParr <- newArray newLen fillElem
  for_ {b = ()} [0 .. len - 1] $ \ix => do
    elem <- unsafeReadArray parr ix
    unsafeWriteArray newParr ix elem
  pure $ MkIxArray newLen newParr

clone : IxArray len a -> IO (IxArray len a)
clone (MkIxArray len parr) = do
  newParr <- newArrayUninitialized len
  for_ {b = ()} [0 .. len - 1] $ \ix => do
    elem <- unsafeReadArray parr ix
    unsafeWriteArray newParr ix elem
  pure $ MkIxArray len newParr
