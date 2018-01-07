module Data.IxArray

import Data.IxRel

%include C "Array.h"
%link C "Array.o"

%access private
%default covering

data Prim_Array = Prim_MkArray

-- This creates an uninitialized array because it allocates, which would ruin any pointers to Idris values passed in.
prim_makeArray : Int -> IO Prim_Array
prim_makeArray len = do
  MkRaw arr <- foreign FFI_C "idris_makeArray" (Int -> IO (Raw Prim_Array)) len
  pure arr

prim_indexArray : Int -> Prim_Array -> IO a
prim_indexArray {a} ix arr = do
  MkRaw elem <- foreign FFI_C "idris_indexArray" (Int -> Raw Prim_Array -> IO (Raw a)) ix (MkRaw arr)
  pure elem

prim_setAtArray : Int -> a -> Prim_Array -> IO ()
prim_setAtArray {a} ix elem arr =
  foreign FFI_C "idris_setAtArray" (Int -> Raw a -> Raw Prim_Array -> IO ()) ix (MkRaw elem) (MkRaw arr)

-- ###

%access export

namespace IxArray
  public export
  CanResize : Int -> Int -> Type
  CanResize = Predicate (<=)

  public export
  CanIndex : Int -> Int -> Type
  CanIndex = Predicate (\ix, len => ix >= 0 && ix < len)

  data IxArray : Int -> Type -> Type where
    MkIxArray : (len : Int) -> (prim_Array : Prim_Array) -> IxArray len a

  %used MkIxArray prim_Array

  length : IxArray len a -> Int
  length (MkIxArray len parr) = len

  fromList : List a -> IO (len ** IxArray len a)
  fromList xs = do
    let len = cast $ length xs
    parr <- prim_makeArray len
    for_ {b = ()} (zip [0 .. len - 1] xs) $ \(ix, elem) => prim_setAtArray ix elem parr
    pure $ (len ** MkIxArray len parr)

  index : (ix: Int) -> IxArray len a -> {auto canIndex: CanIndex ix len} -> IO a
  index ix (MkIxArray len parr) = prim_indexArray ix parr

  setAt : (ix: Int) -> a -> IxArray len a -> {auto canIndex: CanIndex ix len} -> IO ()
  setAt ix elem (MkIxArray len parr) = prim_setAtArray ix elem parr

  replicate : (len: Int) -> a -> IO (IxArray len a)
  replicate len fillElem = do
    parr <- prim_makeArray len
    for_ {b = ()} [0 .. len - 1] $ \ix => prim_setAtArray ix fillElem parr
    pure $ MkIxArray len parr

  imap : (a -> a) -> IxArray len a -> IO ()
  imap f (MkIxArray len parr) =
    for_ {b = ()} [0 .. len - 1] $ \ix => do
      elem <- prim_indexArray ix parr
      let newElem = f elem
      prim_setAtArray ix newElem parr

  itraverse : (a -> IO a) -> IxArray len a -> IO ()
  itraverse f (MkIxArray len parr) =
    for_ {b = ()} [0 .. len - 1] $ \ix => do
      elem <- prim_indexArray ix parr
      newElem <- f elem
      prim_setAtArray ix newElem parr

  resize : (newLen : Int) -> a -> IxArray len a -> {auto canResize : CanResize len newLen} -> IO (IxArray newLen a)
  resize newLen fillElem (MkIxArray len parr) = do
    newParr <- prim_makeArray newLen
    for_ {b = ()} [0 .. len - 1] $ \ix => do
      -- We have to set `a` here because idris is not inferring that newParr
      -- is an array of `a` like parr.
      elem <- prim_indexArray {a = a} ix parr
      prim_setAtArray ix elem newParr
    for_ {b = ()} [len .. newLen - 1] $ \ix => prim_setAtArray ix fillElem newParr
    pure $ MkIxArray newLen newParr

  clone : IxArray len a -> IO (IxArray len a)
  clone (MkIxArray len parr) = do
    newParr <- prim_makeArray len
    for_ {b = ()} [0 .. len - 1] $ \ix => do
      elem <- prim_indexArray {a = a} ix parr
      prim_setAtArray ix elem newParr
    pure $ MkIxArray len newParr
