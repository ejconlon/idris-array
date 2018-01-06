module Data.Array

import Data.Rel

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

prim_fillArray : Int -> a -> Prim_Array -> IO ()
prim_fillArray {a} len elem arr =
  foreign FFI_C "idris_fillArray" (Int -> Raw a -> Raw Prim_Array -> IO ()) len (MkRaw elem) (MkRaw arr)

-- ###

%access export

namespace IOArray
  CanIndex : Int -> Int -> Type
  CanIndex = OrdBounded 0

  data IOArray : Int -> Type -> Type where
    MkIOArray : (len : Int) -> (prim_Array : Prim_Array) -> IOArray len a

  %used MkIOArray prim_Array

  length : IOArray len a -> Int
  length (MkIOArray len parr) = len

  fromList : List a -> IO (len ** IOArray len a)
  fromList xs = do
    let len = cast $ length xs
    parr <- prim_makeArray len
    for_ {b = ()} (zip [0 .. len - 1] xs) $ \(ix, elem) => prim_setAtArray ix elem parr
    pure $ (len ** MkIOArray len parr)

  index : (ix: Int) -> IOArray len a -> {auto canIndex: CanIndex ix len} -> IO a
  index ix (MkIOArray len parr) = prim_indexArray ix parr

  setAt : (ix: Int) -> a -> IOArray len a -> {auto canIndex: CanIndex ix len} -> IO ()
  setAt ix elem (MkIOArray len parr) = prim_setAtArray ix elem parr

  replicate : (len : Int) -> a -> IO (IOArray len a)
  replicate len elem = do
    parr <- prim_makeArray len
    prim_fillArray len elem parr
    pure (MkIOArray len parr)

  imap : (a -> a) -> IOArray len a -> IO ()
  imap f (MkIOArray len parr) =
    for_ {b = ()} [0 .. len - 1] $ \ix => do
      a <- prim_indexArray ix parr
      prim_setAtArray ix (f a) parr
