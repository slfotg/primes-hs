{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLists   #-}
module Primes
  ( primes
  ) where

import           Control.Monad               (forM_, when)
import           Control.Monad.ST            (runST)
import           Data.Bit                    (Bit (..), listBits)
import           Data.STRef                  (modifySTRef', newSTRef, readSTRef,
                                              writeSTRef)
import qualified Data.Vector                 as BVec
import qualified Data.Vector.Unboxed         as Vec
import qualified Data.Vector.Unboxed.Mutable as MVec
import           Prelude                     (Bool (..), Int, Num (..),
                                              Ord (..), Ordering (..), div,
                                              filter, floor, fromIntegral, map,
                                              mod, otherwise, sqrt, ($), (++),
                                              (.))

-- | Size of the wheel for sieving
wheel :: Int
wheel = 30

-- | The primes that divide `wheel`
smallPrimes :: [Int]
smallPrimes = [ 2, 3, 5 ]

-- | The numbers less than and relatively primes to `wheel`
relativePrimes :: Vec.Vector Int
relativePrimes =
  [ 1, 7, 11, 13, 17, 19, 23, 29 ]

-- | The size of `relativePrimes`
relativePrimesSize :: Int
relativePrimesSize = Vec.length relativePrimes

{- | Differences between `relativePrimes`

>>> map diffs [0..10]
[6,4,2,4,2,4,6,2,6,4,2]
-}
diffs :: Int -> Int
diffs i = diffs' Vec.! i
  where
    diffs' :: Vec.Vector Int
    diffs' = [ 6, 4, 2, 4, 2, 4, 6, 2, 6, 4, 2, 4, 2, 4, 6, 2 ]

-- | Multiplication table indexes for `relativePrimes`
multiplicationTable :: Int -> Int -> Int
multiplicationTable i j = (multiplicationTable' BVec.! i) Vec.! j
  where
    multiplicationTable' :: BVec.Vector (Vec.Vector Int)
    multiplicationTable' =
      [ [ 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7 ]
      , [ 1, 5, 4, 0, 7, 3, 2, 6, 1, 5, 4, 0, 7, 3, 2, 6 ]
      , [ 2, 4, 0, 6, 1, 7, 3, 5, 2, 4, 0, 6, 1, 7, 3, 5 ]
      , [ 3, 0, 6, 5, 2, 1, 7, 4, 3, 0, 6, 5, 2, 1, 7, 4 ]
      , [ 4, 7, 1, 2, 5, 6, 0, 3, 4, 7, 1, 2, 5, 6, 0, 3 ]
      , [ 5, 3, 7, 1, 6, 0, 4, 2, 5, 3, 7, 1, 6, 0, 4, 2 ]
      , [ 6, 2, 3, 7, 0, 4, 5, 1, 6, 2, 3, 7, 0, 4, 5, 1 ]
      , [ 7, 6, 5, 4, 3, 2, 1, 0, 7, 6, 5, 4, 3, 2, 1, 0 ]
      ]

{- | Used for converting bit vec index to the value it represents

>>> Prelude.map fromIndex [0..10]
[1,7,11,13,17,19,23,29,31,37,41]
-}
fromIndex :: Int -> Int
fromIndex n =
  let d = n `div` relativePrimesSize
      m = n `mod` relativePrimesSize
    in wheel * d + relativePrimes Vec.! m

{- | Find the index for inserting a new value into a sorted Vector

>>> Prelude.map (binarySearch relativePrimes) [0..30]
[0,1,1,1,1,1,1,2,2,2,2,3,3,4,4,4,4,5,5,6,6,6,6,7,7,7,7,7,7,8,8]
-}
binarySearch :: (Ord a, Vec.Unbox a) => Vec.Vector a -> a -> Int
binarySearch v x = binarySearch' 0 (Vec.length v - 1)
  where
    binarySearch' :: Int -> Int -> Int
    binarySearch' low high =
      if low > high
        then high + 1
        else
          let mid = (low + high) `div` 2
            in case compare x (v Vec.! mid) of
              LT -> binarySearch' low (mid - 1)
              EQ -> mid + 1
              GT -> binarySearch' (mid + 1) high

{- | Calculate the number of bits needed to store primes up to n

>>> Prelude.map bitsNeeded [0..60]
[0,1,1,1,1,1,1,2,2,2,2,3,3,4,4,4,4,5,5,6,6,6,6,7,7,7,7,7,7,8,8,9,9,9,9,9,9,10,10,10,10,11,11,12,12,12,12,13,13,14,14,14,14,15,15,15,15,15,15,16,16]
-}
bitsNeeded :: Int -> Int
bitsNeeded n =
  let s = (n `div` wheel) * relativePrimesSize
      m = n `mod` wheel
    in
      s + binarySearch relativePrimes m

toIndex :: Int -> Int
toIndex n = bitsNeeded n - 1

{- | Get all primes less than or equal to n

>>> primes 100
[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
-}
primes :: Int -> [Int]
primes n
  | n < 7 = filter (<= n) smallPrimes
  | otherwise = smallPrimes ++ map fromIndex (listBits $ sieve n)

sieve :: Int -> Vec.Vector Bit
sieve n =
  runST $ do
    isPrimes <- MVec.replicate vecSize (Bit True)
    -- Remove 1 from list of primes
    MVec.write isPrimes 0 $ Bit False

    -- loop through primes up to sqrt n and perform sieve
    forM_ ([1 .. nRoot] :: [Int]) $ \i -> do
      Bit isPrime <- MVec.read isPrimes i
      when isPrime $
        let prime = fromIndex i
            delta = prime * relativePrimesSize
            iMod = i `mod` relativePrimesSize
          in do
            composite <- newSTRef (prime * prime)
            forM_ ([iMod .. iMod + relativePrimesSize - 1] :: [Int]) $ \j -> do
              compositeValue <- readSTRef composite
              let compositeIndex = calculateIndex compositeValue iMod j
                in
                  forM_ ([compositeIndex, compositeIndex + delta .. lastIndex] :: [Int]) $ \k ->
                    MVec.write isPrimes k $ Bit False
              modifySTRef' composite (+ prime * diffs j)

    Vec.freeze isPrimes
    where
      vecSize = bitsNeeded n
      lastIndex = vecSize - 1
      nRoot = toIndex . floor . sqrt $ fromIntegral n
      calculateIndex :: Int -> Int -> Int -> Int
      calculateIndex n i j = (n `div` wheel) * relativePrimesSize + multiplicationTable i j
