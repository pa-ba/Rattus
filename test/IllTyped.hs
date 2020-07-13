
module Main (module Main) where

import Rattus
import Rattus.Stream
import Prelude hiding ((<*>), map, const)

-- Uncomment the annotation below to check that the definitions in
-- this module don't type check

-- {-# ANN module Rattus #-}

bar1 :: Box (a -> b) -> Str a -> Str b
bar1 f (x ::: xs) = unbox f x ::: (delay (bar2 f) <*> xs)

bar2 :: Box (a -> b) -> Str a -> Str b
bar2 f  (x ::: xs) = unbox f x ::: (delay (bar1 f) <*> xs)


dblDelay :: Box (O (O Int))
dblDelay = box (delay (delay 1))

lambdaUnderDelay :: Box (O (O Int -> Int -> Int))
lambdaUnderDelay = box (delay (\x _ -> adv x))

leaky :: (() -> Bool) -> Str Bool
leaky p = p () ::: delay (leaky (\ _ -> hd (leaky (\ _ -> True))))

grec :: Int
grec = grec

zeros :: Box (Str Int)
zeros = box (0 ::: delay (unbox zeros))

constUnstable :: a -> Str a
constUnstable a = run
  where run = a ::: delay run

mapUnboxed :: (a -> b) -> Str a -> Str b
mapUnboxed f = run
  where run (x ::: xs) = f x ::: delay (run (adv xs))


data Input = Input {jump :: !Bool, move :: Move}
data Move = StartLeft | EndLeft | StartRight | EndRight | NoMove

-- Input is not a stable type (it is not strict). Therefore this
-- should not type check.
constS :: Input -> Str Input
constS a = a ::: delay (constS a)


-- Since Input is not strict, we cannot instantiate the 'const'
-- function.
-- Uncomment the definition below to check this.

-- constS' :: Input -> Str Input
-- constS' = const


{-# ANN main NotRattus #-}
main = putStrLn "This file should not type check"
