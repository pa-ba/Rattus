
module Main (module Main) where

import Rattus
import Rattus.Stream
import Prelude hiding ((<*>), map, const)

-- Uncomment the annotation below to check that the definitions in
-- this module don't type check

-- {-# ANN module Rattus #-}


dblDelay :: Box (O (O Int))
dblDelay = box (delay (delay 1))

lambdaUnderDelay :: Box (O (O Int -> Int -> Int))
lambdaUnderDelay = box (delay (\x _ -> adv x))

sneakyLambdaUnderDelay :: Box (O (O Int -> Int -> Int))
sneakyLambdaUnderDelay = box (delay (let f x _ =  adv x in f))

leaky :: (() -> Bool) -> Str Bool
leaky p = p () ::: delay (leaky (\ _ -> hd (leaky (\ _ -> True))))

grec :: a
grec = grec

boxStream :: Str Int -> Box (Str Int)
boxStream s = box (0 ::: tl s)

mutualLoop :: a
mutualLoop = mutualLoop'

mutualLoop' :: a
mutualLoop' = mutualLoop

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
