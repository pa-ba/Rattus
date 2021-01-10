{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}

module Main (module Main) where

import Rattus
import Rattus.Stream as S
import Rattus.Yampa
import Prelude

-- Uncomment the annotation below to check that the definitions in
-- this module don't type check

-- {-# ANN module Rattus #-}



loopIndirect :: Str Int
loopIndirect = run
  where run :: Str Int
        run = loopIndirect

        
loopIndirect' :: Str Int
loopIndirect' = let run = loopIndirect' in run


nestedUnguard :: Str Int
nestedUnguard = run 0
  where run :: Int -> Str Int
        run 0 = nestedUnguard
        run n = n ::: delay (run (n-1))

sfLeak :: O Int -> SF () (O Int)
sfLeak  x = proc _ -> do
  returnA -< x
  
advDelay :: O (O a) -> O a
advDelay y = delay (let x = adv y in adv x)

advDelay' :: O a -> a
advDelay' y = let x = adv y in x

dblAdv :: O (O a) -> O a
dblAdv y = delay (adv (adv y))

advScope :: O (O Int -> Int)
advScope = delay (\x -> adv x)

advScope' :: O (Int -> Int)
advScope' = delay (let f x =  adv (delay x) in f)

grec :: a
grec = grec

boxStream :: Str Int -> Box (Str Int)
boxStream s = box (0 ::: tl s)

boxStream' :: Str Int -> Box (Str Int)
boxStream' s = box s


intDelay :: Int -> O Int
intDelay = delay

intAdv :: O Int -> Int
intAdv = adv


newDelay :: a -> O a
newDelay x = delay x


mutualLoop :: a
mutualLoop = mutualLoop'

mutualLoop' :: a
mutualLoop' = mutualLoop

constUnstable :: a -> Str a
constUnstable a = run
  where run = a ::: delay run

mapUnboxed :: (a -> b) -> Str a -> Str b
mapUnboxed f = run
  where run (x ::: xs) = f x ::: delay (run (adv xs))
  
mapUnboxedMutual :: (a -> b) -> Str a -> Str b
mapUnboxedMutual f = run
  where run (x ::: xs) = f x ::: delay (run' (adv xs))
        run' (x ::: xs) = f x ::: delay (run (adv xs))


-- mutual recursive pattern definitions
foo1,foo2 :: Box (a -> b) -> Str a -> Str b
(foo1,foo2) = (\ f (x ::: xs) -> unbox f x ::: (delay (foo2 f) <#> xs),
               \ f (x ::: xs) -> unbox f x ::: (delay (foo1 f) <#> xs))

nestedPattern :: Box (a -> b) -> Str a -> Str b
nestedPattern = foo1 where
  foo1,foo2 :: Box (a -> b) -> Str a -> Str b
  (foo1,foo2) = (\ f (x ::: xs) -> unbox f x ::: (delay (foo2 f) <#> xs),
                 \ f (x ::: xs) -> unbox f x ::: (delay (foo1 f) <#> xs))


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
