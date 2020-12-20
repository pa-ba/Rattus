{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}

module Main (module Main) where

import Rattus
import Rattus.Stream as S
import Prelude

-- All of these examples should typecheck with the more relaxed typing
-- rules of Rattus that allows functions and delays under tick.

{-# ANN module Rattus #-}


recBox :: Str Int
recBox = 0 ::: unbox (box (delay recBox))


dblDelay :: O (O Int)
dblDelay = delay (delay 1)


lambdaUnderDelay :: O (Int -> Int)
lambdaUnderDelay = delay (\x -> x)

advUnderLambda :: O (O Int -> O Int)
advUnderLambda = delay (\x -> delay (adv x))

sneakyLambdaUnderDelay :: O (Int -> Int)
sneakyLambdaUnderDelay = delay (let f x = x in f)

zeros :: Box (Str Int)
zeros = box (0 ::: delay (unbox zeros))

oneTwo :: Str Int
oneTwo = 1 ::: delay (2 ::: delay oneTwo)

data FStr a = Cons ! a ! (O (a -> O (FStr a)))

recFun :: Int -> FStr Int 
recFun n = Cons n (delay (\ x -> delay (recFun x)))

nestedRec :: Str Int
nestedRec = run 10
  where run :: Int -> Str Int
        run 0 = 0 ::: delay (nestedRec)
        run n = n ::: delay (run (n-1))


{-# ANN main NotRattus #-}
main = putStrLn "This file should type check"
