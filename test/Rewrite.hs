module Main (module Main) where

import Rattus
import Rattus.Stream
import Prelude hiding ((<*>), map,zip,const)

{-# ANN module Rattus #-}

twice :: Str Int -> Str Int
twice = map (box (+1)) . map (box (+1))

scanAndMap :: Str Int -> Str Int
scanAndMap xs = map (box (+1)) (scan (box (+)) 0 xs)

sums :: Str Int -> Str Int
sums xs = scan (box (+)) 0 xs

twiceScan :: Str Int -> Str Int
twiceScan xs = scan (box (+)) 0  (scan (box (+)) 0 xs)

twiceScanMap :: Str Int -> Str Int
twiceScanMap xs = scan (box (+)) 0  (scanMap (box (+)) (box (+1)) 0 xs)

zipMap :: Str Int -> Str Int -> Str Int
zipMap xs ys = map (box (\ (x:*y) -> x + y)) (zip xs ys)

constMap :: Str Int
constMap = map (box (+1)) (const 5)

{-# ANN main NotRattus #-}
main = putStrLn "This is just to test the rewrite rules"
