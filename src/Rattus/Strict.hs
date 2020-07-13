{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module contains strict versions of some standard data
-- structures.



module Rattus.Strict
  ( List(..),
    reverse',
    (:*)(..),
    Maybe'(..),
   fst',
   snd',
  )where

import Data.VectorSpace

infixr 2 :*

-- | Strict list type.
data List a = Nil | !a :! !(List a)

-- | Reverse a list.
reverse' :: List a -> List a
reverse' l =  rev l Nil
  where
    rev Nil     a = a
    rev (x:!xs) a = rev xs (x:!a)

instance Foldable List where
  
  foldMap f = run where
    run Nil = mempty
    run (x :! xs) = f x <> run xs
  foldr f = run where
    run b Nil = b
    run b (a :! as) = (run $! (f a b)) as
  foldl f = run where
    run a Nil = a
    run a (b :! bs) = (run $! (f a b)) bs
  elem a = run where
    run Nil = False
    run (x :! xs)
      | a == x = True
      | otherwise = run xs
    
  
instance Functor List where
  fmap f = run where
    run Nil = Nil
    run (x :! xs) = f x :! run xs


-- | Strict variant of 'Maybe'.
data Maybe' a = Just' ! a | Nothing'

-- | Strict pair type.
data a :* b = !a :* !b

-- | First projection function.
fst' :: (a :* b) -> a
fst' (a:*_) = a

-- | Second projection function.
snd' :: (a :* b) -> b
snd' (_:*b) = b


instance RealFloat a => VectorSpace (a :* a) a where
    zeroVector = 0 :* 0

    a *^ (x :* y) = (a * x) :* (a * y)

    (x :* y) ^/ a = (x / a) :* (y / a)

    negateVector (x :* y) = (-x) :* (-y)

    (x1 :* y1) ^+^ (x2 :* y2) = (x1 + x2) :* (y1 + y2)

    (x1 :* y1) ^-^ (x2 :* y2) = (x1 - x2) :* (y1 - y2)

    (x1 :* y1) `dot` (x2 :* y2) = x1 * x2 + y1 * y2

instance Functor ((:*) a) where
  fmap f (x:*y) = (x :* f y)
  
instance (Show a, Show b) => Show (a:*b) where
  show (a :* b) = "(" ++ show a ++ " :* " ++ show b ++ ")"
