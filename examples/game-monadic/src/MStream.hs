{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS -fplugin=Rattus.Plugin #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ApplicativeDo #-}

-- | Programming with monadic streams.

module MStream where

import Rattus
import Rattus.Stream hiding (const,map,integral,unfold, zip)
import Control.Eff.Reader.Strict
import Control.Eff
import GHC.Types
import Prelude hiding (map, const, zipWith, zip, filter)

import Data.VectorSpace

-- | @MStr a@ is a stream of values of type @a@.
data MStr m a = MStr !(m (a :* (O (MStr m a))))

type EStr r = MStr (Eff r)

cons :: Applicative m => a -> O (MStr m a) -> MStr m a
cons x xs = MStr (pure (x:*xs))

-- | Get the first element (= head) of a stream.
hd :: Functor m => MStr m a -> m a
hd (MStr xs) = fst' <$> xs


-- | Get the tail of a stream, i.e. the remainder after removing the
-- first element.
tl :: Functor m => MStr m a -> m (O (MStr m a))
tl (MStr xs) = snd' <$> xs


-- | Apply a function to each element of a stream.
mapPure :: Monad m => Box (a -> b) -> MStr m a -> MStr m b
mapPure f (MStr xs) = MStr $ do
  (x :* xs') <- xs
  return (unbox f x :* delay (mapPure f (adv xs')))

-- | Apply a function to each element of a stream.
map :: Monad m => Box (a -> m b) -> MStr m a -> MStr m b
map f (MStr xs) = MStr $ do
  (x :* xs') <- xs
  x' <- unbox f x
  return (x' :* delay (map f (adv xs')))

type family (<) l t :: Constraint where
  '[] < _ = ()
  (t ': ts) < r = (Member (Reader t) r, ts < r)


unfold :: (Stable b,Functor m) => Box(b -> m b) -> b -> MStr m b
unfold f acc = MStr $ do
  acc' <- unbox f acc
  return (acc' :* delay (unfold f acc'))


-- | Construct a stream that has the same given value at each step.
const :: (Applicative m, Stable a) => a -> MStr m a
const a = a `cons` delay (const a)



-- | Construct a stream that has the same given value at each step.
constBox :: (Applicative m, Stable a) => Box (m a) -> MStr m a
constBox ma = run where
  run = MStr $ do
    a <- unbox ma
    return (a :* delay run)


-- | Similar to 'Prelude.zip' on Haskell lists.
zip :: Monad m => MStr m a -> MStr m b -> MStr m (a:*b)
zip (MStr mas) (MStr mbs) = MStr $ do
  (a :* as) <- mas
  (b :* bs) <- mbs
  return ((a :* b) :* delay (zip (adv as) (adv bs)))


runReaderStr :: EStr (Reader a ': r) b -> EStr r a -> EStr r (a :* b)
runReaderStr (MStr bs') (MStr as') = MStr $ do
  (a :* as) <- as'
  (b :* bs) <-runReader a bs'
  return ((a :* b) :* delay (runReaderStr (adv bs) (adv as)))

runReaderStr' :: EStr (Reader a ': r) b -> Str a -> EStr r b
runReaderStr' (MStr bs') (a ::: as) = MStr $ do
  (b :* bs) <-runReader a bs'
  return (b :* delay (runReaderStr' (adv bs) (adv as)))



runEffStr :: EStr '[] a -> Str a
runEffStr (MStr as') =
  let (a :* as) = run as'
  in a ::: delay (runEffStr (adv as))

type DTime = Double

-- | Calculates an approximation of an integral of the stream of type
-- @Str a@ (the y-axis), where the stream of type @Str s@ provides the
-- distance between measurements (i.e. the distance along the y axis).
integral :: (Stable a, VectorSpace a DTime, '[DTime] < r) => a -> EStr r a -> EStr r a
integral acc (MStr as') = MStr $ do
  (a :* as) <- as'
  t <- ask
  let acc' = acc ^+^ (t *^ a)
  return (acc' :* delay (integral acc' (adv as)))



-- | @switch s e@ will behave like @s@ but switches to @s'$ every time
-- the event 'e' occurs with some value @s'@.
switch :: Box (Eff r (Maybe' (EStr r a))) -> EStr r a -> EStr r a
switch f as = MStr $ do
  mb' <- unbox f
  let (MStr ma) = case mb' of
                    Nothing' -> as
                    Just' mb -> mb
  (a :* as) <- ma
  return (a :* delay (switch f (adv as)))
