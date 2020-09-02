{-# OPTIONS -fplugin=Rattus.Plugin #-}
{-# LANGUAGE TypeOperators #-}

-- | Programming with single shot events, i.e. events that may occur at
-- most once.

module Rattus.Event
  ( map
  , never
  , switch
  , switchTrans
  , whenJust
  , Event(..)
  , await
  , trigger
  , triggerMap
  )

where

import Rattus
import Rattus.Stream hiding (map)

import Prelude hiding (map)


-- | An event may either occur now or later.
data Event a = Now !a | Wait !(O (Event a))

-- all functions in this module are in Rattus 
{-# ANN module Rattus #-}

-- | Apply a function to the value of the event (if it ever occurs).
{-# NOINLINE [1] map #-}
map :: Box (a -> b) -> Event a -> Event b
map f (Now x) = Now (unbox f x)
map f (Wait x) = Wait (delay (map f) <#> x)

-- | An event that will never occur.
never :: Event a
never = Wait (delay never)


-- | @switch s e@ will behave like @s@ until the event @e@ occurs with
-- value @s'@, in which case it will behave as @s'@.
switch :: Str a -> Event (Str a) -> Str a
switch (x ::: xs) (Wait fas) = x ::: (delay switch <#> xs <#> fas)
switch _xs        (Now ys)   = ys 

-- | Turn a stream of 'Maybe''s into an event. The event will occur
-- whenever the stream has a value of the form @Just' v@, and the
-- event then has value @v@.
firstJust :: Str (Maybe' a) -> Event a
firstJust (Just' x ::: _) = Now x
firstJust (Nothing' ::: xs) = Wait (delay firstJust <#> xs)

-- | Turn a stream of 'Maybe''s into a stream of events. Each such
-- event behaves as if created by 'firstJust'.
whenJust :: Str (Maybe' a) -> Str (Event a)
whenJust cur@(_ ::: xs) = firstJust cur ::: (delay whenJust <#> xs)


-- | Like 'switch' but works on stream functions instead of
-- streams. That is, @switchTrans s e@ will behave like @s@ until the
-- event @e@ occurs with value @s'@, in which case it will behave as
-- @s'@.
switchTrans :: (Str a -> Str b) -> Event (Str a -> Str b) -> (Str a -> Str b)
switchTrans f es as = switchTrans' (f as) es as

-- | Helper function for 'switchTrans'.
switchTrans' :: Str b -> Event (Str a -> Str b) -> Str a -> Str b
switchTrans' (x ::: xs) (Wait fas) (_:::is) = x ::: (delay switchTrans' <#> xs <#> fas <#> is)
switchTrans' _xs        (Now ys)   is = ys is

-- | Helper function for 'await'.
await1 :: Stable a => a -> Event b -> Event (a :* b)
await1 a (Wait eb) = Wait (delay await1 <## a <#> eb)
await1 a (Now  b)  = Now  (a :* b)

-- | Helper function for 'await'.
await2 :: Stable b => b -> Event a -> Event (a :* b)
await2 b (Wait ea) = Wait (delay await2 <## b <#> ea)
await2 b (Now  a)  = Now  (a :* b)

-- | Synchronise two events. The resulting event occurs after both
-- events have occurred (coinciding with whichever event occurred
-- last.
await :: (Stable a, Stable b) => Event a -> Event b -> Event(a :* b)
await (Wait ea) (Wait eb)  = Wait (delay await <#> ea <#> eb)
await (Now a)   eb         = await1 a eb
await ea        (Now b)    = await2 b ea

-- | Trigger an event as soon as the given predicate turns true on the
-- given stream. The value of the event is the same as that of the
-- stream at that time.
trigger :: Box (a -> Bool) -> Str a -> Event a
trigger p (x ::: xs)
  | unbox p x  = Now x
  | otherwise  = Wait (delay (trigger p) <#> xs)


-- | Trigger an event as soon as the given function produces a 'Just''
-- value.
triggerMap :: Box (a -> Maybe' b) -> Str a -> Event b
triggerMap f (x ::: xs) =
  case unbox f x of
    Just' y  -> Now y
    Nothing' -> Wait (delay (triggerMap f) <#> xs)

{-# RULES

  "map/map" forall f g xs.
    map f (map g xs) = map (box (unbox f . unbox g)) xs ;

#-}
