-- | This module provides a variant of the standard
-- 'Control.Arrow.Arrow' type class with a different
-- 'Control.Arrow.arr' method so that it can be implemented for signal
-- functions in Rattus.

module Rattus.Arrow where

import Prelude hiding (id)
import Rattus.Primitives
import Control.Category

-- | Variant of the standard 'Control.Arrow.Arrow' type class with a
-- different 'Control.Arrow.arr' method so that it can be implemented
-- for signal functions in Rattus.
class Category a => Arrow a where
    {-# MINIMAL arrBox, (first | (***)) #-}

    -- | Lift a function to an arrow. It is here the definition of the
    -- 'Arrow' class differs from the standard one. The function to be
    -- lifted has to be boxed.
    -- 
    arrBox :: Box (b -> c) -> a b c

    -- | Send the first component of the input through the argument
    --   arrow, and copy the rest unchanged to the output.
    first :: a b c -> a (b,d) (c,d)
    first = (*** id)

    -- | A mirror image of 'first'.
    --
    --   The default definition may be overridden with a more efficient
    --   version if desired.
    second :: a b c -> a (d,b) (d,c)
    second = (id ***)

    -- | Split the input between the two argument arrows and combine
    --   their output.  Note that this is in general not a functor.
    (***) :: a b c -> a b' c' -> a (b,b') (c,c')
    f *** g = first f >>> arr swap >>> first g >>> arr swap
      where swap ~(x,y) = (y,x)

    -- | Fanout: send the input to both argument arrows and combine
    --   their output.
    --
    --   The default definition may be overridden with a more efficient
    --   version if desired.
    (&&&) :: a b c -> a b c' -> a b (c,c')
    f &&& g = arr (\b -> (b,b)) >>> f *** g


-- | This combinator is subject to the same restrictions as the 'box'
-- primitive of Rattus. That is,
--
-- >   Γ☐ ⊢ t :: b -> c
-- > --------------------
-- >  Γ ⊢ arr t :: a b c
--
-- where Γ☐ is obtained from Γ by removing ✓ and any variables @x ::
-- 𝜏@, where 𝜏 is not a stable type.

arr :: Arrow a => (b -> c) -> a b c
arr f = arrBox (box f)

-- | The identity arrow, which plays the role of 'return' in arrow notation.
returnA :: Arrow a => a b b
returnA = arrBox (box id)
