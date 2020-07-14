-- | The language primitives of Rattus. Note that the Rattus types
--  'delay', 'adv', and 'box' are more restrictive that the Haskell
--  types that are indicated. The more stricter Rattus typing rules
--  for these primitives are given. To ensure that your program
--  adheres to these stricter typing rules, use the plugin in
--  "Rattus.Plugin" so that GHC will check these stricter typing
--  rules.

module Rattus.Primitives
  (O
  ,Box
  ,delay
  ,adv
  ,box
  ,unbox
  ,Stable
  ) where


-- | To prevent the user from declaring instances of Stable, we do not
-- export the 'StableInternal' class it depends on.

class StableInternal a where

-- | A type is @Stable@ if it is a strict type and the later modality
-- @O@ and function types only occur under @Box@.
--
-- For example, these types are stable: @Int@, @Box (a -> b)@, @Box (O
-- Int)@, @Box (Str a -> Str b)@.
--
-- But these types are not stable: @[Int]@ (because the list type is
-- not strict), @Int -> Int@, (function type is not stable), @O
-- Int@, @Str Int@.

class StableInternal a => Stable a  where

-- | The "later" type modality. A value of type @O a@ is a computation
-- that produces a value of type @a@ in the next time step. Use
-- 'delay' and 'adv' to construct and consume 'O'-types.
data O a = Delay a

-- | The "stable" type modality. A value of type @Box a@ is a
-- time-independent computation that produces a value of type @a@.
-- Use 'box' and 'unbox' to construct and consume 'Box'-types.
data Box a = Box a

-- | This is the constructor for the "later" modality 'O':
--
-- >     Γ ✓ ⊢ t :: 𝜏
-- > --------------------
-- >  Γ ⊢ delay t :: O 𝜏
--
delay :: a -> O a
delay x = Delay x


-- | This is the eliminator for the "later" modality 'O':
--
-- >     Γ ⊢ t :: O 𝜏
-- > ---------------------
-- >  Γ ✓ Γ' ⊢ adv t :: 𝜏
--
adv :: O a -> a
adv (Delay x) = x


-- | This is the constructor for the "stable" modality 'Box':
--
-- >     Γ☐ ⊢ t :: 𝜏
-- > --------------------
-- >  Γ ⊢ box t :: Box 𝜏
--
-- where Γ☐ is obtained from Γ by removing ✓ and any variables @x ::
-- 𝜏@, where 𝜏 is not a stable type.


box :: a -> Box a
box x = Box x



-- | This is the eliminator for the "stable" modality  'Box':
--
-- >   Γ ⊢ t :: Box 𝜏
-- > ------------------
-- >  Γ ⊢ unbox t :: 𝜏

unbox :: Box a -> a
unbox (Box d) = d
