{-# LANGUAGE DeriveDataTypeable #-}
module Rattus.Plugin.Annotation (Rattus(..)) where

import Data.Data

-- | Use this type to mark a Haskell function definition as a Rattus
-- function:
--
-- > {-# ANN myFunction Rattus #-}
-- 
-- Or mark a whole module as consisting of Rattus functions only:
--
-- > {-# ANN module Rattus #-}
--
-- If you use the latter option, you can mark exceptions
-- (i.e. functions that should be treated as ordinary Haskell function
-- definitions) as follows:
--
-- > {-# ANN myFunction NotRattus #-}

data Rattus = Rattus | NotRattus deriving (Typeable, Data, Show, Eq)
