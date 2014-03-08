---------------------------------------------------------------------------------
-- |
-- Module       : Control.Monad.List
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- Constructing the List monad from the adjunction between the `FreeMonoid` and
-- `U` functors.
--
---------------------------------------------------------------------------------
module Control.Monad.List (
    -- * The List Monad
        List(..)
    -- * The Hom-set Isomorphism that defines the FreeMonoid and U adjunction
    ,   monoidphi
    ,   monoidunphi
    -- * Units and counits
    ,   monoidunit'
    ,   monoidunit
    ,   monoidcounit'
    ,   monoidjoin'
    ,   monoidjoin
    ) where

import Data.Functor.Forgetful
import Data.Functor.FreeMonoid

import Prelude (Show, Eq, ($) )
import Control.Monad ( Monad(..) )
import Data.Function ( (.), id )
import Data.Functor ( Functor(..) )
import Data.Monoid ( Monoid(..) )

newtype List a = List { unList :: U (FreeMonoid a) } deriving (Show, Eq)

-- instances

instance Functor List where
    fmap f = List . fmap (fmap f) . unList

instance Monad List where
    return = monoidunit

    ma >>= f = monoidjoin $ fmap f ma

-- |
-- The monad adjunction between `FreeMonoid` and `U` means there
-- is a `phi` and `unphi` exist.
-- and for [k, f :: (Monoid a, Monoid b) => a -> b] a monoid
-- homomorphism as described in `Data.Monoid` and
-- [h, g :: a' -> b'] a plain set homomorphism
--
-- @ monoidphi (k . f) = fmap k . monoidphi f @
-- @ monoidphi (f . fmap h) = monoidphi f . h @
--
-- and
--
-- @ monoidunphi (g . h) = monoidunphi g . fmap h @
-- @ monoidunphi (fmap h . g) = h . monoidunphi g @
--
monoidphi :: (Monoid p) => (FreeMonoid a -> p) -> a -> U p
monoidphi f = U . f . (`Mappend` Mempty)

monoidunphi :: (Monoid p) => (a -> U p) -> FreeMonoid a -> p
monoidunphi f = interpretFreeMonoid . fmap (unforget . f)

monoidunit' :: a -> U (FreeMonoid a)
monoidunit' = monoidphi id

monoidcounit' :: (Monoid p) => FreeMonoid (U p) -> p
monoidcounit' = monoidunphi id

monoidunit :: a -> List a
monoidunit = List . monoidunit'

monoidjoin' :: U (FreeMonoid (U (FreeMonoid a))) -> U (FreeMonoid a)
monoidjoin' = fmap monoidcounit'

monoidjoin :: List (List a) -> List a
monoidjoin = List . monoidjoin' . unList . fmap unList
