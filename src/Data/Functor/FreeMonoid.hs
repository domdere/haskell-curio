---------------------------------------------------------------------------------
-- |
-- Module       : Data.Functor.FreeMonoid2
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- The Free functor that maps a type in (Proper) Hask to the subcategory of
-- Monoid, where the objects are monoids and the arrows are
-- monoid homomorphisms
--
-- The `FreeMonoid` functor is an examination of the `[]` monad, its internal
-- structure is different (and perhaps more redundant) but the idea was to make
-- the instance for `Monoid` as trivial as possible, in mapping `mempty` and
-- `mappend` directly to the Constructors, it emphasises the fact that the
-- datatype implements the Monoid algebra "by construction"
--
-- The `toList` function provides an homomorphism from `FreeMonoid a` to `[a]`
--
-- The `Eq` instance for `FreeMonoid a` makes it an isomorphism (sort of).
--
---------------------------------------------------------------------------------
module Data.Functor.FreeMonoid (
    -- * The Free Functor
        FreeMonoid(..)
    -- * The interpreter of Free Monoids
    ,   interpretFreeMonoid
    ) where

import Data.Functor.Forgetful

import Prelude ( Show(..), Eq(..), ($) )
import Control.Monad ( Monad(..) )
import Data.Function ( (.), on )
import Data.Functor ( Functor(..) )
import Data.Maybe ( Maybe(..) )
import Data.Monoid ( Monoid(..) )

-- |
-- The FreeMonoid functor takes any arbitrary type and extends it so that it
-- is inside `Monoid`, by adding the trivial element necessary to satisfy the
-- `mempty` part of the algebra.
--
-- The set is extended such that for every value [m :: FreeMonoid a]
-- [a `Mappend` m] is also of that type.
--
-- [Mappend :: a -> FreeMonoid a -> FreeMonoid a] does not
-- have the right type signature for `mappend` but its name was so
-- chosen because when you "fold" it into a Monoid, you basically
-- replace `Mappend` with `mappend`, refer to `interpretMonoid`
--
data FreeMonoid a =
        Mempty                                  -- ^ Add a value for `mempty`, equivalent to [[]]
    |   Singleton a                             -- ^ Embed the original type, equivalent to [[x]]
    |   Mappend (FreeMonoid a) (FreeMonoid a)   -- ^ Close the set of values under the `mappend` operation

-- instances

-- | Display the FreeMonoid as a string of elements of the original type
instance (Show a) => Show (FreeMonoid a) where
    show = show . toList

-- | Two [FreeMonoid a] values are the same if they can be generated
-- by appending the same string of elements of the base type.
--
instance (Eq a) => Eq (FreeMonoid a) where
    (==) = (==) `on` toList

-- |
-- This instance demonstrates how the structure of
-- `FreeMonoid` allows it to satisfy the Monoid algebra
-- quite trivially by construction.
instance Monoid (FreeMonoid a) where
    mempty = Mempty

    mappend = Mappend

instance Functor FreeMonoid where
    _ `fmap` Mempty             = Mempty
    f `fmap` (Singleton x)      = (Singleton . f) x
    f `fmap` (Mappend xs ys)    = (Mappend `on` fmap f) xs ys

-- functions

-- |
-- When the `FreeMonoid` functor acts on a type that is already in `Monoid`,
--
-- The trivial additions made by `FreeMonoid` can be translated or "interpreted"
-- back to the `Monoid` algebra of the original type.
--
--
interpretFreeMonoid :: (Monoid a) => FreeMonoid a -> a
interpretFreeMonoid Mempty          = mempty
interpretFreeMonoid (Singleton x)   = x
interpretFreeMonoid (Mappend xs ys) = (mappend `on` interpretFreeMonoid) xs ys

-- | the homomorphism that takes the FreeMonoid to the [] monad
-- The other Free Monoid
--
toList :: FreeMonoid a -> [a]
toList = interpretFreeMonoid . fmap return

