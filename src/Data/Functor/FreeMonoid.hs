---------------------------------------------------------------------------------
-- |
-- Module       : Data.Functor.FreeMonoid
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- The Free functor that maps a type in (Proper) Hask to the subcategory of
-- Monoid, where the objects are monoids and the arrows are
-- monoid homomorphisms
--
-- The `FreeMonoid` functor is an examination of the `[]` monad
--
---------------------------------------------------------------------------------
module Data.Functor.FreeMonoid (
    -- * The Free Functor
        FreeMonoid(..)
    -- * The interpreter of Free Monoids
    ,   interpretFreeMonoid
    ) where

import Data.Functor.Forgetful

import Prelude ( Show, Eq, ($) )
import Data.Functor ( Functor(..) )
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
        Mempty
    |   Mappend a (FreeMonoid a) deriving (Show, Eq)

-- instances

-- |
-- This instance demonstrates how the structure of
-- `FreeMonoid` allows it to satisfy the Monoid algebra
--
instance Monoid (FreeMonoid a) where
    mempty = Mempty

    x `mappend` y = foldFreeMonoidr Mappend y x

instance Functor FreeMonoid where
    _ `fmap` Mempty         = Mempty
    f `fmap` (Mappend x xs) = Mappend (f x) (fmap f xs)

-- functions

-- |
-- When the `FreeMonoid` functor acts on a type that is already in `Monoid`,
--
-- The trivial additions made by `FreeMonoid` can be translated or "interpreted"
-- back to the `Pointed` algebra of the original type.
--
-- This is basically the `fold` function of the `Foldable` type class.
--
interpretFreeMonoid :: (Monoid a) => FreeMonoid a -> a
interpretFreeMonoid = foldFreeMonoidl mappend mempty

-- helpers

foldFreeMonoidr :: (a -> b -> b) -> b -> FreeMonoid a -> b
foldFreeMonoidr _ x Mempty          = x
foldFreeMonoidr f x (Mappend a as)  = f a (foldFreeMonoidr f x as)

foldFreeMonoidl :: (a -> b -> a) -> a -> FreeMonoid b -> a
foldFreeMonoidl _ x Mempty          = x
foldFreeMonoidl f x (Mappend a as)  = foldFreeMonoidl f (f x a) as
