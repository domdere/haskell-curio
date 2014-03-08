---------------------------------------------------------------------------------
-- |
-- Module       : Data.Functor.FreePointed
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- The Free functor that maps a type in (Proper) Hask to the subcategory of
-- "Pointed Sets", where the objects are pointed sets as described in
-- `Data.Pointed` and the arrows are pointed set homomorphisms, again as
-- described in `Data.Pointed`
--
-- The `FreePointed` functor is an examination of the `Maybe` monad
--
---------------------------------------------------------------------------------
module Data.Functor.FreePointed (
    -- * The Free Functor
        FreePointed(..)
    -- * The interpreter of Free Pointed Sets
    ,   interpretFreePointed
    ) where

import Data.Functor.Forgetful
import Data.Pointed

import Prelude ( Show, Eq, ($) )
import Data.Functor ( Functor(..) )

-- |
-- The FreePointed functor takes any arbitrary type and extends it so that it
-- is inside `Pointed`, by adding the trivial element necessary to satisfy its
-- algebra.
--
data FreePointed a =
        Base
    |   Just a deriving (Show, Eq)

-- instances

-- |
-- The `FreePointed` functor acts on any arbitrary type by
-- Adding the `Base` vallue to the type so that it can
-- satisfy the `Pointed` algebra (`base`).
--
instance Pointed (FreePointed a) where
    base = Base

instance Functor FreePointed where
    _ `fmap` Base       = Base
    f `fmap` (Just x)   = Just $ f x

-- functions

-- |
-- When the `FreePointed` functor acts on a type that is already in `Pointed`,
--
-- The trivial additions made by `FreePointed` can be translated or "interpreted"
-- back to the `Pointed` algebra of the original type.
--
interpretFreePointed :: (Pointed p) => FreePointed p -> p
interpretFreePointed Base       = base
interpretFreePointed (Just x)   = x
