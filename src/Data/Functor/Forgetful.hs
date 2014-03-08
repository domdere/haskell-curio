---------------------------------------------------------------------------------
-- |
-- Module       : Data.Functor.Forgetful
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- A functor that takes a type and "forgets" its algebras
--
-- This functor is mostly used in mathematical definitions and proofs,
--
-- But in practice in FP, since the properties that mathematically set @ U a @
-- apart from @ a @ are pretty superficial from an applied perspective, its
-- dropped since it would just increase boilerplate code and serves no practical
-- purpose.
--
---------------------------------------------------------------------------------
module Data.Functor.Forgetful (
        U(..)
    ,   unforget
    ) where

import Prelude ( Show, Eq, ($) )
import Data.Functor ( Functor(..) )

-- |
-- The forgetful functor takes a type and strips away its algebras.
--
-- Typically in mathematics each algebra has a specific forgetful functor,
-- But for my purposes, I'll use this to implement each semantically distinct
-- Forgetful functor (at least the ones that strip away *all* of its algebras)
--
-- For instance, this functor cannot be used to "implement"
-- the forgetful functor that takes a monad to a functor.
--
newtype U a = U a deriving (Show, Eq)

-- instances

instance Functor U where
    f `fmap` (U x) = U $ f x

-- |
-- when we map something with @ U :: a -> U a @ its like a function @ f :: <S, *> -> S @
-- in mathematics which maps an element in @ S @ with the algebra @ * @ to the same element in @ S @ but without
-- the @ * @ algebra attached to it.  Other than thats its basically the set identity function.
--
-- Similarly for any algebra @ * @ we can define a function that goes from @ g :: S -> <S, *> @ that
-- is effectively the same as the set identity function but attaches the @*@ algebra back to it.
--
-- `unforget` picks the original algebras attached to @ a @ and reattaches them.
--
unforget :: U a -> a
unforget (U x) = x
