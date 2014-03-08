---------------------------------------------------------------------------------
-- |
-- Module       : Data.Pointed
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- Haskell type class for the Pointed Set algebra
--
---------------------------------------------------------------------------------
module Data.Pointed (
        Pointed(..)
    ) where

-- |
-- In mathematics the elements of an ordinary set are generally of the same level of significance.
-- A pointed set is a Set where one element is distinguished as the "base" point.
-- A pointed set homomorphism @ f :: (Pointed a, Pointed b) => a -> b @ is a function
-- where @ f base = base @
--
-- This concept is unrelated (as far as I can tell) to the `Point` typeclass.
--
class Pointed a where
    base :: a
