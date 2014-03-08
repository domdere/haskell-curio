---------------------------------------------------------------------------------
-- |
-- Module       : Control.Monad.Maybe
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- Constructing the Maybe monad from the adjunction between the `FreePointed` and
-- `U` functors.
--
---------------------------------------------------------------------------------
module Control.Monad.Maybe (
    -- * The Maybe Monad
        Maybe(..)
    -- * The Hom-set Isomorphism that defines the FreePointed and U adjunction
    ,   pointedphi
    ,   pointedunphi
    -- * Units and counits
    ,   pointedunit'
    ,   pointedunit
    ,   pointedcounit'
    ,   pointedjoin'
    ,   pointedjoin
    ) where

import Data.Functor.Forgetful
import Data.Functor.FreePointed
import Data.Pointed

import Prelude (Show, Eq, ($) )
import Control.Monad ( Monad(..) )
import Data.Function ( (.), id )
import Data.Functor ( Functor(..) )

newtype Maybe a = Maybe { unMaybe :: U (FreePointed a) } deriving (Show, Eq)

-- instances

instance Functor Maybe where
    fmap f = Maybe . fmap (fmap f) . unMaybe

instance Monad Maybe where
    return = pointedunit

    ma >>= f = pointedjoin $ fmap f ma

-- |
-- The monad adjunction between `FreePointed` and `U` means there
-- is a `phi` and `unphi` exist.
-- and for [k, f :: (Pointed a, Pointed b) => a -> b] a pointed set
-- homomorphism as described in `Data.Pointed` and
-- [h, g :: a' -> b'] a plain set homomorphism
--
-- @ pointedphi (k . f) = fmap k . pointedphi f @
-- @ pointedphi (f . fmap h) = pointedphi f . h @
--
-- and
--
-- @ pointedunphi (g . h) = pointedunphi g . fmap h @
-- @ pointedunphi (fmap h . g) = h . pointedunphi g@
--
pointedphi :: (Pointed p) => (FreePointed a -> p) -> a -> U p
pointedphi f = U . f . Just

pointedunphi :: (Pointed p) => (a -> U p) -> FreePointed a -> p
pointedunphi f = interpretFreePointed . fmap (unforget . f)

pointedunit' :: a -> U (FreePointed a)
pointedunit' = pointedphi id

pointedcounit' :: (Pointed p) => FreePointed (U p) -> p
pointedcounit' = pointedunphi id

pointedunit :: a -> Maybe a
pointedunit = Maybe . pointedunit'

pointedjoin' :: U (FreePointed (U (FreePointed a))) -> U (FreePointed a)
pointedjoin' = fmap pointedcounit'

pointedjoin :: Maybe (Maybe a) -> Maybe a
pointedjoin = Maybe . pointedjoin' . unMaybe . fmap unMaybe
