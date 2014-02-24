---------------------------------------------------------------------------------
-- |
-- Module       : CT.Monad.State
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- Constructing the State Monad from a particular adjunction
--
---------------------------------------------------------------------------------
module CT.Monad.State where

import Control.Comonad ( Comonad(..) )
import Control.Monad ( Monad(..) )
import Data.Functor ( Functor(..) )

-- |
-- The original State Monad
-- a definition derived directly from the utility of the state monad
--
-- This definition is pretty much reproduced from Control.Monad.State in mtl.
--
data State' s a = State' { runState' :: s -> (s, a) }

-- Instances

instance Functor (State' s) where
    f `fmap` (State' g) = State' $ sndMap f . g
        where
            sndMap :: (a -> b) -> (c, a) -> (c, b)
            sndMap func (x, y) = (x, func y)

instance Monad (State' s) where
    return x = State' $ \s -> (s, x)

    mx >>= f = State' $ \s -> let
        (s', x) = runState' mx s
        in runState' (f x) s'

-- | The Store Comonad, again defined directly
-- This definition is reproduced from Control.Comonad.Store in comonad
--
data Store' s a = Store' s (s -> a)

-- Instances

instance Functor (Store' s) where
    f `fmap` (Store' state g) = Store' state (f . g)

-- Helpers

runStore' :: Store' s a -> a
runStore' (Store' state f) = f state

--extendStore :: (Store' s a -> b) -> Store' s a -> Store' s b
--extendStore f (Store' state g) = Store' state $ extend (\g' state' -> f (Store' state' g')) g

--duplicateStore :: Store' s a -> Store' s (Store' s a)
--duplicateStore (Store' state f) = 

-- Now we defined the following two functors, `F` and `G`:

-- | This is the functor that sends X -> S x X
--
data F s a = Pair s a deriving (Show, Eq)

instance Functor (F s) where
    f `fmap` (Pair s x) = Pair s $ f x

-- | This is the functor that sends X -> Hom(S, X)
-- Its technically the Reader Monad
data G s a = Func { runG :: s -> a }

instance Functor (G s) where
    f `fmap` g = Func $ f . runG g

-- These two functors are adjoint (with F being left adjoint to G)

-- That means we can find an isomorphism (`phi`) between Hom(F a, b) and Hom(a, G b) s.t
-- for [k :: a -> a'] and [h :: b -> b'],
--
-- phi (k . f) == fmap k . phi f
-- and
-- phi (f . fmap h) == phi f . h
--
-- and if phi' is the inverse of phi, then
--
-- phi' (g . h) == phi' g . fmap h
-- and
-- phi' (fmap k . g) == k . phi' g
--

-- | In this case `phi` is the `curry` method from Data.Tuple:
--
curry' :: (F s a -> b) -> a -> G s b
curry' f x = Func $ \state -> f (Pair state x)

-- | And the inverse is the `uncurry` method from Data.Tuple:
--
uncurry' :: (a -> G s b) -> F s a -> b
uncurry' g (Pair state x) = (runG . g) x state

-- Some (undefined) arrows of interesting types to provide insight into what you can do with curry'/uncurry' and fmap

-- | Try [>> :t curry' fautomorphism] in GHCi
--
fautomorphism :: F s a -> F s a
fautomorphism = undefined

-- | Try [>> :t uncurry' gautomorphism] in GHCi
--
gautomorphism :: G s a -> G s a
gautomorphism = undefined


kleisliArrow :: a -> G s (F s b)
kleisliArrow = undefined

-- by choosing the "canonical" or "obvious" functions for `fautomorphism` and `gautomorphism` and using `curry'` and `uncurry'` (and their properties)
-- we can derive our units

unit' :: a -> G s (F s a)
unit' = curry' id

-- | this is the "counit" for `unit'` under the adjunction [F,G]
--
counit' :: F s (G s b) -> b
counit' = uncurry' id

-- | this is technically also a co unit for unit' but under a different adjunction, so we just call it "join" here
--
join'' :: G s (F s (G s (F s a))) -> G s (F s a)
join'' = fmap counit'

duplicate'' :: F s (G s b) -> F s (G s (F s (G s b)))
duplicate'' = fmap unit'

-- | Now we define the State monad another way...
-- via the composition G . F
data State'' s a = State'' { runState'' :: G s (F s a) }

-- | And similarly we can redefine the Store Comonad
--
data Store'' s a = Store'' { runStore'' :: F s (G s a)}

-- Just some boiler plate to translate `unit'`, `counit'`, `join'` and `duplicate'`
-- over to `State''` and `Store''`

unit :: a -> State'' s a
unit = State'' . unit'

counit :: Store'' s a -> a
counit = counit' . runStore''

join' :: State'' s (State'' s a) -> State'' s a
join' = State'' . join'' . runState'' . fmap runState''

duplicate' :: Store'' s a -> Store'' s (Store'' s a)
duplicate' =  fmap Store'' . Store'' . duplicate'' . runStore''

-- Instances

instance Functor (State'' s) where
    fmap f = State'' . fmap (fmap f) . runState''

instance Monad (State'' s) where
    return = unit

    ma >>= f = (join' . fmap f) ma

instance Functor (Store'' s) where
    fmap f = Store'' . fmap (fmap f) . runStore''

instance Comonad (Store'' s) where
    extract = counit

    duplicate = duplicate'
