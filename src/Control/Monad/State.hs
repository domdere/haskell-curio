---------------------------------------------------------------------------------
-- |
-- Module       : Control.Monad.State
-- Copyright    : (C) 2014 Dom De Re
-- License      : BSD-style (see the file etc/LICENSE.md)
-- Maintainer   : Dom De Re
--
-- Constructing the State Monad from a particular adjunction
--
---------------------------------------------------------------------------------
module Control.Monad.State where

import Prelude ( Show, Eq, ($), undefined )
import Control.Comonad ( Comonad(..) )
import Control.Monad ( Monad(..) )
import Data.Function ( (.), const, id )
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

instance Comonad (Store' s) where
    extract (Store' state f) = f state

    duplicate x@(Store' state _) = Store' state $ const x

-- Helpers

runStore' :: Store' s a -> a
runStore' (Store' state f) = f state

--extendStore :: (Store' s a -> b) -> Store' s a -> Store' s b
--extendStore f (Store' state g) = Store' state $ extend (\g' state' -> f (Store' state' g')) g

duplicateStore :: Store' s a -> Store' s (Store' s a)
duplicateStore x@(Store' state _) = Store' state $ const x

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
-- @
-- phi (k . f) == fmap k . phi f
-- @
--
-- and
--
-- @
-- phi (f . fmap h) == phi f . h
-- @
--
-- and if `unphi` is the inverse of `phi`, then
--
-- unphi (g . h) == unphi g . fmap h
-- and
-- unphi (fmap k . g) == k . unphi g
--
-- (This is what the /naturality/ of `phi` refers to)
--
-- And because its a (set) isomorphism,
--
-- @
-- phi . unphi == id :: (a -> G s b) -> a -> G s b
-- @
--
-- and
--
-- @
-- unphi . phi == id :: (F s a -> b) -> F s a -> b
-- @
--

-- | In this case `phi` is the `curry` method from Data.Tuple:
--
-- @
--     curry :: ((a, s) -> b) -> a -> s -> b
--  == curry :: ((a, s) -> b) -> a -> (s -> b)
--   ~ phi :: (F s a -> b) -> a -> G s b        -- Since (a, s) ~ F s a and (s -> b) ~ G s b
-- @
phi :: (F s a -> b) -> a -> G s b
phi f x = Func $ \state -> f (Pair state x)

-- | And the inverse is the `uncurry` method from Data.Tuple:
--
-- @
--     uncurry :: (a -> s -> b) -> (a, s) -> b
--  == uncurry :: (a -> s -> b) -> ((a, s) -> b)
--   ~ unphi :: (a -> G s b) -> F s a -> b        -- Since (a, s) ~ F s a and (s -> b) ~ G s b
-- @

unphi :: (a -> G s b) -> F s a -> b
unphi g (Pair state x) = (runG . g) x state

-- Isomorphism:
--
-- now lets see what @unphi . phi@ and @phi . unphi@ evaluate to (applying equational reasoning):
--
-- @
-- (unphi . phi) f      == unphi (\x -> Func $ \s -> f (Pair s x))                              -- (expanding `phi f`)
--                      == \(Pair s' x') -> ((runG . (\x -> Func $ \s -> f (Pair s x))) x' s')  -- (expanding `unphi`)
--                      == \(Pair s' x') -> (runG (Func $ \s -> f (Pair s x'))) s'              -- (reducing @(\x -> Func $ \s -> f (Pair s x))) x'@)
--                      == \(Pair s' x') -> (\s -> f (Pair s x')) s'                            -- (evaluating @runG (Func $ \s -> f (Pair s x'))@)
--                      == \(Pair s' x') -> f (Pair s' x')                                      -- (reducing @(\s -> f (Pair s x')) s'@)
--                      == f                                                                    -- (reducing @\(Pair s' x') -> f (Pair s' x')@)
-- @
--
-- Similarly for @phi . unphi@:
--
-- @
-- (phi . unphi) g      == phi (\(Pair s x) -> (runG . g) x s)                                   -- (expanding `unphi g`)
--                      == \x' -> (Func $ \s' -> ((\(Pair s x) -> (runG . g) x s) (Pair s' x'))) -- (expanding `phi`)
--                      == \x' -> (Func $ \s' -> (runG . g) x' s')                               -- (reducing @((\(Pair s x) -> (runG . g) x s) (Pair s' x'))@)
--                      == \x' -> (Func $ \s' -> (runG (g x')) s')                               -- (reducing @runG . g@)
--                      == \x' -> (Func $ \s' -> (runG (Func g')) s')                            -- (rewriting @g x'@ as @Func g'@ for some [g' :: s -> b])
--                      == \x' -> (Func $ \s' -> g' s')                                          -- (rewriting using @runG . Func == id@)
--                      == \x' -> (Func g')                                                      -- (reducing \s' -> g' s')
--                      == \x' -> g x'                                                           -- (using @g x' == Func g'@ again)
--                      == g                                                                     -- (reducing @\x' -> g x'@)
-- @
--
-- hence `phi` is indeed a one to one bijection, with `unphi` as its inverse
--
-- Naturality
--
-- 1) @phi (k . f) == fmap k . phi f@
--
-- (I work through one direction of the proof, and leave the reversibility of the steps as an exercise):
--
-- @forall k. k :: a -> a'@,
--
-- @
-- phi (k . f) == \x -> Func $ \s -> (k . f) (Pair s x)         -- (expanding @phi@)
-- phi (k . f) == \x -> Func $ ((k . f) . l x)                  -- letting @l = flip Pair@
-- phi (k . f) == \x -> Func $ (k . (f . l x))                  -- using the associativity of composition
-- phi (k . f) == \x -> Func $ k . (runG (Func (f . l x)))      -- rewriting using @runG . Func == id@
-- phi (k . f) == \x -> fmap k . Func $ runG (Func (f . l x))   -- rewriting using the definition of `fmap` for `G`
-- phi (k . f) == \x -> fmap k . Func (f . l x)                 -- again using @runG . Func == id@
-- phi (k . f) == \x -> fmap k . Func (\s -> f (Pair s x))      -- using @l = flip Pair@
-- phi (k . f) == fmap k . (\x -> Func (\s -> f (Pair s x)))    -- again by associativity of composition
-- phi (k . f) == fmap k . phi f                                -- by the definition of `phi`
-- @
--

-- Some (undefined) arrows of interesting types to provide insight into what you can do with `phi`, `unphi` and `fmap`

-- | Try [>> :t phi fautomorphism] in GHCi
--
fautomorphism :: F s a -> F s a
fautomorphism = undefined

-- | Try [>> :t unphi gautomorphism] in GHCi
--
gautomorphism :: G s a -> G s a
gautomorphism = undefined


kleisliArrow :: a -> G s (F s b)
kleisliArrow = undefined

-- by choosing the "canonical" or "obvious" functions for `fautomorphism` and `gautomorphism` and using `phi` and `unphi` (and their properties)
-- we can derive our units

-- |
-- try [>> :t curry id] in GHCi, it will probably look closer to what you would recognise as the type for the `State` monads `return`.
--
unit' :: a -> G s (F s a)
unit' = phi id

-- | this is the "counit" for `unit'` under the adjunction [F,G]
--
-- again if it doesnt make sense to you, try [>> :t uncurry id] in GHCi, and it will most likely looks more recognisable to you as
-- the `Store` Comonads `extract`.
--
counit' :: F s (G s b) -> b
counit' = unphi id

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
data Store'' s a = Store'' { runStore'' :: F s (G s a) }

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
