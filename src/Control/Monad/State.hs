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
-- for [k :: b -> b'] and [h :: a -> a'],
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
-- @
-- unphi (g . h) == unphi g . fmap h
-- @
--
-- and
--
-- @
-- unphi (fmap k . g) == k . unphi g
-- @
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
-- first its interesting to consider the following result:
--
-- for some [s' :: s], [x :: a], and [g :: a -> G s b]
--
-- Func $ \s' -> (runG . g) x s'    == Func $ \s' -> (runG (g x)) s'    -- expanding out the (.)
--                                  == Func $ \s' -> g' s'              -- let @g' :: s -> b; g' = runG (g x)@
--                                  == Func g'                          -- @\s' -> g' s' == g'@
--                                  == Func $ runG (g x)                -- @g' == runG (g x)@
--                                  == (Func . runG) (g x)
--                                  == g x                              -- using @Func . runG == id@
--
-- hence for all [s' :: s], [x :: a], [g :: a -> G s b],
--
-- @
-- Func $ \s' -> (runG . g) x s' == g x
-- @
--
-- Which i will refer back to with (**)
--
-- @
-- (phi . unphi) g      == phi (\(Pair s x) -> (runG . g) x s)                                   -- (expanding `unphi g`)
--                      == \x' -> (Func $ \s' -> ((\(Pair s x) -> (runG . g) x s) (Pair s' x'))) -- (expanding `phi`)
--                      == \x' -> (Func $ \s' -> (runG . g) x' s')                               -- (reducing @((\(Pair s x) -> (runG . g) x s) (Pair s' x'))@)
--                      == \x' -> g x'                                                           -- (rewriting using (**))
--                      == g                                                                     -- (reducing @\x' -> g x'@)
-- @
--
-- hence `phi` is indeed a one to one bijection, with `unphi` as its inverse
--
-- the result that @Func $ \s' -> (runG . g) x' s' == g x'@, @forall g. g :: (a -> G s b)@ is a handy result
--
-- Naturality
--
-- 1) @phi (k . f) == fmap k . phi f@
--
-- (I work through one direction of the proof, and leave the reversibility of the steps as an exercise):
--
-- @forall k. k :: b -> b'@,
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
-- 2) phi (f . fmap h) == phi f . h
--
-- @forall h. h :: a -> a'@
--
-- @
-- phi (f . fmap h) == \x -> Func $ \s -> (f . fmap h) (Pair s x)       -- (expanding @phi@)
-- phi (f . fmap h) == \x -> Func $ \s -> f (fmap h (Pair s x))         -- (by the definition of (.))
-- phi (f . fmap h) == \x -> Func $ \s -> f (Pair s (h x))              -- (from the definition of `fmap` for `F`)
-- phi (f . fmap h) == (\x -> Func $ \s -> f (Pair s x)) . (\x -> h x)  -- (from the definition of (.))
-- phi (f . fmap h) == (\x -> Func $ \s -> f (Pair s x)) . h            -- (@(\x -> h x) == h@)
-- phi (f . fmap h) == phi f . h                                        -- (@phi f == \x -> Func $ \s -> f (Pair s x)@)
-- @
--
-- 3) unphi (g . h) == unphi g . fmap h
--
-- @forall h. h :: a -> a'@
--
-- @
-- unphi (g . h)    == \(Pair state x) -> (runG . (g . h)) x state                                      -- (expanding @unphi@)
--                  == \(Pair state x) -> (runG . g) (h x) state                                        -- (from the definition of (.))
--                  == (\(Pair state x) -> (runG . g) x state) . (\(Pair state x) -> Pair state (h x))  -- (by the definition of (.))
--                  == unphi g . (\(Pair state x) -> Pair state (h x))                                  -- (from the definition of @unphi@)
--                  == unphi g . fmap h                                                                 -- (from the definition of @fmap@ for `F`)
-- @
--
-- 4) @unphi (fmap k . g) == k . unphi g@
--
-- @forall k. k :: b -> b'@
--
-- @
-- unphi (fmap k . g)   == \(Pair state x) -> (runG . (fmap k . g)) x state         -- (expanding @unphi@)
--                      == \(Pair state x) -> (runG . fmap k) (g x) state           -- (by the definition of (.))
--                      == \(Pair state x) -> (runG . fmap k) (g x) state           -- (by the definition of (.))
--                      == \(Pair state x) -> (runG (fmap k (g x))) state           -- (by the definition of (.))
--                      == \(Pair state x) -> (runG (Func $ k . runG (g x))) state  -- (by the definition of `fmap` for `G`)
--                      == \(Pair state x) -> (k . runG (g x)) state                -- (using @runG . Func@)
--                      == k . (\(Pair state x) -> (runG (g x)) state)              -- (using the definition of (.))
--                      == k . (\(Pair state x) -> (runG . g) x state)              -- (using the definition of (.))
--                      == k . unphi g                                              -- (using the definition of @unphi@)
-- @
--
-- Hence (again leaving the reverse directions as an exercise), `phi` is /natural/ in its underlying categories `C` and `D` (in this case
-- they are both (Proper) Hask).

-- Some (undefined) arrows of interesting types to provide insight into what you can do with `phi`, `unphi` and `fmap`

-- | Try [>> :t phi fautomorphism] in GHCi
--
-- @

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

-- The Monad Laws
--
-- Reviewing the Monad Laws (<http://hackage.haskell.org/package/base-4.6.0.1/docs/Control-Monad.html#t:Monad>):
--
-- 1) @return a >>= k  ==  k a@                         (`return` is a 'left identity' of sorts for the bind)
-- 2) @m >>= return  ==  m@                             (`return` is a 'right identity' of sorts for the bind)
-- 3) @m >>= (\x -> k x >>= h)  ==  (m >>= k) >>= h@    (bind is Associative)
--
-- From here on in i will not differentiate between @foo'@, @foo''@, @foo'''@, etc.. for any @foo@, they are all fundamentally
-- The same thing. I.e from here on in:
--
-- @ return = unit = phi id @
-- @ extract = counit = unphi id @
-- @ join = fmap counit @ using the Functor instance for `G`
-- @ duplicate = fmap unit @ using the Functor instance for `F`
--
-- we'll also be using this fact: @ m >>= f == (join . fmap (fmap f)) m @  (See the Functor instance of State'' to see why there are two fmaps here...)
--
-- We can rewrite the laws in the following equivalent forms:
--
-- 1:
-- @
--      k   == (phi . unphi) k
--          == phi (unphi k)
--          == phi (unphi (id . k))
--          == phi (unphi id . fmap k)
--          == phi (counit . fmap k)
--          == fmap counit . phi (fmap k)
--          == join . phi (fmap k)
--          == join . phi (fmap k . id)
--          == join . fmap (fmap k) . phi id
--          == join . fmap (fmap k) . unit
--
--     hence
--     k a  == (join . fmap (fmap k) . unit) a
--          == (join . fmap (fmap k)) (unit a)
--          == unit a >>= k
--          == return a >>= k
-- @
--
-- (Once again its left as an exercise to show that the steps are reversible)
--
-- 2:
--
-- @
--     id   == fmap id
--          == fmap (unphi (phi id))
--          == fmap (unphi unit)
--          == fmap (unphi (id . unit))
--          == fmap (unphi id . fmap unit)
--          == fmap (counit . fmap unit)
--          == fmap counit . fmap (fmap unit)
--          == join . fmap (fmap unit)
--          == join . fmap (fmap return)
--
--     and so:
--
--     m    == id m
--          == join . fmap (fmap return) m
--          == m >>= return
-- @
--
-- (Exercise to show the steps are reversible)
--
-- 3:
--
-- @
--      m >>= (\x -> k x >>= h) == join . fmap (fmap (\x -> k x >>= h)) m
--                              == join . fmap (fmap (\x -> (join . fmap (fmap h)) (k x))) m
--                              == join . fmap (fmap ((\x -> (join . fmap (fmap h)) x) . k)) m
--                              == join . fmap (fmap ((join . fmap (fmap h)) . k)) m
--
--      and
--
--      join . fmap (fmap ((join . fmap (fmap h)) . k)) == join . fmap (fmap (f . k))    -- (let f = (join . fmap (fmap h)))
--                                                      == join . fmap (fmap f . fmap k)
--                                                      == join . ()
-- @
