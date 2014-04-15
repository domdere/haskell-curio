module Data.Aggregator where

import Prelude ( ($) )
import Data.List ( foldl' )
import Data.Maybe ( Maybe(..) )
import Data.Ord ( Ord, min, max )

minMaybe :: (Ord a) => Maybe a -> a -> Maybe a
minMaybe Nothing x  = Just x
minMaybe (Just x) y = Just $ min x y

maxMaybe :: (Ord a) => Maybe a -> a -> Maybe a
maxMaybe Nothing x = Just x
maxMaybe (Just x) y = Just $ max x y

minFold :: (Ord a) => [a] -> Maybe a
minFold = foldl' minMaybe Nothing

maxFold :: (Ord a) => [a] -> Maybe a
maxFold = foldl' maxMaybe Nothing

diag :: (b -> a -> b) -> (c -> a -> c) -> (b, c) -> a -> (b, c)

minMaxFold :: (Ord a) => [a] -> Maybe (a, a)
minMaxFold 
