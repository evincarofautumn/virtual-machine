{-# LANGUAGE ScopedTypeVariables #-}

module Utils where

import Data.Monoid

type Build a = a -> a

bug :: String -> a
bug = error

mconcatMap :: (Monoid b) => (a -> b) -> [a] -> b
mconcatMap = mconcat .: map

spanJust :: (a -> Maybe b) -> [a] -> ([b], [a])
spanJust f = go []
  where
  -- These 'reverse's could be gotten rid of with a bit more cleverness.
  go ys l = case l of
    x : xs -> case f x of
      Just y -> go (y : ys) xs
      Nothing -> end
    [] -> end
    where
    end = (reverse ys, l)

spanJust1 :: (a -> Maybe b) -> [a] -> (Maybe b, [a])
spanJust1 f l@(x : xs) = case f x of
  Nothing -> (Nothing, l)
  x'@Just{} -> (x', xs)
spanJust1 _ [] = (Nothing, [])

splitWhen :: forall a. (a -> a -> Bool) -> [a] -> [[a]]
splitWhen f = foldr go [[]]
  where
  go :: a -> [[a]] -> [[a]]
  go x ys@(z@(y : _) : zs) = if f x y then [x] : ys else (x : z) : zs
  go x ([] : zs) = [x] : zs
  go _ _ = error "splitWhen: the impossible happened"

{-# INLINE (.:) #-}
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = (.) . (.)
