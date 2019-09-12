{-
    Copyright (C) Stilo International plc, 2019

    This source code is unpublished proprietary information of Stilo
    Corporation.  The copyright notice above does not evidence any
    actual or intended publication of such source code.

    This file may not be redistributed as source, either by itself,
    or as part of software derived from this file.
-}

{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, UndecidableInstances #-}

module Data.PriorityQueue (PQueue, Branching, Pruned,
                           branchable, prune, pruneAbove, pruneAlternativesAbove, mapWithCost, filter, foldPeers,
                           canonical, pruneSubsets, strip, stripCommon,
                           cost, leastCost, withCost) where

import Control.Applicative (Applicative(..), Alternative(..))
import Data.Coerce (coerce)
import Data.Foldable (Foldable(fold))
import Data.Monoid (Monoid(mempty, mappend), Alt(Alt, getAlt))
import Data.Semigroup (Semigroup((<>)))

import Prelude hiding (filter)

data Branching
data Pruned

data PQueue t c a = Costly !c (PQueue t c a)
                  | Free !(Ground a) (PQueue t c a)
                  | Empty
                  deriving Show

data Ground a = Leaf a
              | Peer !(Ground a) !(Ground a)
              deriving Show

instance Foldable Ground where
   foldMap f (Leaf a) = f a
   foldMap f (Peer g h) = foldMap f g <> foldMap f h

instance Functor Ground where
   fmap f (Leaf a) = Leaf (f a)
   fmap f (Peer g h) = Peer (fmap f g) (fmap f h)

instance Applicative Ground where
   Leaf f <*> g = f <$> g
   Peer g1 g2 <*> h = Peer (g1 <*> h) (g2 <*> h)
   pure = Leaf

instance Foldable (PQueue t c) where
   foldMap f (Costly _ q) = foldMap f q
   foldMap f (Free a q) = foldMap f a <> foldMap f q
   foldMap f Empty = mempty

instance Functor (PQueue t c) where
   fmap f (Costly c q) = Costly c (fmap f q)
   fmap f (Free a q) = Free (fmap f a) (fmap f q)
   fmap _ Empty = Empty

instance (Alternative (PQueue t c), Semigroup c) => Applicative (PQueue t c) where
   Costly c1 q1 <*> Costly c2 q2 = Costly (c1 <> c2) (q1 <*> q2)
   Costly c q1 <*> q2 = Costly c (q1 <*> q2)
   q1 <*> Costly c q2 = Costly c (q1 <*> q2)
   Free f q1 <*> Free a q2 = Free (f <*> a) (mapPeers (f <*>) q2 <|> mapPeers (<*> a) q1 <|> q1 <*> q2)
      where mapPeers f (Free g q) = Free (f g) (mapPeers f q)
            mapPeers f (Costly c q) = Costly c (mapPeers f q)
            mapPeers f Empty = Empty
   Empty <*> _ = Empty
   _ <*> Empty = Empty
   pure a = Free (Leaf a) Empty
   {-# INLINABLE (<*>) #-}

instance (Num c, Ord c, Semigroup c) => Alternative (PQueue Branching c) where
   Costly c1 q1 <|> Costly c2 q2 = {-# SCC "AltB.compare" #-}
      case compare c1 c2
      of LT -> Costly c1 (q1 <|> Costly (c2 - c1) q2)
         GT -> Costly c2 (Costly (c1 - c2) q1 <|> q2)
         EQ -> Costly c1 (q1 <|> q2)
   Free a q1 <|> Free b q2 = Free (Peer a b) (q1 <|> q2)
   Free a q1 <|> q2 = Free a (q1 <|> q2)
   q1 <|> Free a q2 = Free a (q1 <|> q2)
   Empty <|> pq = pq
   pq <|> Empty = pq
   empty = Empty
   {-# INLINABLE (<|>) #-}

instance (Num c, Ord c, Semigroup c) => Alternative (PQueue Pruned c) where
   Costly c1 q1 <|> Costly c2 q2 = {-# SCC "AltP.compare" #-}
      case compare c1 c2
      of LT -> Costly c1 (q1 <|> Costly (c2 - c1) q2)
         GT -> Costly c2 (Costly (c1 - c2) q1 <|> q2)
         EQ -> Costly c1 (q1 <|> q2)
   Free a _ <|> _ = Free a Empty
   _ <|> Free a _ = Free a Empty
   Empty <|> pq = pq
   pq <|> Empty = pq
   empty = Empty
   {-# INLINABLE (<|>) #-}

instance (Semigroup c, Alternative (PQueue t c)) => Monad (PQueue t c) where
   Costly c q >>= f = Costly c (q >>= f)
   Free a q >>= f = getAlt (foldMap (Alt . f) a) <|> (q >>= f)
   Empty >>= _ = Empty
   {-# INLINABLE (>>=) #-}

-- | @withCost k@ adds a penalty of k to each value in the queue.
withCost :: (Semigroup c, Num c, Ord c) => c -> PQueue t c a -> PQueue t c a
withCost 0 q = q
withCost c q | c <= 0 = error "The cost must be non-negative!"
             | otherwise = Costly c q
{-# INLINE withCost #-}

-- | Fold together all stored values that share the same priority.
foldPeers :: (a -> a -> a) -> PQueue t c a -> PQueue t c a
foldPeers _ Empty = Empty
foldPeers f (Costly c q) = Costly c (foldPeers f q)
foldPeers f (Free g q) = Free (Leaf a'') q''
   where (a'', q'') = case foldPeers f q
                      of Free (Leaf b) q' -> (f a' b, q')
                         q' -> (a', q')
         a' = foldGroundPeers f g

foldGroundPeers :: (a -> a -> a) -> Ground a -> a
foldGroundPeers _ (Leaf a) = a
foldGroundPeers f (Peer l r) = f (foldGroundPeers f l) (foldGroundPeers f r)

-- | Imposes the given cost on the current computation branch.
-- > cost k = withCost k (pure ())
cost :: (Semigroup c, Num c, Ord c) => c -> PQueue Branching c ()
cost 0 = pure ()
cost k | k > 0 = Costly k (pure ())

-- | Relax the 'Pruned' phantom constraint, allowing the queue to become 'Branching'.
branchable :: PQueue Pruned c a -> PQueue t c a
branchable = coerce

-- | Prune away all stored values more expensive than the given cost.
pruneAbove :: (Semigroup c, Num c, Ord c) => c -> PQueue t c a -> PQueue t c a
pruneAbove k _
   | k < 0 = Empty
pruneAbove k (Costly c q)
   | k' < 0 = Empty
   | otherwise = Costly c (pruneAbove k' q)
   where k' = k - c
pruneAbove k (Free a q) = Free a (pruneAbove k q)
pruneAbove _ Empty = Empty
{-# INLINABLE pruneAbove #-}

-- | Prune away all stored values more expensive than the given cost and a less expensive alternative value.
pruneAlternativesAbove :: (Semigroup c, Num c, Ord c) => c -> PQueue t c a -> PQueue t c a
pruneAlternativesAbove k q
   | k <= 0 = q
pruneAlternativesAbove k (Costly c q) = Costly c (pruneAlternativesAbove (k - c) q)
pruneAlternativesAbove k (Free a q) = Free a (pruneAbove k q)
pruneAlternativesAbove _ Empty = Empty
{-# INLINABLE pruneAlternativesAbove #-}

-- | Prune away all stored values except the one with the least penalty, making the queue 'Pruned'.
prune :: PQueue t c a -> PQueue Pruned c a
prune (Costly c q) = Costly c (prune q)
prune (Free a q) = Free (Leaf $ leftmost a) Empty
   where leftmost :: Ground a -> a
         leftmost (Leaf a) = a
         leftmost (Peer l r) = leftmost l
prune Empty = Empty

-- | Minimize the queue structure. This operation forces the entire spine of the queue and its every level.
canonical :: Semigroup c => PQueue t c a -> PQueue t c a
canonical (Costly c1 (Costly c2 q)) = canonical (Costly (c1 <> c2) q)
canonical (Costly c q) = Costly c (canonical q)
canonical (Free a q) = Free a (canonical q)
canonical Empty = Empty

-- | Filter away from the queue the values that the argument function maps to `False`
filter :: (a -> Bool) -> PQueue t c a -> PQueue t c a
filter f (Costly c q) = Costly c (filter f q)
filter f (Free g q) = maybe id Free (filterGround g) (filter f q)
   where filterGround g@(Leaf a) = if f a then Just g else Nothing
         filterGround (Peer g1 g2) = case (filterGround g1, filterGround g2)
                                     of (Just g1', Just g2') -> Just (Peer g1' g2')
                                        (Just g', Nothing) -> Just g'
                                        (Nothing, Just g') -> Just g'
                                        (Nothing, Nothing) -> Nothing
filter _ Empty = Empty

-- | Assuming the stored values belong to a cancellative monoid, prune away all extraneous values and factors using the
-- supplied function that calculates the sum and difference of the two values, if there is any difference, and the monoid null.
-- > fold (pruneSubsets plusDiff mempty pq) == fold pq
-- >   where plusDiff u a
-- >           | gcd u a == a = Nothing
-- >           | d <- a - gcd u a = Just (u <> d, d)
pruneSubsets :: (a -> b -> Maybe (a, b)) -> a -> PQueue t c b -> PQueue t c b
pruneSubsets unionDiff set (Costly c q) = Costly c (pruneSubsets unionDiff set q)
pruneSubsets unionDiff set (Free g q) =
   case pruneGroundSubsets unionDiff set g
   of Nothing -> pruneSubsets unionDiff set q
      Just (set', g') -> Free g' (pruneSubsets unionDiff set' q)
pruneSubsets _ _ Empty = Empty

pruneGroundSubsets :: (a -> b -> Maybe (a, b)) -> a -> Ground b -> Maybe (a, Ground b)
pruneGroundSubsets unionDiff set (Leaf l) = case unionDiff set l
                                            of Nothing -> Nothing
                                               Just (set', l') -> Just (set', Leaf l')
pruneGroundSubsets unionDiff set (Peer g1 g2) =
   case pruneGroundSubsets unionDiff set g1
   of Nothing -> pruneGroundSubsets unionDiff set g2
      Just (set', g1') -> case pruneGroundSubsets unionDiff set' g2
                          of Nothing -> Just (set', g1')
                             Just (set'', g2') -> Just (set'', Peer g1' g2')

-- | Returns the pair of the GCD of all the penalties and the penalties without the GCD
-- > gcd <*> rest == f
-- >   where (gcd, rest) = stripCommon f
stripCommon :: (Ord c, Num c, Functor f, Foldable f, Alternative (PQueue t c)) =>
               f (PQueue t c a) -> (PQueue Pruned c (a -> a), f (PQueue t c a))
stripCommon f = (common, strip common <$> f)
   where common = const id <$> prune (getAlt $ foldMap Alt f)

-- | Subtract the first argument cost GCD from the cost of every value in the second argument
strip :: (Ord c, Num c) => PQueue Pruned c a -> PQueue t c b -> PQueue t c b
strip (Costly c q1) q2 = stripCost c (strip q1 q2)
strip _ q = q

stripCost :: (Ord c, Num c) => c -> PQueue t c a -> PQueue t c a
stripCost c (Costly c' q)
   | c < c' = Costly (c' - c) q
   | c > c' = stripCost (c - c') q
   | otherwise = q
stripCost _ Empty = Empty
-- stripCost c q = error ("stripCost " <> show c <> " " <> show (() <$ q))

-- | Returns 'Just' the minimal cost present in the queue, 'Nothing' if the queue is empty.
leastCost :: Monoid c => PQueue t c a -> Maybe c
leastCost (Costly c q) = (c <>) <$> leastCost q
leastCost Free{} = Just mempty
leastCost Empty = Nothing

-- | Maps each item contained in the queue, supplying the item's cost as first argument
mapWithCost :: Monoid c => (c -> a -> b) -> PQueue t c a -> PQueue t c b
mapWithCost f (Costly c q) = Costly c (mapWithCost (f . (c <>)) q)
mapWithCost f (Free a q) = Free (f mempty <$> a) (mapWithCost f q)
mapWithCost _ Empty = Empty
