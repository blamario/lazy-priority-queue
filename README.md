Lazy Priority Queue
==================

### Collection of costed computations ###

This library represents another point in the monadic priority queue design space already inhabited by
[monad-dijkstra](http://hackage.haskell.org/package/monad-dijkstra) and [A*
Monad](http://hackage.haskell.org/package/astar-monad). It shares with them the monadic interface, the ability to
assign concrete cost to each running computation, and the ability to extract the least costly result.

The present library is simpler in that it's implemented quite simply as a priority queue data structure. It is not a
monad transformer. On the other hand, it provides several operations that are not available elsewhere.

Compared to other priority queue data structures on Hackage, this one is meticulously lazy. It has to be in order to
avoid forcing computations that we may later decide to abandon in favour of a better one.

As one example of use, the included executable calculates the Levenshtein distance of two strings. Below is another
example of Manhattan distance adjusted from [A* Monad](http://hackage.haskell.org/package/astar-monad).

~~~ {.haskell}
{-# LANGUAGE TemplateHaskell #-}
import Control.Lens ((+~), (-~), (<>~), (&), _1, _2)
import Control.Lens.TH (makeLenses)
import Data.Foldable (asum)
import Data.Monoid (Sum(..))
import Data.PriorityQueue

-- Track which moves we've made, up, down, left or right
data Move = U | D | L | R
    deriving (Show, Eq)

-- Track our current position, the goal we're moving towards, and the moves we've taken so far.
data Context =
    Context { _currentPos :: (Int, Int)
            , _goal    :: (Int, Int)
            , _moves   :: [Move]
            }
    deriving (Show, Eq)

makeLenses ''Context

-- Move around the space looking for the destination point.
findPoint :: Context -> PQueue Branching (Sum Int) Context
findPoint context
    | _currentPos context == _goal context = pure context
    | otherwise = do
         -- Register the cost of a move
         cost (Sum 1)
         -- Non-deterministically choose a direction to move, 
         -- store that move in our state, and edit our current position.
         asum
            [ findPoint $ context & moves <>~ [R] & currentPos . _1 +~ 1
            , findPoint $ context & moves <>~ [L] & currentPos . _1 -~ 1
            , findPoint $ context & moves <>~ [D] & currentPos . _2 +~ 1
            , findPoint $ context & moves <>~ [U] & currentPos . _2 -~ 1
            ]

run :: PQueue Pruned (Sum Int) Context
run = canonical $ prune $ findPoint
             Context { _currentPos = (5, 5)
                     , _goal    = (7, 4)
                     , _moves   = []
                     }

main = print run
~~~
