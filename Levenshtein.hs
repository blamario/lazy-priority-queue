-- ./Levenshtein "$(cat ../web/regression/test/blocks/input/input.xml)" "$(cat ../web/regression/test/blocks/output/input.xml)"
{-# Language DeriveFunctor #-}

import Control.Applicative
import Data.Monoid (Sum(..))
import Data.Semigroup (First(..), Option(Option, getOption), option)
import System.Environment (getArgs)
import qualified Data.IntMap.Strict as IntMap

import Data.PriorityQueue

data Edit a = Keep !a
            | Delete !a
            | Insert !a
            | Replace !a !a
            deriving (Eq, Show, Functor)

totalCost :: [Edit a] -> Int
totalCost = getSum . foldMap editCost

editCost :: Edit a -> Sum Int
editCost Keep{} = Sum 0
editCost _ = Sum 1

-- | A naïve Levenshtein distance function suffers from an exponential explosion problem.
naïve :: Eq a => [a] -> [a] -> [Edit a]
naïve [] goal = Insert <$> goal
naïve origin [] = Delete <$> origin
naïve (x:xs) (y:ys)
   | x == y = Keep x : naïve xs ys
   | deletionCost < insertionCost && deletionCost < replacementCost = deletion
   | insertionCost < deletionCost && insertionCost < replacementCost = insertion
   | otherwise = replacement
   where deletion = Delete x : naïve xs (y:ys)
         insertion = Insert y : naïve (x:xs) ys
         replacement = Replace x y : naïve xs ys
         deletionCost = totalCost deletion
         insertionCost = totalCost insertion
         replacementCost = totalCost replacement

-- | We shall keep track of the partial solution of the problem in this data structure.
data Partial a = Partial {
   -- | length of the matched prefixes of the two strings
   xlen, ylen :: !Int,
   -- | remaining unmatched suffixes of the two strings
   xrest, yrest :: [a],
   -- | calculated edits that convert the first prefix into the second
   delta :: [Edit a]}

-- | Given a single partial solution, produce a priority queue of all possible solutions.
step :: (Eq a, Show a) => Partial a -> PQueue Branching (Sum Int) (Partial a)
step (Partial xl yl [] goal edits) = withCost (Sum yl') (pure $ Partial xl (yl+yl') [] [] $ reverse (Insert <$> goal) <> edits)
   where yl' = length goal
step (Partial xl yl origin [] edits) = withCost (Sum xl') (pure $ Partial (xl+xl') yl [] [] $ reverse (Delete <$> origin) <> edits)
   where xl' = length origin
step (Partial xl yl (x:xs) (y:ys)  edits)
   | x == y = pure (Partial (xl+1) (yl+1) xs ys $ Keep x : edits)
   | otherwise = {-# SCC "step.hard" #-}
                 withCost 1 (pure (Partial (xl+1) yl xs (y:ys) $ Delete x : edits)
                             <|> pure (Partial xl (yl+1) (x:xs) ys $ Insert y : edits)
                             <|> pure (Partial (xl+1) (yl+1) xs ys $ Replace x y : edits))

-- | Repeatedly 'step' through the two strings and 'optimize' after every step, collect all relevant solutions, and
-- then extract the best one (i.e., the solution with the least cost).
stepped :: (Eq a, Show a) => [a] -> [a] -> [Edit a]
stepped xs ys = reverse (delta $ getFirst $ option undefined id $ foldMap (Option . Just . First)
                         $ applyN (length xs + length ys) (optimize . (>>= step)) (pure $ Partial 0 0 xs ys []))

-- | Optimize the queue by removing every partial solution that can be proven to be no better than another existing
-- solution. The task is performed by 'pruneSubsets', which requires a function, 'unionDiff', that compares two
-- partial solutions.
optimize = pruneSubsets unionDiff mempty

-- | A partial Levenshtein distance solution that has edited the first x items from the original string into the first
-- y items of the target string cannot be any worse than any alternative partial solution that has edited x−n original
-- items into y−n target items.
-- 
-- The first argument is a map from @length x - length y@ into the longest @length x@ consumed by the solutions
-- examined so far. Any 'Partial' solution worse than that will be eliminated.
unionDiff :: IntMap.IntMap Int -> Partial a -> Maybe (IntMap.IntMap Int, Partial a)
unionDiff state p@Partial{xlen= xl, ylen= yl}
   | Just reach <- IntMap.lookup distance state, reach >= xl = Nothing
   | otherwise = Just (IntMap.insert distance xl state, p)
   where distance = xl - yl

main = do args <- getArgs
          solution <- case args of
             -- character-based distance of two command-line arguments
             ["-c", xs, ys] -> pure (fmap (:[]) <$> stepped xs ys)
             -- line-based distance of two command-line arguments
             ["-l", xs, ys] -> pure (stepped (lines xs) (lines ys))
             -- line-based distance of two named files' contents
             ["-f", xf, yf] -> stepped <$> (lines <$> readFile xf) <*> (lines <$> readFile yf)
             _ -> error "Expecting -[clf] and two more arguments to diff."
          if head args == "-f"
             then mapM_ (putStrLn . toDiff) solution
             else print solution
          print (totalCost solution)

-- | Convert the edits into diff-like output.
toDiff (Keep line) = "  " <> line
toDiff (Delete line) = "< " <> line
toDiff (Insert line) = "> " <> line
toDiff (Replace old new) = "< " <> old <> "\n> " <> new

-- | Apply a function N times.
applyN :: Int -> (a -> a) -> a -> a
applyN n f x
   | n > 0 = applyN (pred n) f (f x)
   | otherwise = x
