-- ./Levenshtein "$(cat ../web/regression/test/blocks/input/input.xml)" "$(cat ../web/regression/test/blocks/output/input.xml)"
{-# Language DeriveFunctor #-}

import Control.Applicative
import Data.Monoid (Sum(..))
import Data.Semigroup (First(..), Option(Option, getOption), option)
import System.Environment (getArgs)
import qualified Data.IntMap.Strict as IntMap

import Data.PriorityQueue

import Debug.Trace

data Edit a = Keep !a
            | Delete !a
            | Insert !a
            | Replace !a !a
            deriving (Eq, Show, Functor)

totalCost :: [Edit a] -> Int
totalCost = getSum . foldMap cost

cost :: Edit a -> Sum Int
cost Keep{} = Sum 0
cost _ = Sum 1

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

prioritized :: Eq a => [a] -> [a] -> [Edit a]
prioritized xs ys = reverse (getFirst $ option undefined id $ foldMap (Option . Just . First) $ prune $ prioritize xs ys [])

prioritize :: Eq a => [a] -> [a] -> [Edit a] -> PQueue Branching (Sum Int) [Edit a]
prioritize [] goal edits = weigh1pure (Sum $ length goal) (reverse (Insert <$> goal) <> edits)
prioritize origin [] edits = weigh1pure (Sum $ length origin) (reverse (Delete <$> origin) <> edits)
prioritize (x:xs) (y:ys) edits
   | x == y = prioritize xs ys (Keep x : edits)
   | otherwise =  (weigh1pure 1 (Delete x : edits) >>= prioritize xs (y:ys))
              <|> (weigh1pure 1 (Insert y : edits) >>= prioritize (x:xs) ys)
              <|> (weigh1pure 1 (Replace x y : edits) >>= prioritize xs ys)

data Partial a = Partial {
   xlen, ylen :: !Int,
   xrest, yrest :: [a],
   delta :: [Edit a]}

derived :: (Eq a, Show a) => [a] -> [a] -> [Edit a]
derived xs ys = reverse (delta $ getFirst $ option undefined id $ foldMap (Option . Just . First)
                         $ prune $ derive (Partial 0 0 xs ys []))

derive :: (Eq a, Show a) => Partial a -> PQueue Branching (Sum Int) (Partial a)
derive (Partial xl yl [] goal edits) = weigh1pure (Sum yl') (Partial xl (yl+yl') [] [] $ reverse (Insert <$> goal) <> edits)
   where yl' = length goal
derive (Partial xl yl origin [] edits) = weigh1pure (Sum xl') (Partial (xl+xl') yl [] [] $ reverse (Delete <$> origin) <> edits)
   where xl' = length origin
derive (Partial xl yl (x:xs) (y:ys)  edits)
   | x == y = derive (Partial (xl+1) (yl+1) xs ys $ Keep x : edits)
   | otherwise = {-# SCC "derive.hard" #-}
                 optimize (weigh1 1 (pure (Partial (xl+1) yl xs (y:ys) $ Delete x : edits)
                                     <|> pure (Partial xl (yl+1) (x:xs) ys $ Insert y : edits)
                                     <|> pure (Partial (xl+1) (yl+1) xs ys $ Replace x y : edits))
                           >>= derive)

step :: (Eq a, Show a) => Partial a -> PQueue Branching (Sum Int) (Partial a)
step (Partial xl yl [] goal edits) = weigh1pure (Sum yl') (Partial xl (yl+yl') [] [] $ reverse (Insert <$> goal) <> edits)
   where yl' = length goal
step (Partial xl yl origin [] edits) = weigh1pure (Sum xl') (Partial (xl+xl') yl [] [] $ reverse (Delete <$> origin) <> edits)
   where xl' = length origin
step (Partial xl yl (x:xs) (y:ys)  edits)
   | x == y = pure (Partial (xl+1) (yl+1) xs ys $ Keep x : edits)
   | otherwise = {-# SCC "step.hard" #-}
                 weigh1 1 (pure (Partial (xl+1) yl xs (y:ys) $ Delete x : edits)
                           <|> pure (Partial xl (yl+1) (x:xs) ys $ Insert y : edits)
                           <|> pure (Partial (xl+1) (yl+1) xs ys $ Replace x y : edits))

stepped :: (Eq a, Show a) => [a] -> [a] -> [Edit a]
stepped xs ys = reverse (delta $ getFirst $ option undefined id $ foldMap (Option . Just . First)
                         $ prune $ applyN (length xs + length ys) (optimize . (>>= step)) (pure $ Partial 0 0 xs ys []))

optimize = traceThruId "after" length . pruneSubsets unionDiff mempty . traceThruId "before" length
   where unionDiff state p@Partial{xlen= xl, ylen= yl}
            | Just reach <- IntMap.lookup distance state, reach >= xl = Nothing
            | otherwise = Just (IntMap.insert distance xl state, p)
            where distance = xl - yl

main = do args <- getArgs
          solution <- case args of
                 ["-c", xs, ys] -> pure (fmap (:[]) <$> stepped xs ys)
                 ["-l", xs, ys] -> pure (stepped (lines xs) (lines ys))
                 ["-f", xf, yf] -> stepped <$> (lines <$> readFile xf) <*> (lines <$> readFile yf)
                 _ -> error "Expecting -[clf] and two more arguments."
          if head args == "-f"
             then mapM_ (putStrLn . toDiff) solution
             else print solution
          print (totalCost solution)

toDiff (Keep line) = "  " <> line
toDiff (Delete line) = "< " <> line
toDiff (Insert line) = "> " <> line
toDiff (Replace old new) = "< " <> old <> "\n> " <> new

applyN :: Int -> (a -> a) -> a -> a
applyN n f x
   | n > 0 = applyN (pred n) f (f x)
   | otherwise = x

traceThruId prefix f x
   | True = x
   | otherwise = trace (prefix <> ": " <> show (f x)) x
