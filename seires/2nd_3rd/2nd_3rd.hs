-- Nikos Mavrogeorgis 03113087

import Test.QuickCheck
import Control.Monad  
import Data.Ratio

-- | A polymorphic n-ary tree data structure.

data Tree a = T a [Tree a]
  deriving Show

-- 2nd Exercise
--  1.
foldTree :: (a -> [b] -> b) -> Tree a -> b
foldTree f t = aux f t
  where aux f (T x ts) = f x bs
          where bs = auxs f ts
        auxs f [] = []
        auxs f (t : ts) = b : bs
          where b  = aux f t 
                bs = auxs f ts

--  2.

sizeTree :: Num b => Tree a -> b
sizeTree t = foldTree (\a bs -> 1 + sum bs) t

heightTree :: (Ord b, Num b) => Tree a -> b
heightTree t = foldTree f t 
  where f x [] = 1
        f x bs = 1 + maximum bs

sumTree :: Num a => Tree a -> a 
sumTree t = foldTree (\a bs -> a + sum bs) t

maxTree :: Ord a => Tree a -> a 
maxTree t = foldTree f t
  where f a [] = a 
        f a bs = max a (maximum bs)

inTree :: Eq a => a -> Tree a -> Bool
inTree x t = foldTree f t 
  where f a [] = (a == x)
        f a bs = (a == x) || (foldr (||) False bs)

nodes :: Tree a -> [a]
nodes t = foldTree (\a bs -> a : (concat bs)) t

countTree :: (a -> Bool) -> Tree a -> Integer
countTree f t = foldTree aux t
  where aux a [] = if f a then 1 else 0
        aux a bs = if f a then 1 + sum bs else sum bs

leaves :: Tree a -> [a]
leaves t = foldTree f t 
  where f a [] = [a]
        f a bs = concat bs 

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f t = foldTree (\a bs -> T (f a) bs) t

--  3.

trimTree :: Int -> Tree a -> Tree a
trimTree limit t 
        | limit <= 1 = error "It should be n > 1, because height is positive, and you also cannot trim the root of a tree!"
        | otherwise  = fst (aux 1 t)
                        where aux n (T x ts) = (T x ts', n')
                                where (ts', n') = auxs (n+1) ts
                              auxs n [] = ([], n)
                              auxs n (t : ts) = if n >= limit 
                                                  then ([], n)
                                                  else (t' : ts', n'')
                                                          where (t', n')   = aux n t
                                                                (ts', n'') = auxs n ts
                  
path :: [Int] -> Tree a -> a
path [] (T x ts) = x
path (b : bs) t = path bs (findKid b t) --findKind finds the b-th tree child in the list, or gives an error
  where findKid n (T x [])       = error "Cannot find path!"
        findKid 0 (T x (t : ts)) = t
        findKid n (T x (t : ts)) = findKid (n - 1) (T x ts)                
                  
-- 3rd Exercise

--  1.

-- Failed attempt

--instance (Arbitrary a) => Arbitrary (Tree a) where
--  arbitrary = sized tree'
--    where tree' 0 = liftM (\x -> T x []) arbitrary
--          tree' n | n > 0 = oneof [liftM (\x -> T x []) arbitrary, liftM2 T arbitrary arbitrary]
--                             where arb2 = vector (n `div` 2) (tree' (n `div` 2))

-- The following instance is taken from : 
-- https://stackoverflow.com/questions/15959357/quickcheck-arbitrary-instances-of-nested-data-structures-that-generate-balanced

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized arbTree

arbTree :: Arbitrary a => Int -> Gen (Tree a)
arbTree 0 = do
    a <- arbitrary
    return $ T a []
arbTree n = do
    (Positive m) <- arbitrary
    let n' = n `div` (m + 1)
    f <- replicateM m (arbTree n')
    a <- arbitrary
    return $ T a f

--  2.

prop_1 t = (heightTree t > 0) ==> 
              --collect (heightTree t)$
              --collect (sizeTree t)$
              heightTree t <= sizeTree t
  where types = t :: (Tree Int)

prop_2 t = inTree (maxTree t) t
   where types = t :: (Tree Int)

prop_3 t = foldr (\a b -> (inTree a t) && b) True (nodes t)
   where types = t :: (Tree Int)

-- A simple function needed for prop_4
g :: Int -> Bool
g x = if (x `mod` 2 == 0) then True else False

prop_4 t = ((countTree g t) >= 0) ==> (countTree g t) <= sizeTree t
   where types = t :: (Tree Int)

prop_5 t = (length (nodes t) == sizeTree t) ==>
                        classify (length (leaves t) < sizeTree t)  "Leaves fewer than nodes in a tree, if nodes > 1"$
                        classify (length (leaves t) == sizeTree t) "Leaves equal to nodes in a tree, if nodes == 1"$
                        length (leaves t) <= sizeTree t
   where types = t :: (Tree Int)

-- A simple function needed for prop_6 and prop_8
f :: Int -> Int
f x = x + 1

prop_6 t = (sizeTree (mapTree f t) == sizeTree t) ==>
            --collect (sizeTree t)$
            (heightTree (mapTree f t)) == heightTree t
   where types = t :: (Tree Int)

prop_7 n t = (inTree n t) ==>
            --collect (n)$
            --collect (sizeTree t)$
            inTree (f n) (mapTree f t)
   where types = (n :: Int, t :: (Tree Int))

prop_8 t = (map f (nodes t) == nodes (mapTree f t)) ==>
           (map f (leaves t) == leaves (mapTree f t))
   where types = t :: (Tree Int)


--  3.

bird :: Tree Rational
bird = T 1 [mapTree recipr (mapTree inc bird), mapTree inc (mapTree recipr bird)]
    where inc x = x + 1
          recipr x = 1 / x



--  4.

isBinList :: [Int] -> Bool
isBinList list = foldr (\a b -> (a == 0 || a == 1) && b) True list

-- In a binary tree like Bird Tree, the input list for path, should be a list of binary digits (0 for left subtree and 1 for right subtree).
prop_9 n p = (isBinList p && n > 1 && n > (length p) + 1) ==>
              --collect (length p)$
              path p bird == path p (trimTree n bird)
  where types = (n :: Int, p :: [Int])



-- This function returns an Int list with every node of a path in a Rational Tree. The path to follow is also given as a list.
path2 :: [Int] -> Tree Rational -> [Int]
path2 [] (T x ts) = [ceiling x]
path2 (b : bs) (T x ts) = (ceiling x) : (path2 bs (findKid b (T x ts))) --findKind finds the b-th tree child in the list, or gives an error
  where findKid n (T x [])       = error "Cannot find path!"
        findKid 0 (T x (t : ts)) = t
        findKid n (T x (t : ts)) = findKid (n - 1) (T x ts)  

--The path2 function returns n + 1 numbers, for input == n, so we compare it with the first n + 1 natural numbers.
prop_10 n = (n >=0) ==>
            --collect (n)$
            (path2 (take n (cycle [1, 0])) bird) == [1 .. (n + 1)]
  where types = n :: Int



-- Infinite list of Fibonacci numbers
-- https://stackoverflow.com/questions/1105765/generating-fibonacci-numbers-in-haskell
fibs :: [Integer]
fibs = 1 : 1 : zipWith (+) fibs (tail fibs)

-- This function returns an Integer list with the denominator of every node of a path in a Rational Tree.
-- The path to follow is also given as a list.
path3 :: [Integer] -> Tree Rational -> [Integer]
path3 [] (T x ts) = [denominator x]
path3 (b : bs) (T x ts) = (denominator x) : (path3 bs (findKid b (T x ts))) --findKind finds the b-th tree child in the list, or gives an error
  where findKid n (T x [])       = error "Cannot find path!"
        findKid 0 (T x (t : ts)) = t
        findKid n (T x (t : ts)) = findKid (n - 1) (T x ts) 

--The bird tree Fibonacci series is missing the first '1'. So we drop the first element of fibs and check one number further,
--to compare the two lists. Also, the path3 funcion returns n + 1 numbers, for input == n, so we compare it with the first n + 1 Fibonacci
--numbers. The above two statements explain the following (n + 2) operand.
prop_11 n = (n >= 0) ==>
            --collect (n)$
            (path3 (take n (cycle [0])) bird) == drop 1 (take (n + 2) fibs)
  where types = n :: Int




-- No prop_12

