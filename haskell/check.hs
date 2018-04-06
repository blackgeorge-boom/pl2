import Test.QuickCheck
import Control.Monad

-- | A polymorphic n-ary tree data structure.

data Tree a = T a [Tree a]
  deriving Show

prop_Rev xs = reverse xs == xs
    where types = xs::[Int]

ordered xs = and (zipWith (<=) xs (drop 1 xs))
insert x xs = takeWhile (<x) xs ++ [x] ++ dropWhile (<x) xs

--Checking insert. If you insert in an ordered list, will it remain ordered?
prop_Ins x xs = (ordered xs) ==> ordered (insert x xs)
    where types = x :: Int

prop_Ins2 x = forAll orderedList $ \xs -> ordered (insert x xs)
    where types = x :: Int

--prop_Ins3 x xs = ordered xs ==> null xs `trivial` ordered (insert x xs)
--    where types = x :: Int

prop_Ins4 x xs = 
    ordered xs ==> 
        classify (ordered (x:xs)) "at-head"$
        classify (ordered (xs++[x])) "at-tail"$
        ordered (insert x xs)
  where types = x::Int

prop_Ins5 x xs =
    ordered xs ==>
        collect (length xs)$
        ordered (insert x xs)
  where types = x :: Int

prop_Assoc f g h x =
  ((f . g) . h ) x == (f . (g . h)) x
  where types = [f, g, h] :: [Int -> Int]
--needs import Text.Show.Functions


--instance (Arbitrary a) => Arbitrary (Tree a) where
--  arbitrary = sized tree'
--    where tree' 0 = liftM (\x -> T x []) arbitrary
--          tree' n | n > 0 = oneof [liftM (\x -> T x []) arbitrary, liftM2 T arbitrary arbitrary]
--                             where arb2 = vector (n `div` 2) (tree' (n `div` 2))

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

data List a = [] | a : (List a)

