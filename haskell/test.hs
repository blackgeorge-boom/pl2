import Test.QuickCheck
import Control.Monad

data Tree = Leaf Int | Branch Tree Tree deriving Show

instance Arbitrary Tree where
  arbitrary = sized tree'
    where tree' 0 = liftM Leaf arbitrary
	  tree' n | n>0 = 
		oneof [liftM Leaf arbitrary,
	          liftM2 Branch subtree subtree]
  	    where subtree = tree' (n `div` 2)

sizeTree :: Tree -> Int
sizeTree (Leaf _) = 1
sizeTree (Branch l r) = (sizeTree l) + (sizeTree r)

prop_1 t = sizeTree t > 0
	where types = t :: Tree
