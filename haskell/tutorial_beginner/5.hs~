class Listable a where
	toList :: a -> [Int]

instance Listable Int where
	toList x = [x]

instance Listable Bool where
	toList True  = [1]
	toList False = [0]

data Tre a = Empty | Node a (Tre a) (Tre a)

--instance Listable (Tre Int) where
--toList Empty        = []
--toList (Node x l r) = toList l ++ [x] ++ toList r

