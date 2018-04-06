data Shape = Circle Point Float | Rectangle Point Point  deriving Show
data Point = Point Float Float deriving Show

surface :: Shape -> Float
surface (Circle (Point x y) z) = 2 * pi * z^2
--surface (Rectangle x y z w) = (abs (x - z)) * (abs (y - w))

data Person = Person  {firstName :: String
                      , lastName :: String
                      } deriving Show

data Maybe a = Nothing | Just a   deriving (Eq, Show)                    

 

data Vector a = Vector a a a deriving Show
vplus :: (Num t) => Vector t -> Vector t -> Vector t
vplus (Vector x1 y1 z1) (Vector x2 y2 z2) = Vector (x1 + x2)  (y1 + y2)  (z1 + z2)

data List a = Empty | Cons a (List a) deriving (Show, Read, Eq, Ord)

infixr 5 .++
(.++) :: List a -> List a -> List a
Empty .++ y = y
(Cons a b) .++ c = Cons a (b .++ c)

data Tree a = EmptyTree | Node a (Tree a) (Tree a) deriving (Show, Read, Eq)

singleton :: a -> Tree a
singleton x = Node x EmptyTree EmptyTree

treeInsert :: (Ord a) => a -> Tree a -> Tree a
treeInsert x EmptyTree = singleton x
treeInsert x (Node a l r) 
            | x == a = Node x l r
            | x > a  = Node a l (treeInsert x r)
            | x < a  = Node a (treeInsert x l) r  

treeElem :: (Ord a) => a -> Tree a -> Bool
treeElem x EmptyTree = False
treeElem x (Node a l r) 
  | x == a = True
  | x > a = False || treeElem x r
  | x < a = treeElem x l

--let nums = [1,2,3,4,5]
--let numsTree = foldr treeInsert EmptyTree nums

            