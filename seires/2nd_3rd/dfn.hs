-- | A polymorphic n-ary tree data structure.

data Tree a = T a [Tree a]
  deriving Show

-- | Function that annotates each node of a tree with the order in which
-- | a DFS traversal would visit it.

dfn :: Tree a -> Tree (a, Int)
dfn t = fst (aux 1 t)
  where aux n (T x ts) = (T (x, n) ts', n')
          where (ts', n') = auxs (n+1) ts
        auxs n [] = ([], n)
        auxs n (t : ts) = (t' : ts', n'')
          where (t', n') = aux n t
                (ts', n'') = auxs n' ts

-- | Example

t = T 'a' [ T 'b' []
          , T 'c' [ T 'e' []    
                  , T 'f' []
                  ]
          , T 'd' []
          ]

main = print (dfn t)

foldTree :: (a -> [b] -> b) -> Tree a -> b
foldTree f t = aux f t
  where aux f (T x ts) = f x bs
          where bs = auxs f ts
        auxs f [] = []
        auxs f (t : ts) = b : bs
          where b  = aux f t 
                bs = auxs f ts

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
path (b : bs) t = path bs (findKid b t)
  where findKid n (T x [])       = error "Cannot find path!"
        findKid 0 (T x (t : ts)) = t
        findKid n (T x (t : ts)) = findKid (n - 1) (T x ts)                
                  
-- | Example2

t2 = T 1 [ T 5 []
          , T 3 [ T 4 []    
                  , T 2 []
                  ]
          , T 1 []
          ]

bird :: Tree Rational
bird = T 1 [mapTree recipr (mapTree inc bird), mapTree inc (mapTree recipr bird)]
    where inc x = x + 1
          recipr x = 1 / x
--use trimTree to check