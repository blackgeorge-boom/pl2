data Tree a = T a [Tree a] deriving Show

dfs :: Tree a -> Tree (a, Int)
dfs (T a list) = aux (T a list) 1
aux (T a []) n = (a, n)
aux (T a (x : xs)) n = (a, n) : (aux (T x) n + 1 : (aux (T xs) n + 2))