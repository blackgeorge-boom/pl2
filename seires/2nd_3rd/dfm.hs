import Control.Monad

-- | State monad, where the state is an integer number.

data State a = S (Int -> (a, Int))

instance Monad State where
  return x = S (\n -> (x, n))
  S f >>= g = S (\n -> let (x, n') = f n
                           S h = g x
                       in  h n')

get :: State Int
get = S (\n -> (n, n))

set :: Int -> State ()
set k = S (\n -> ((), k))

run :: Int -> State a -> a
run n (S f) = fst (f n)

-- | A polymorphic n-ary tree data structure.

data Tree a = T a [Tree a]
  deriving Show

-- | Function that annotates each node of a tree with the order in which
-- | a DFS traversal would visit it.
dfn :: Tree a -> Tree (a, Int)
dfn t = run 1 (aux t)
  where aux (T x ts) = do n <- get
                          set (n+1)
                          ts' <- auxs ts
                          return (T (x, n) ts')
        auxs [] = return []
        auxs (t : ts) = do t' <- aux t
                           ts' <- auxs ts
                           return (t' : ts')

-- | Example

t = T 'a' [ T 'b' []
          , T 'c' [ T 'e' []
                  , T 'f' []
                  ]
          , T 'd' []
          ]

main = print (dfn t)

-- | Boilerplate code to make 'State' a legal monad.

instance Functor State where
  fmap = liftM

instance Applicative State where
  pure  = return
  (<*>) = ap
