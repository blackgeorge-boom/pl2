import Test.QuickCheck
import Control.Monad  
import Data.Ratio

-- | A polymorphic n-ary tree data structure.

data Tree a = T a [Tree a]
  deriving Show

-- | Function that annotates each node of a tree with the order in which
-- | a DFS traversal would visit it.

dfn :: Tree a -> Tree (a, Int)
dfn t = fst (aux t 1)
    where aux (T x ts) n = (T (x, n) ts', n')
            where (ts', n') = auxs ts (n + 1)
          auxs [] n = ([], n)
          auxs (t : ts) n = (t' : ts', n'')
            where (t', n') = aux t n
                  (ts', n'') = auxs ts n'

t = T 'a' [ T 'b' []
          , T 'c' [ T 'e' []    
                  , T 'f' []
                  ]
          , T 'd' []
          ]