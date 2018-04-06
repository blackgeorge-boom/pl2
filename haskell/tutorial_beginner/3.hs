data List = Empty | Cons Int List deriving Show

x :: List
x = Cons 3 Empty

mapList :: (Int -> Int) -> List -> List 
mapList _ Empty = Empty
mapList f (Cons x xs) = Cons (f x) (mapList f xs)

keepOnlyEven :: List -> List
keepOnlyEven Empty = Empty
keepOnlyEven (Cons x xs) 
	| even x  = Cons x (keepOnlyEven xs)
    | otherwise = keepOnlyEven xs

data L t = E | C t (L t) deriving Show

l1 :: L Int
l1 = C 3 E

l2 :: L Char
l2 =  C 's' (C 'f' E)

filterList :: (t -> Bool) -> (L t) -> (L t)
filterList _ E = E
filterList p (C x xs) 
	| p x = C x (filterList p xs)
	| otherwise = filterList p xs
