greaterThan100 :: [Int] -> [Int]
greaterThan100 l = filter (\x -> x > 100) l

strange :: (b -> c) -> (a -> b) -> (a -> c)
strange f g = \x -> f (g x)

comp :: (b -> c) -> (a -> b) -> (a -> c)
comp f g x = f (g x)

ex :: [Int] -> Int
ex = sum . map (\x -> 7 * x + 2) . filter (> 3)

myFold :: b -> (a -> b -> b) -> [a] -> b
myFold z f [] = z
myFold z f (x : xs) = f x (myFold z f xs)
