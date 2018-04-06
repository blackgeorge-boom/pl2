--File: qsort.hs

qsort [] = []
qsort (p : xs) = 
    qsort [x | x <- xs, x < p] ++
    [p] ++
    qsort [x | x <- xs, x >= p]

qsort2 [] = []
qsort2 (p : xs) = qsort2 lt ++ [p] ++ qsort2 ge
    where   lt = [x | x <- xs, x < p]
            ge = [x | x <- xs, x >= p]

qsort3 [] = []
qsort3 (p : xs) =  let  lt = [x | x <- xs, x < p]
                        ge = [x | x <- xs, x >= p]
                    in  qsort3 lt ++ [p] ++ qsort3 ge

len l = case l of 
            [] -> 0
            a : xs -> 1 + len xs 

tak 0 ls = []
tak n [] = []
tak n (a : xs) = a : tak (n - 1) xs

tak2 n ls =
    case (n, ls) of 
        (0, _)      -> []
        (_, [])     -> []
        (n, a : xs) -> a : tak2 (n - 1) xs


fac 0 = 1
fac n | n > 0 = n * fac (n - 1)

abs1 :: Integer -> Integer
abs1 x | x > 0 = x
      | x < 0 = -x

data Color = Green | Yellow | Red

next Green = Yellow
next Yellow = Red
next Red = Green

data Shape =    Rectangle Double Double
           |    Circle Double

area (Rectangle x y) = x * y
area (Circle r) = 3.14 * r * r

data Ext_Expr a = Const a
          | Add (Ext_Expr a) (Ext_Expr a)
          | Neg (Ext_Expr a)
          | Mult (Ext_Expr a) (Ext_Expr a)

type Int_Expr = Ext_Expr Integer
eval :: Int_Expr -> Integer
eval (Const c)  = c
eval (Add a b)  = (eval a) + (eval b)
eval (Neg a)    = - (eval a)
eval (Mult a b) = eval a * eval b

data Tree a = Empty | Node (Tree a, a, Tree a)

depth Empty = 0
depth (Node (left, _, right)) = (depth left) + 1 + (depth right)

type Name = String 
data OptAdress = None | Addr String
type Person = (Name, OptAdress)

my_map :: (a -> b) -> [a] -> [b]
my_map f [] = []
my_map f (a : xs) = f a : map f xs

nums = [17, 42, 54]
inc x = x + 1

inc42 = \x -> x + 42
add = \x y -> x + y 

add2 x y = x `add` y 
add3 x y = (+) x y 

[] @@ ys = ys
(x : xs) @@ ys = x : (xs @@ ys)


-- finds all pythagorian triples up to n
pythag :: Int -> [(Int, Int, Int)]
pythag n =
  [(x, y, z) | x <- [1..n], y <- [x..n], z <- [1..n],
              z ^ 2 == x ^ 2 + y ^ 2]

my_zip [] ys = []
my_zip xs [] = [] 
my_zip (x : xs) (y : ys) = (x, y) : my_zip xs ys 

my_foldr op init [] = init
my_foldr op init (x : xs) = x `op` (my_foldr op init xs)

my_sum = my_foldr (+) 0 
my_prod = my_foldr (*) 1

my_and = my_foldr (&&) True 
my_concat = my_foldr (++) []

rev = my_foldr (\x y -> y ++ [x]) [] 

maxim (x : xs) = my_foldr max x xs

pos_sum [] _ _= 0
pos_sum (a : xs) k n = if (k > 0) then (a * k + (pos_sum xs (k + 1) n)) else (a * (n + k) + (pos_sum xs (k + 1) n))


--max_shift ls n 0 cur_max = cur_max
--max_shift ls n counter cur_max = max (pos_sum) 

data Student =  Student Name2 Score
type Name2 = String
type Score = Integer

better (Student x y ) (Student w z) = y > z

a = 6

doh a = b where b = a * 2

booms xs = [if x < 10 then "boom" else "bang" | x <- xs, mod x 2 ==  1]

length' xs = sum [1 | _ <- xs]

removeNonUpperCase st = [x | x <- st, x >= 'A', x <= 'Z']

removeNonUppercase2 st = [ c | c <- st, c `elem` ['A'..'Z']]

remove_odds list = [[x | x <- xs, even x] | xs <- list]

addVectors a b = (fst a + fst b, snd a + snd b) 

addVectors2 (a1, b1) (a2, b2) = (a1 + a2, b1 + b2)

add_pairs list = [a + b | (a, b) <- list]

max' a b 
  | a > b = a
  | otherwise = b

calcBmis list = [bmi w h | (w, h) <- list]
  where bmi weight height = weight / height ^ 2

calcBmis2 list = [let bmi weight height = weight / height ^ 2 in bmi w h | (w, h) <- list]

calcBmis3 xs = [bmi | (w, h) <- xs, let bmi = w / h ^ 2] 

cylinder r h = 
  let sideArea = 2 * pi * r * h
      topArea  = 2 * pi * r ^ 2
  in sideArea + topArea

describe_list l = "This list is " ++ case l of  []    -> "empty"
                                                [a]   -> "single element"
                                                _ : _ -> "multiple elements"

maxim2 [] = error "empty list"
maxim2 [a] = a
maxim2 (a : xs) = max a (maxim xs)

replica :: (Num i, Ord i) => i -> a -> [a] 
replica 0 _ = []
replica n x = x : (replica (n - 1) x)

take' _ [] = []
take' n _ 
    | n <= 0 = []
take' n (a : xs) = a : take' (n - 1) xs 

repeat' x = x : repeat' x

divideByTen = (/10)

isUpper = (`elem` ['A' .. 'Z'])

applyTwice f x = f (f x)  

zipWith' _ left [] = []
zipWith' _ [] right = []
zipWith' f (a : xs) (b : ys) = f a b : zipWith f xs ys

flip' f = g  
    where g x y = f y x 

flip'' f x y = f y x

isUpper2 = flip elem ['A' .. 'Z']

filter' _ [] = []
filter' f (a : xs) 
      | f a       = a : filter' f xs
      | otherwise = filter' f xs

--maximum (filter (\x -> x `mod` 3829 == 0) [1..1000000])
--head (filter (\x -> x `mod` 3829 == 0) [1000000, 999999 ..])

oddSquaresBefore n = takeWhile (< n) (filter odd (map (^ 2) [1 ..]))

--sum (takeWhile (<10000000) (filter odd (map (^2) [1..])))
--sum (takeWhile (<10000000) [n^2 | n <- [1..], odd (n^2)])  

chain n 
  | n == 1 = [1]
  | odd n  = n : chain (3 * n + 1)
  | even n = n : chain (div n 2)

--length (filter (> 15) [length (chain x) | x <- [1 .. 100]])

element' x list = foldl (\a b -> if b == x then True else a) False list

maximum' list = foldl max (head list) list

reverse' = foldl (\acc x -> x : acc) [] 

--length (takeWhile (< 1000) (scanl (+) 0 (map sqrt [1 ..])))