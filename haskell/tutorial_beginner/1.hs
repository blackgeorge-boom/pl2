x :: Int
x = 4

y :: Int
y = y + 1


-- Machine-sized integers
biggestInt, smallestInt :: Int
biggestInt = maxBound
smallestInt = minBound

reallyBig :: Integer
reallyBig = 2^(2^(2^(2^2)))

numDigits :: Int
numDigits = length (show reallyBig)

googol :: Integer
googol = 10 ^ 100

-- Danger
googolPlex :: Integer
googolPlex = 10 ^ googol

-- Double (of Float for single precision
d1, d2 :: Double
d1 = 3.14
d2 = 3.5e-4

b1, b2 :: Bool
b1 = True
b2 = False

-- String (there is also Char)
s :: String
s = "Hello world"

sumtorial :: Integer -> Integer
sumtorial 0 = 0
sumtorial n = n + sumtorial (n - 1)

hailstone :: Integer -> Integer
hailstone n
	| n `mod` 2 == 0	= n `div` 2
	| otherwise 		= 3 * n + 1

foo :: Integer -> Integer
foo 0 = 16
foo 1  
	| "Haskell" > "C++" = 3
	| otherwise 		= 4
foo n 
	| n < 0 = 0
	| n `mod` 30 == 2 = 33
	| otherwise 		= 3

sumPair :: (Int, Int) -> Int
sumPair (x, y) = x + y

nums, range, range2 :: [Int]
nums = [1, 2, 3, 4]
range = [1 .. 100]
range2 = [2, 4 .. 100 ]

hailSeq :: Integer -> [Integer]
hailSeq 1 = [1]
hailSeq n = n : hailSeq (hailstone n)

intListLength :: [Integer] -> Integer
intListLength [] = 0
intListLength (x : xs) = 1 + intListLength xs

sumEveryTwo :: [Integer] -> [Integer]
sumEveryTwo [] = []
sumEveryTwo (x : []) = [x]
sumEveryTwo (x : (y : zs)) = (x + y) : sumEveryTwo zs
