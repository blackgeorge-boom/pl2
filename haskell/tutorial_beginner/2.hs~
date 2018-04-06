data Thing = Shoe | Ship | Cabbage | Pencil deriving Show

shoe :: Thing
shoe = Shoe

isSmall :: Thing -> Bool
isSmall Shoe = True
isSmall Ship = False
isSmall Cabbage = True

data FailableDouble = Failure | OK Double deriving Show

safeDiv :: Double -> Double -> FailableDouble
safeDiv _ 0 = Failure
safeDiv x y = OK (x / y)

data Person = Person String Int String deriving Show

stan :: Person
stan = Person "Stan" 33 "Malakas"

getAge :: Person -> Int
getAge (Person _ x _) = x

ex01 = case "Hello" of
		[]	->	3
		('H' : s) -> length s
		_		-> 5

data List = Empty | Cons Int List deriving Show

x :: List
x = Cons 3 Empty

listProd :: List -> Int
listProd Empty = 1
listProd (Cons x xs) = x * listProd xs
