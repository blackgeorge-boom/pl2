import Test.QuickCheck

qsort :: [Int] -> [Int]
qsort [] = []
qsort (pivot : xs) = qsort [x | x <- xs, x < pivot] ++
                     [pivot] ++
                     qsort [x | x <- xs, x >= pivot]

isSorted (x : xs@(y : _)) = x <= y && isSorted xs
isSorted _ = True

prop_same_length :: [Int] -> Bool
prop_same_length l = length l == length (qsort l)

prop_is_sorted :: [Int] -> Bool
prop_is_sorted l = isSorted (qsort l)

main = do
  -- Using explicit generators:
  putStrLn "testing for length"
  quickCheck $ forAll (listOf (choose (0, 1000))) $ \l ->
    length l == length (qsort l)
  putStrLn "testing for sorted"
  quickCheck $ forAll (listOf (choose (0, 1000))) $ \l ->
    isSorted (qsort l)
  -- Using type-annotated property functions:
  putStrLn "or equivalently..."
  quickCheck prop_same_length
  quickCheck prop_is_sorted
