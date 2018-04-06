import Data.List

search :: (Eq a) => [a] -> [a] -> Bool
search _ [] = False
search needle haystack = 
    foldl 