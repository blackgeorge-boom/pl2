main = forever $ do 
    putStrLn "gimme"
    line <- getLine
    putStrLn $ map toUpper line

putString [] = return ()
putString (x : xs) = do
    putChar x
    putString xs