main :: IO ()
main = do
  all <- getContents
  let (sn : sm : rest) = words all
  let n = read sn :: Int
  let m = read sm :: Int
  let x = map read rest
  --print (n :: Int)
  --print (m :: Int)
  --print (x :: [Int])
  print (amp (x :: [Int]) (m :: Int) 0)


amp []  _ _ = 0
amp [a] m curr_max =
                    let
                        x = div (curr_max - a) m 
                    in
                        if curr_max > a 
                            then x
                            else 0    
amp (a : b : xs) m curr_max =
                            if a <= b then 
                                    let x = div (b - a) m
                                        y = amp (b : xs) m (max a curr_max)
                                    in
                                        if (mod (b - a) m) == 0 then x + y else x + y + 1
                            else
                                    let
                                        y = amp (b : xs) m (max a curr_max)
                                    in
                                        if (mod (a - b) m) == 0 then y else y + 1    







