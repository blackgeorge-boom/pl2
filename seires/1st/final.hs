main :: IO ()
main = do
  all <- getContents
  let (sn : sm : rest) = words all
  let n = read sn :: Integer
  let m = read sm :: Integer
  let x = map read rest
  --print (n :: Integer)
  --print (m :: Integer)
  --print (x :: [Integer])
  print (amp (x :: [Integer]) (m :: Integer) 0)


amp []  _ _ = 0
amp [a] m curr_max = div (curr_max - a) m 
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







