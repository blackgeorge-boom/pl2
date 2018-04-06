
--amp :: [Integer] -> Integer -> Integer
amp []  _ _  = 0
amp [a] m curr_max  =
                    let
                        x = div (curr_max - a) m 
                    in
                        if curr_max > a 
                            then if mod (curr_max - a) m == 0 then x else x + 1
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

        