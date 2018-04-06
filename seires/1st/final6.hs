{-# OPTIONS_GHC -O2 -optc-O2 #-}

import Data.Char (isSpace)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC

main = 
  do all <- BS.getContents
     let Just (n, r1) = readInt all
     let Just (m, r2) = readInt r1
     let (x, _)  = readMany readInt r2
     print (amp (x) (m) 0 0)
  where readInt s = BSC.readInt (BSC.dropWhile isSpace s)
        readInteger s = BSC.readInteger (BSC.dropWhile isSpace s)
        readMany readf s = case readf s of
          Just (x, r) -> let (xs, t) = readMany readf r
                         in  (x : xs, t)
          Nothing     -> ([], s)

amp []  _ _ _= 0
amp [a] m curr_max _ = div (curr_max - a) m 
amp [a,b] m curr_max maxim =
                            if a == b then amp [b] m (max a curr_max) (max a maxim)
                            else
                                if a < b then 
                                        let x = div (b - a) m
                                            y = amp [b] m (max b (max a curr_max)) (max b (max a maxim))
                                        in
                                            --if (b == curr_max) then y
                                            if (mod (b - a) m) == 0 then x + y else x + y + 1
                                else
                                        if (mod (a - b) m) == 0
                                          then  amp [b] m (max a curr_max) (max a maxim)
                                          else  (amp [b + 1] m (max a curr_max) (max a maxim)) + 1
amp (a : b : c : xs) m curr_max maxim = 
                                if (a == c && a > b) then amp (b : c : xs) m (max a curr_max) (max a maxim)
                                else
                                  if a == b then amp (b : c : xs) m curr_max (max a maxim)
                                  else
                                      if a < b then 
                                              let x = div (b - a) m
                                                  y = amp (b : c : xs) m curr_max (max b (max a maxim))
                                              in
                                                  --if (b == curr_max) then y
                                                  if (mod (b - a) m) == 0 then x + y else x + y + 1
                                      else
                                              if (mod (a - b) m) == 0
                                                then  amp (b : c : xs) m (max a curr_max) (max a maxim)
                                                else  (amp ((b + 1) : c : xs) m (max a curr_max) (max a maxim)) + 1
                                                  







