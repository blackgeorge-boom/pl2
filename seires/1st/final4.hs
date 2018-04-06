{-# OPTIONS_GHC -O2 -optc-O2 #-}

import Data.Char (isSpace)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC

main = 
  do all <- BS.getContents
     let Just (n, r1) = readInt all
     let Just (m, r2) = readInt r1
     let (x, _)  = readMany readInt r2
     print (amp (x) (m) 0)
  where readInt s = BSC.readInt (BSC.dropWhile isSpace s)
        readInteger s = BSC.readInteger (BSC.dropWhile isSpace s)
        readMany readf s = case readf s of
          Just (x, r) -> let (xs, t) = readMany readf r
                         in  (x : xs, t)
          Nothing     -> ([], s)

amp []  _ _ = 0
amp [a] m curr_max = div (abs (curr_max - a)) m 
amp [a,b] m curr_max =
                            if a == b then amp [b] m (max a curr_max)
                            else
                                if a < b then 
                                        let x = div (b - a) m
                                            y = amp [b] m (max b (max a curr_max))
                                        in
                                            if (mod (b - a) m) == 0 then x + y else x + y + 1
                                else
                                        let
                                            y = amp [b] m (max b (max a curr_max))
                                        in
                                            if (mod (a - b) m) == 0 then y else y + 1   
amp (a : b : c : xs) m curr_max = 
                                if (a == c && a > b) then amp (b : c : xs) m (max a curr_max)
                                else
                                  if a == b then amp (b : c : xs) m (max a curr_max)
                                  else
                                      if a < b then 
                                              let x = div (b - a) m
                                                  y = amp (b : c : xs) m (max b (max a curr_max))
                                              in
                                                  if (mod (b - a) m) == 0 then x + y else x + y + 1
                                      else
                                              let
                                                  y = amp (b : c : xs) m (max b (max a curr_max))
                                              in
                                                  if (mod (a - b) m) == 0 then y else y + 1     







