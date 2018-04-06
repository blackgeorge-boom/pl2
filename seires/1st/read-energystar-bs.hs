o{- (Comments are in Greek, iso8859-7)
 -
 - ÃñÜøôå ìßá "óõíÜñôçóç" ðïõ íá äéáâÜæåé ôá äåäïìÝíá åéóüäïõ ãéá
 - ôçí Üóêçóç "Êé Üëëç Haskell ãéá åíåñãåéáêïýò" êáé íá ôá åìöáíßæåé
 - óôçí ïèüíç.
 - 
 - ÁõôÞ ç Ýêäïóç ÷ñçóéìïðïéåß ôç âéâëéïèÞêç ôùí byte strings ôïõ GHC.
 -}

{-# OPTIONS_GHC -O2 -optc-O2 #-}

import Char (isSpace)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC

main = 
  do all <- BS.getContents
     let Just (n, r1) = readInt all
     let Just (l, r2) = readInt r1
     let Just (b, r3) = readInteger r2
     let (x, _)  = readMany readInt r3
     print (n :: Int)
     print (l :: Int)
     print (b :: Integer)
     print (x :: [Int])
  where readInt s = BSC.readInt (BSC.dropWhile isSpace s)
        readInteger s = BSC.readInteger (BSC.dropWhile isSpace s)
        readMany readf s = case readf s of
          Just (x, r) -> let (xs, t) = readMany readf r
                         in  (x : xs, t)
          Nothing     -> ([], s)
