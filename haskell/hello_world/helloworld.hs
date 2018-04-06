--helloworlds.hs
import Data.Char
import Control.Monad

main = do
    l <- getContents
    putStrLn (map toUpper l)