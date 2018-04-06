import Test.QuickCheck
data TrafficLight = Red | Yellow | Green 

instance Eq TrafficLight where
    Red == Red = True
    Yellow == Yellow = True
    Green == Green = True
    _ == _ = False

instance Show TrafficLight where
    show Red = "Red"
    show Green = "Green"
    show Yellow = "Yellow"

class YesNo a where
    yesno :: a -> Bool

instance YesNo Int where
    yesno 0 = False
    yesno _ = True

instance YesNo [a] where 
    yesno [] = False
    yesno _  = True

instance YesNo (Maybe a) where
    yesno (Just a) = True
    yesno Nothing  = False

yesnoIf :: (YesNo cond) => cond -> a -> a -> a
yesnoIf cond s1 s2 = if yesno cond then s1 else s2  

--instance Functor Maybe where
--    fmap f (Just a) = Just (f a)
--    fmap f Nothing  = Nothing

main = do line <- fmap reverse getLine
          --let line' = reverse line
          a <- getLine
          b <- getLine
          putStrLn $ "check this out " ++ line
          putStrLn $ a ++ b

--Aplicative
-- (+3) <$> [1,2,3] 
-- [(+3)] <*> [1,2,3]
--(++) <$> Just "johntra" <*> Just "volta"  

myAction = (++) <$> getLine <*> getLine  

type Birds = Int
type Pole  = (Birds, Birds)

landLeft :: Birds -> Pole -> Maybe Pole
landLeft n (left, right) 
    | n + left - right > 3  = fail "boom"
    | otherwise             = Just (left + n, right)


landRight :: Birds -> Pole -> Maybe Pole
landRight n (left, right) 
    | n + right - left > 3  = fail "boom"
    | otherwise             = Just (left, right + n)

x -: f = f x 

banana :: Pole -> Maybe Pole
banana _ = Nothing

foo :: Maybe String
foo =   Just 3 >>= (\x ->
        Just "!" >>= (\y ->
        Just (show x ++ y)))

foo2 :: Maybe String
foo2 = do
    x <- Just 3
    y <- Just "!"
    Just (show x ++ y)

walking :: Maybe Pole
walking = do
        first  <- return (0,0)
        second <- landRight 2 first
        third  <- landLeft  2 second
        landRight 2 third

oops :: Maybe Char
oops = do
    (x : xs) <- Just ""
    return x 

understand1 :: Maybe String
understand1 = Just 3 >>= (\x -> Just $ show x)

understand2 :: Maybe String
understand2 = Just 3 >>= (\x -> Just "!" >>= (\y -> Just (show x ++ y)))

understand3 = do
        a <- Just 3
        b <- Just "!"
        Just $ show a ++ b


gen :: IO String
gen = do
    x <- getLine
    return x
            