newtype Eventually a = NotYet (Eventually a -> a)

sa :: Eventually a -> a
sa eventually@(NotYet f) = f eventually

inc :: Int -> Int
inc x = x + 1