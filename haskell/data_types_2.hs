data Shape = Circle Float Float Float | Rectangle Float Float Float Float deriving Show

surface :: Shape -> Float
surface (Circle _ _ r) = 3.14 * r ^ 2
surface (Rectangle x1 y1 x2 y2) = abs(x2 - x1) * abs(y2 - y1)