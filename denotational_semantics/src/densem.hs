-- ------------------------------------------------------------------------------
-- Nikos Mavrogeorgis 03113087
-- GHCi, version 7.10.3
-- TODO : Usage
-- ------------------------------------------------------------------------------


--
-- Syntax
-- We present WHILE++ syntax in exact correspondence with the assignment's presentation.
-- 

type Var = String

data C = Cskip | N | Cseq C C | Cif B C C | Cfor N C | Cwhile B C
  deriving (Show)

data N = Nzero | Nsucc N | Npred N | Nvar Var | Nassign Var N | Npp Var | Nmm Var
  deriving (Show)

data B = Btrue | Bfalse | Blt N N | Beq N N | Bnot B
  deriving (Show)

-- Semantic domains

type S = Var -> Integer

--
-- Semantic functions
-- 

-- Commands

semC :: C -> S -> (S, Integer)
semC Cskip s = (s, -1)
semC (Cseq c1 c2) s = semC c2 (fst (semC c1 s))
semC (Cif b c1 c2) s | semB b s  = semC c1 s
                     | otherwise = semC c2 s
semC (Cfor n c) s = expon i (semC c) (s, 0)
  where i = snd (semN n s)
semC (Cwhile b c) s = fix bigF s
  where bigF f s | semB b s  = f (fst (semC c s))
                 | otherwise = (s, 0)

-- Numbers

semN :: N -> S -> (S, Integer)
semN Nzero s = (s,0)
semN (Nsucc n) s = (s, value + 1)
	where value = snd (semN n s)
semN (Npred n) s = (s, value - 1)
	where value = snd (semN n s)
semN (Nvar x) s = (s, s x)
semN (Nassign x n) s = (update s x value, value)
	where value = snd (semN n s)
semN (Npp x) s = (update s x n, n)
	where n = snd (semN (Nvar x) s) + 1 
semN (Nmm x) s = (update s x n, n)
	where n = snd (semN (Nvar x) s) - 1 

-- Booleans

semB :: B -> S -> Bool
semB Btrue s = True
semB Bfalse s = False
semB (Blt n1 n2) s = snd (semN n1 s) < snd (semN n2 s)
semB (Beq n1 n2) s = snd (semN n1 s) == snd (semN n2 s)
semB (Bnot b) s = not (semB b s)

-- auxiliary functions

expon 0 f = id
expon n f = f . fst . expon (n-1) f

update s x n y | x == y    = n
               | otherwise = s y

-- example
 
makeN 0 = Nzero
makeN n = Nsucc (makeN (n-1))

s0 x = error ("not initialized variable " ++ x)

run c = print (fst (semN c s0) "result")

ex0 = Nassign "result" (makeN 42)

fix f = f (fix f)
