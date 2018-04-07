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

data C = Cskip | Cseq C C | Cif B C C | Cfor C C | Cwhile B C | Nzero | Nsucc C | Npred C | Nvar Var | Nassign Var C | Npp Var | Nmm Var
  deriving (Show)

data B = Btrue | Bfalse | Blt C C | Beq C C | Bnot B
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
  where i = snd (semC n s)
semC (Cwhile b c) s = fix bigF s
  where bigF f s | semB b s  = f (fst (semC c s))
                 | otherwise = (s, 0)

-- Numbers

semC Nzero s = (s,0)
semC (Nsucc n) s = (s, value + 1)
	where value = snd (semC n s)
semC (Npred n) s = (s, value - 1)
	where value = snd (semC n s)
semC (Nvar x) s = (s, s x)
semC (Nassign x n) s = (update s x value, value)
	where value = snd (semC n s)
semC (Npp x) s = (update s x n, n)
	where n = snd (semC (Nvar x) s) + 1 
semC (Nmm x) s = (update s x n, n)
	where n = snd (semC (Nvar x) s) - 1 

-- Booleans

semB :: B -> S -> Bool
semB Btrue s = True
semB Bfalse s = False
semB (Blt n1 n2) s = snd (semC n1 s) < snd (semC n2 s)
semB (Beq n1 n2) s = snd (semC n1 s) == snd (semC n2 s)
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

run c = print (fst (semC c s0) "result")

ex0 = Nassign "result" (makeN 42)

ex1 = Cseq (Nassign "result" Nzero)
           (Cfor (makeN 6) (
              Cfor (makeN 7) (
                Nassign "result" (Nsucc (Nvar "result"))
              )
           ))

ex2 = Cseq (Nassign "x" (makeN 42))
      (Cseq (Nassign "result" Nzero)
            (Cwhile (Blt Nzero (Nvar "x"))
              (Cseq (Nassign "x" (Npred (Nvar "x")))
                    (Nassign "result" (Nsucc (Nvar "result"))))))

ex3 = Cseq (Nassign "x" (makeN 42))
      (Cseq (Nassign "result" Nzero)
            (Cwhile (Blt Nzero (Nvar "x"))
              (Cseq (Nassign "x" (Npred (Nvar "x")))
                    (Npp "result"))))

fix f = f (fix f)
