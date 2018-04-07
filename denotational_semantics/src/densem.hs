-- ------------------------------------------------------------------------------
-- Nikos Mavrogeorgis 03113087
-- GHCi, version 7.10.3
-- TODO : Usage
-- ------------------------------------------------------------------------------


--
-- Syntax
-- We present WHILE++ syntax in exact correspondence with the assignment's presentation.
-- We merge C and N rules.
-- 

type Var = String

data C = Cskip | 
		 Nzero | Nsucc C | Npred C | Nvar Var | Nassign Var C | Npp Var | Nmm Var |
		 Cseq C C | Cif B C C | Cfor C C | Cwhile B C  
  deriving (Show)

data B = Btrue | Bfalse | Blt C C | Beq C C | Bnot B
  deriving (Show)

-- Semantic domains

type S = Var -> Integer

--
-- Semantic functions
-- Every expression in C rules (either command or number), is evaluated as a tuple (State, Integer). 
-- Meaning that : 
-- 		1) It may change the current variable state, which is returned. 
-- 		2) It will return a number as a side effect. 
--
-- The evaluation of N-rules (Nzero, Nsucc etc.) is generally obvious. Concerning the returned Integer, 
-- the rule Nassign returns the value assigned. The rule Npp (Nmm), returns the value of the variable 
-- after adding (subtracting) 1.
--
-- The evaluation of C-rules (Cskip, Cseq etc.), concerning the returned Integer goes like this:
-- The rule Cskip returns the value 0. This makes sense, if we write "Cfor Cskip C", which is 
-- equivalent to Cskip itself (nothing is done).
-- 
--
--
-- Every expression in B rule, is evaluated as a boolean value.
-- 

-- Commands

semC :: C -> S -> (S, Integer)
semC Cskip s = (s, 0)
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

-- Examples
 
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

-- Usage of x++

ex3 = Cseq (Nassign "x" (makeN 42))
      (Cseq (Nassign "result" Nzero)
            (Cwhile (Blt Nzero (Nvar "x"))
              (Cseq (Nassign "x" (Npred (Nvar "x")))
                    (Npp "result"))))

-- Usage of Cskip as a value

ex4 = Cseq (Nassign "result" Cskip)
           (Cfor (makeN 6) (
              Cfor (makeN 7) (
                Nassign "result" (Nsucc (Nvar "result"))
              )
           ))


fix f = f (fix f)
