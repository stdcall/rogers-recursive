-- | Turing machines of section 1.5 (pp. 30-34): quadruples
-- q_i s o q_j (state, scanned symbol 1 or B, operation 1, B, R or L,
-- next state), the consistency restriction, the two-way infinite tape,
-- the conventions for inputs (x + 1 ones; for <x_1, ..., x_k> blocks of
-- x_i + 1 ones separated by one B; the machine starts in q_0 on the
-- leftmost 1) and for the output (the number of ones on the tape when
-- the machine stops), and the configurations "... q_i ..." of p. 33.
module Ch01Turing
  ( Sym (..), Op (..), Quad, Machine, Tape (..), Result (..)
  , consistent, states, inputTape, run, runFrom, output
  , configuration, configurations, loopsForever
  ) where

import Data.List (nub)

data Sym = One | Blank deriving (Eq, Show)

-- | The basic operations (1)-(4) of p. 30: write 1, erase (B), move the
-- attention one cell to the right (R) or to the left (L).
data Op = W1 | WB | R | L deriving (Eq, Show)

type Quad = (Int, Sym, Op, Int)

type Machine = [Quad]

-- | Two different quadruples differ in the state or in the scanned symbol.
consistent :: Machine -> Bool
consistent m = length (nub m) == length (nub [(q, s) | (q, s, _, _) <- m])

states :: Machine -> [Int]
states m = nub (concat [[q, q'] | (q, _, _, q') <- m])

-- | The tape: the cells left of the scanned one (nearest first), the
-- scanned cell, the cells right of it; the lists may be infinite, blanks
-- beyond their ends.
data Tape = Tape [Sym] Sym [Sym]

-- | Input <x_1, ..., x_k>, the machine on the leftmost 1.
inputTape :: [Int] -> Tape
inputTape xs = case concat (blocks xs) of
  (c : cs) -> Tape [] c cs
  [] -> Tape [] Blank []
  where
    blocks [] = []
    blocks [x] = [replicate (x + 1) One]
    blocks (x : rest) = (replicate (x + 1) One ++ [Blank]) : blocks rest

move :: Op -> Tape -> Tape
move W1 (Tape l _ r) = Tape l One r
move WB (Tape l _ r) = Tape l Blank r
move R (Tape l c (d : r)) = Tape (c : l) d r
move R (Tape l c []) = Tape (c : l) Blank []
move L (Tape (d : l) c r) = Tape l d (c : r)
move L (Tape [] c r) = Tape [] Blank (c : r)

step :: Machine -> (Int, Tape) -> Maybe (Int, Tape)
step m (q, t@(Tape _ c _)) =
  case [(o, q') | (p, s, o, q') <- m, p == q, s == c] of
    [(o, q')] -> Just (q', move o t)
    _ -> Nothing

data Result = Halted Int Tape Int   -- ^ final state, tape, number of steps
            | Running               -- ^ no stop within the given fuel

-- | Run from state q_0 on the input, at most fuel steps.
run :: Int -> Machine -> [Int] -> Result
run fuel m xs = runFrom fuel m 0 (inputTape xs)

runFrom :: Int -> Machine -> Int -> Tape -> Result
runFrom fuel m q0 t0 = go 0 (q0, t0)
  where
    go n c
      | n > fuel = Running
      | otherwise = case step m c of
          Nothing -> let (q, t) = c in Halted q t n
          Just c' -> go (n + 1) c'

-- | The output: all ones on a finite tape.
output :: Tape -> Int
output (Tape l c r) = length (filter (== One) (l ++ [c] ++ r))

-- | The configuration of p. 33: the stretch of the tape holding every
-- nonblank cell and the scanned cell, with "q_i" inserted just left of
-- the scanned symbol (a finite tape).
configuration :: Int -> Tape -> String
configuration q (Tape l c r) = concatMap sym left ++ "q" ++ show q ++ concatMap sym (c : right)
  where
    left = dropWhile (== Blank) (reverse l)
    right = reverse (dropWhile (== Blank) (reverse r))
    sym One = "1"
    sym Blank = "B"

-- | The first n configurations of a computation (fewer if it stops).
configurations :: Int -> Machine -> [Int] -> [String]
configurations n m xs = take n (go (0, inputTape xs))
  where
    go c@(q, t) = configuration q t : maybe [] go (step m c)

-- | One step leads back to the same configuration (state, scanned
-- symbol and tape unchanged): the machine never stops (it is
-- deterministic).  Checked for a finite tape.
loopsForever :: Machine -> Int -> Tape -> Bool
loopsForever m q t@(Tape l c r) = case step m (q, t) of
  Just (q', Tape l' c' r') -> q' == q && c' == c && trim l' == trim l && trim r' == trim r
  Nothing -> False
  where
    trim = reverse . dropWhile (== Blank) . reverse
