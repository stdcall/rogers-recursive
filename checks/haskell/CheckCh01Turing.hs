-- | Checks of chapter 1, sections 1.5 and 1.8-1.10 (pp. 30-34, 40-41,
-- 44, 49-50): the Turing machines of the book run on inputs, the
-- configurations of p. 33, the padding of theorem III (p. 41), the
-- looping pair of quadruples of p. 44, the functions p, q, t of the
-- normal form theorem X (pp. 49-50) on concrete machines, and Kleene's
-- system of equations for lambda x [2x] (p. 34).
--
-- Run: runghc -ichecks/haskell checks/haskell/CheckCh01Turing.hs
--
-- Expected values are the printed ones: the eraser machine of p. 31
-- (erases a block of ones and stops; never stops on a tape of ones),
-- the machine of p. 32 for lambda x [2x] (stops in q_2 for the input 0,
-- in q_8 otherwise), its first configurations for the input 2 (p. 33),
-- the function lambda x_1 ... x_k [2x_1 + x_2 + ... + x_k + k - 1]
-- (p. 33), the function lambda x [x + 1] of a machine without q_0
-- (footnote, p. 32), the padding q_m 1 1 q_m, ..., q_(m+k) 1 1 q_(m+k)
-- of theorem III, the quadruples q_n 1 1 q_n, q_n B B q_n of p. 44,
-- p, q, t and the identity phi_z = lambda x [p(mu y [t(z, x, y) = 1])]
-- of theorem X, Kleene's equations f(0) = 0, g(x) = f(x) + 1,
-- f(x + 1) = g(x) + 1 of p. 34.
--
-- Theorem III, p. 41: the printed choice of m ("a number exceeding the
-- subscripts of all internal states of P_(x_0)") admits m = 0 for the
-- empty set of quadruples (a machine by p. 32; it computes
-- lambda x [x + 1]); then the added quadruple q_0 1 1 q_0 is used at
-- once and the machine never stops.  The refuted printed case is
-- checked beside the corrected choice m > 0.
--
-- Not established: the general statements (that the machine of p. 32
-- computes 2x for every x, theorem III, theorem X for every machine)
-- beyond the finite ranges below; termination is checked within a step
-- bound, non-termination only where one step returns to the same
-- configuration (then the deterministic machine repeats it forever) or,
-- for the tape of ones of p. 31, as an invariant over a bounded number of
-- steps.
module Main (main) where

import Ch01Turing
import Harness

-- | The eraser of p. 31: q_0 1 B q_2, q_2 B R q_0.
eraser :: Machine
eraser = [(0, One, WB, 2), (2, Blank, R, 0)]

-- | The machine of p. 32 for lambda x [2x].
double :: Machine
double =
  [ (0, One, WB, 1), (1, Blank, R, 2), (2, One, WB, 3), (3, Blank, R, 4)
  , (4, One, R, 4), (4, Blank, R, 5), (5, One, R, 5), (5, Blank, W1, 6)
  , (6, One, R, 6), (6, Blank, W1, 7), (7, One, L, 7), (7, Blank, L, 8)
  , (8, One, L, 1), (1, One, L, 1) ]

fuel :: Int
fuel = 200000

halts :: Machine -> [Int] -> Maybe (Int, Int, Int)  -- state, output, steps
halts m xs = case run fuel m xs of
  Halted q t n -> Just (q, output t, n)
  Running -> Nothing

-- | Theorem III: add q_m 1 1 q_m, ..., q_(m+k) 1 1 q_(m+k).
pad :: Int -> Int -> Machine -> Machine
pad m k p = p ++ [(i, One, W1, i) | i <- [m .. m + k]]

-- | The eraser on a tape of ones infinite to the right: at every even
-- step (up to the bound) it is in q_0 scanning a 1 and has not stopped.
eraserOnOnes :: Int -> Bool
eraserOnOnes bound = go 0 (0, Tape [] One (repeat One))
  where
    go n (q, t@(Tape _ c _))
      | n >= bound = True
      | even n && (q /= 0 || c /= One) = False
      | otherwise = case stepOf (q, t) of
          Nothing -> False
          Just c' -> go (n + 1) c'
    stepOf (q, t@(Tape _ c _)) =
      case [(o, q') | (p, s, o, q') <- eraser, p == q, s == c] of
        [(o, q')] -> Just (q', apply o t)
        _ -> Nothing
    apply WB (Tape l _ r) = Tape l Blank r
    apply W1 (Tape l _ r) = Tape l One r
    apply R (Tape l c (d : r)) = Tape (c : l) d r
    apply R (Tape l c []) = Tape (c : l) Blank []
    apply L (Tape (d : l) c r) = Tape l d (c : r)
    apply L (Tape [] c r) = Tape [] Blank (c : r)

-- Normal form, theorem X ------------------------------------------------

-- | s(z, x, y, w) = 1 iff P_z on the input x gives the output y within w
-- steps (the machines are given directly instead of by their indices).
s :: Machine -> Int -> Int -> Int -> Int
s m x y w = case run w m [x] of
  Halted _ t _ | output t == y -> 1
  _ -> 0

-- | The exponent of the prime b in x + 1 (p uses 3, q uses 2).
expo :: Int -> Int -> Int
expo b x = go (x + 1) 0
  where go n e = if n `mod` b == 0 then go (n `div` b) (e + 1) else e

p, q :: Int -> Int
p = expo 3
q = expo 2

t :: Machine -> Int -> Int -> Int
t m x y = s m x (p y) (q y)

-- | mu y [t(z, x, y) = 1], searched below a bound.
muT :: Int -> Machine -> Int -> Maybe Int
muT bound m x = case [y | y <- [0 .. bound], t m x y == 1] of
  (y : _) -> Just y
  [] -> Nothing

-- Kleene's system of p. 34: f(0) = 0, g(x) = f(x) + 1, f(x + 1) = g(x) + 1.
kleeneF, kleeneG :: Integer -> Integer
kleeneF 0 = 0
kleeneF x = kleeneG (x - 1) + 1
kleeneG x = kleeneF x + 1

main :: IO ()
main = do
  c <- newCounter
  group c "p. 31: eraser q0 1 B q2, q2 B R q0"
    ( ("consistent", consistent eraser)
    : [ ("block of " ++ show n ++ " ones erased, stop",
         case runFrom fuel eraser 0 (Tape [] One (replicate (n - 1) One)) of
           Halted 0 tp _ -> output tp == 0
           _ -> False)
      | n <- [1 .. 60] ]
      ++ [("tape of ones: q0 on a 1 at every even step, 100000 steps", eraserOnOnes 100000)] )
  group c "p. 32: the machine for lambda x [2x]"
    ( ("consistent", consistent double)
    : [ ("x = " ++ show x, case halts double [x] of
          Just (st, out, _) -> out == 2 * x && st == (if x == 0 then 2 else 8)
          Nothing -> False)
      | x <- [0 .. 60] ] )
  group c "p. 33: configurations for the input 2"
    [ ("q0 111 ... 1 q4 B", configurations 6 double [2] ==
        ["q0111", "q1B11", "q211", "q3B1", "q41", "1q4B"]) ]
  group c "p. 33: lambda x_1 ... x_k [2x_1 + x_2 + ... + x_k + k - 1]"
    [ ("k = " ++ show (length xs) ++ ", " ++ show xs, case halts double xs of
        Just (st, out, _) ->
          out == 2 * sum (take 1 xs) + sum (drop 1 xs) + length xs - 1
            && st == (if take 1 xs == [0] then 2 else 8)
        Nothing -> False)
    | k <- [1 .. 4], xs <- mapM (const [0 .. 5]) [1 .. k] ]
  group c "p. 32, footnote: no q0, the function lambda x [x + 1]"
    [ ("x = " ++ show x ++ ", machine " ++ show i, case halts mch [x] of
        Just (_, out, 0) -> out == x + 1
        _ -> False)
    | (i, mch) <- zip [1 :: Int ..] [[], [(5, One, R, 5)], [(3, Blank, W1, 1), (1, One, L, 3)]]
    , x <- [0 .. 20] ]
  let maxState mch = maximum (0 : states mch)
  group c "theorem III (p. 41): padding with q_m 1 1 q_m, m > 0"
    [ ("machine " ++ show i ++ ", m = " ++ show m ++ ", k = " ++ show k ++ ", x = " ++ show x,
       fmap (\(_, out, _) -> out) (halts (pad m k mch) [x])
         == fmap (\(_, out, _) -> out) (halts mch [x])
         && consistent (pad m k mch))
    | (i, mch) <- zip [1 :: Int ..] [double, eraser, [], [(5, One, R, 5)]]
    , m <- [max 1 (maxState mch + 1) .. max 1 (maxState mch + 1) + 2]
    , k <- [0 .. 5], x <- [0 .. 12] ]
  group c "theorem III: the printed choice m = 0 for the empty machine (refuted)"
    [ ("empty machine: x + 1 at x = 0", fmap (\(_, out, _) -> out) (halts [] [0]) == Just 1)
    , ("m = 0 exceeds the subscripts of the (no) states of the empty machine",
       null (states []))
    , ("q0 1 1 q0 added: the first step repeats the configuration",
       loopsForever (pad 0 0 []) 0 (inputTape [0]))
    , ("so the padded machine has no output at 0", case halts (pad 0 3 []) [0] of
         Nothing -> True
         Just _ -> False) ]
  group c "p. 44: q_n 1 1 q_n, q_n B B q_n repeat the configuration"
    [ ("n = " ++ show n ++ ", scanned " ++ show sc,
       loopsForever [(n, One, W1, n), (n, Blank, WB, n)] n (Tape [] sc [One, Blank, One]))
    | n <- [0, 3, 9], sc <- [One, Blank] ]
  group c "theorem X: every pair <p(y), q(y)> occurs (y = 2^b 3^a - 1)"
    [ ("a = " ++ show a ++ ", b = " ++ show b,
       p (2 ^ b * 3 ^ a - 1) == a && q (2 ^ b * 3 ^ a - 1) == b)
    | a <- [0 .. 12], b <- [0 .. 20] ]
  group c "theorem X: the least y with p(y) = v, q(y) >= n is 2^n 3^v - 1"
    [ ("v = " ++ show v ++ ", n = " ++ show n,
       take 1 [y | y <- [0 ..], p y == v, q y >= n] == [2 ^ n * 3 ^ v - 1])
    | v <- [0 .. 4], n <- [0 .. 8] ]
  group c "theorem X: phi_z = lambda x [p(mu y [t(z, x, y) = 1])]"
    ( [ ("machine " ++ show i ++ ", x = " ++ show x,
         case halts mch [x] of
           Just (_, out, steps) ->
             muT (2 ^ steps * 3 ^ out) mch x == Just (2 ^ steps * 3 ^ out - 1)
               && fmap p (muT (2 ^ steps * 3 ^ out) mch x) == Just out
           Nothing -> False)
      | (i, mch, xs) <- [ (1 :: Int, eraser, [0 .. 5]), (2, double, [0, 1])
                         , (3, [], [0 .. 6]), (4, [(5, One, R, 5)], [0 .. 6]) ]
      , x <- xs ]
      ++ [ ("never stops: no y <= 5000 with t = 1, x = " ++ show x,
            muT 5000 (pad 0 0 []) x == Nothing)
         | x <- [0 .. 3] ] )
  group c "p. 34: Kleene's equations give lambda x [2x]"
    [ ("x = " ++ show x, kleeneF x == 2 * x) | x <- [0 .. 200] ]
  finish c "ch01-04-turing"
