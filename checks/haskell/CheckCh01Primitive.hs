-- | Checks of the introduction and of chapter 1, sections 1.2-1.5
-- (pp. 13, 22-29), and of the hint of exercise 2-1 (p. 62): the
-- Fibonacci numbers and their closed form, primitive recursive
-- derivations (clauses (i)-(v) of the definition, p. 22-23) run by an
-- interpreter, the derivation of lambda x [2x] (p. 23) and the
-- computation of f(2) (p. 24) step by step, Ackermann's function (p. 25)
-- in its formal definition against the informal description, the
-- derivations of the hint of exercise 2-1, and two small examples of the
-- introduction and of p. 29.
--
-- Run: runghc -ichecks/haskell checks/haskell/CheckCh01Primitive.hs
--
-- Expected values: the printed numbers 1, 1, 2, 3, 5, 8, 13 and the
-- formula f(x) = sqrt5/5 ((1 + sqrt5)/2)^(x+1) - sqrt5/5 ((1 - sqrt5)/2)^(x+1)
-- (p. 22, evaluated exactly in Q(sqrt5)); f_5 = lambda x y [x + y] and
-- f_6 = lambda x [2x] (p. 23); the fourteen printed lines of the
-- computation of f(2) = 4 (p. 24); f(0, x, y) = y + x, f(1, x, y) = y x,
-- f(2, x, y) = y^x and "the result of applying to y x - 1 times the
-- operation of level z" (p. 25); the functions h^ = lambda x [max(0, x - 1)],
-- h = lambda x y [max(0, x - y)], f = lambda x [min(x, 1)] and the step
-- functions g of section 1.3 (p. 26) of exercise 2-1; the domain of
-- "the least prime proper divisor of x" (p. 13); the domain {0, ..., 8}
-- of the instruction of p. 29 if pi had eight fives in a row and no
-- more (checked on model digit strings).
--
-- Correction checked (p. 23): the last line of the derivation, printed
-- "f_6 = f_5(f_1, f_1) by (iii)", is by (iv): f_6 is not a selection
-- function (refuted printed reading) and is the substitution of f_1, f_1
-- into f_5 (the corrected reading).
--
-- Ackermann's function: the informal line agrees with the formal
-- definition for every x >= 1 (also proved for all z, x >= 1, y in
-- checks/lean/RogersRecursive/Ch01_04Ackermann.lean); at x = 0 it says
-- nothing ("x - 1 times"), and read with x - 1 = 0 it would give y,
-- against f(1, 0, y) = 0 and f(z + 2, 0, y) = 1.
--
-- Not established: that lambda x [f(x, x, x)] is not primitive recursive
-- (footnote, p. 25), or any statement beyond the finite ranges below.
module Main (main) where

import Harness

-- Q(sqrt5) -----------------------------------------------------------

-- | a + b sqrt5 with rational a, b.
data Q5 = Q5 Rational Rational deriving (Eq, Show)

instance Num Q5 where
  Q5 a b + Q5 c d = Q5 (a + c) (b + d)
  Q5 a b * Q5 c d = Q5 (a * c + 5 * b * d) (a * d + b * c)
  negate (Q5 a b) = Q5 (negate a) (negate b)
  fromInteger n = Q5 (fromInteger n) 0
  abs = undefined
  signum = undefined

binet :: Integer -> Q5
binet x = c * (phi ^ (x + 1)) - c * (psi ^ (x + 1))
  where
    c = Q5 0 (1 / 5)                  -- sqrt5 / 5
    phi = Q5 (1 / 2) (1 / 2)          -- (1 + sqrt5) / 2
    psi = Q5 (1 / 2) (-1 / 2)         -- (1 - sqrt5) / 2

fib :: [Integer]
fib = 1 : 1 : zipWith (+) fib (drop 1 fib)

-- Primitive recursive derivations ---------------------------------------

-- | The clauses of the definition (pp. 22-23).  RecN g h is clause (v)
-- with k = 1, where g is "a function of zero variables", a number.
data PR
  = Const Int Integer   -- (i): lambda x_1 ... x_k [m]
  | Succ                -- (ii)
  | Proj Int Int        -- (iii): lambda x_1 ... x_k [x_i]
  | Comp PR [PR]        -- (iv): f(g_1, ..., g_k)
  | Rec PR PR           -- (v), k >= 2
  | RecN Integer PR     -- (v), k = 1

-- | The number of variables, if the derivation is well formed.
arity :: PR -> Maybe Int
arity (Const k _) | k >= 1 = Just k
arity Succ = Just 1
arity (Proj k i) | 1 <= i && i <= k = Just k
arity (Comp f gs) = do
  k <- arity f
  ms <- mapM arity gs
  case ms of
    (m : rest) | length gs == k && all (== m) rest -> Just m
    _ -> Nothing
arity (Rec g h) = do
  a <- arity g
  b <- arity h
  if b == a + 2 then Just (a + 1) else Nothing
arity (RecN _ h) = do
  b <- arity h
  if b == 2 then Just 1 else Nothing
arity _ = Nothing

eval :: PR -> [Integer] -> Integer
eval (Const _ m) _ = m
eval Succ [x] = x + 1
eval (Proj _ i) xs = xs !! (i - 1)
eval (Comp f gs) xs = eval f [eval g xs | g <- gs]
eval (Rec g h) (y : xs) =
  foldl (\acc n -> eval h (n : acc : xs)) (eval g xs) [0 .. y - 1]
eval (RecN m h) [y] = foldl (\acc n -> eval h [n, acc]) m [0 .. y - 1]
eval _ _ = error "ill-formed application"

-- | Is the derivation a selection function (clause (iii)) of k variables?
-- On the inputs tried: equal to some lambda x_1 ... x_k [x_i].
isSelection :: Int -> PR -> Bool
isSelection k f = or [all (\xs -> eval f xs == xs !! (i - 1)) inputs | i <- [1 .. k]]
  where inputs = mapM (const [0 .. 3]) [1 .. k]

-- The derivation of p. 23.
f1, f2, f3, f4, f5, f6 :: PR
f1 = Proj 1 1
f2 = Succ
f3 = Proj 3 2
f4 = Comp f2 [f3]
f5 = Rec f1 f4
f6 = Comp f5 [f1, f1]

-- The computation of p. 24 --------------------------------------------

data T = N Integer | Ap String [T] deriving (Eq, Show)

-- | One rewriting step at the root: the defining equation of the name
-- applied to numerals (and the name f of f_6).
rootStep :: T -> [T]
rootStep (Ap "f" [a]) = [Ap "f6" [a]]
rootStep (Ap "f6" [a]) = [Ap "f5" [Ap "f1" [a], Ap "f1" [a]]]
rootStep (Ap "f1" [N x]) = [N x]
rootStep (Ap "f2" [N x]) = [N (x + 1)]
rootStep (Ap "f3" [N _, N b, N _]) = [N b]
rootStep (Ap "f4" [a, b, c]) = [Ap "f2" [Ap "f3" [a, b, c]]]
rootStep (Ap "f5" [N 0, a]) = [Ap "f1" [a]]
rootStep (Ap "f5" [N y, a]) | y > 0 = [Ap "f4" [N (y - 1), Ap "f5" [N (y - 1), a], a]]
rootStep _ = []

-- | All terms obtained by one rewriting step anywhere in the term.
oneStep :: T -> [T]
oneStep t@(N _) = rootStep t
oneStep t@(Ap g as) = rootStep t ++
  [Ap g (pre ++ [a'] ++ post) | (pre, a : post) <- splits as, a' <- oneStep a]
  where splits xs = [splitAt i xs | i <- [0 .. length xs - 1]]

value :: T -> Integer
value (N x) = x
value t = case rootStep t of
  [t'] -> value t'
  _ -> value (reduceArgs t)
  where
    reduceArgs (Ap g as) = Ap g (map (N . value) as)
    reduceArgs u = u

-- | The fourteen lines of p. 24.
printed :: [T]
printed =
  [ Ap "f" [n 2]
  , Ap "f6" [n 2]
  , Ap "f5" [Ap "f1" [n 2], Ap "f1" [n 2]]
  , Ap "f5" [n 2, Ap "f1" [n 2]]
  , Ap "f5" [n 2, n 2]
  , Ap "f4" [n 1, Ap "f5" [n 1, n 2], n 2]
  , Ap "f4" [n 1, Ap "f4" [n 0, Ap "f5" [n 0, n 2], n 2], n 2]
  , Ap "f4" [n 1, Ap "f4" [n 0, Ap "f1" [n 2], n 2], n 2]
  , Ap "f4" [n 1, Ap "f4" [n 0, n 2, n 2], n 2]
  , Ap "f4" [n 1, Ap "f2" [Ap "f3" [n 0, n 2, n 2]], n 2]
  , Ap "f4" [n 1, Ap "f2" [n 2], n 2]
  , Ap "f4" [n 1, n 3, n 2]
  , Ap "f2" [Ap "f3" [n 1, n 3, n 2]]
  , Ap "f2" [n 3]
  , n 4 ]
  where n = N

-- Ackermann's function, p. 25 ----------------------------------------

ack :: Integer -> Integer -> Integer -> Integer
ack 0 0 y = y
ack 0 x y = ack 0 (x - 1) y + 1
ack 1 0 _ = 0
ack _ 0 _ = 1
ack z x y = ack (z - 1) (ack z (x - 1) y) y

-- | The informal reading: apply u -> f(z, u, y) to y, x - 1 times.
informal :: Integer -> Integer -> Integer -> Integer
informal z x y = iterate (\u -> ack z u y) y !! fromInteger (x - 1)

-- Exercise 2-1 ---------------------------------------------------------

hHat, hSub, hRev, fMin :: PR
hHat = RecN 0 (Proj 2 1)                 -- h^(0) = 0, h^(y + 1) = y
hRev = Rec (Proj 1 1) (Comp hHat [Proj 3 2])  -- H(y, x) = x - y (truncated)
hSub = Comp hRev [Proj 2 2, Proj 2 1]    -- h(x, y) = H(y, x)
fMin = RecN 0 (Const 2 1)                -- f(0) = 0, f(y + 1) = 1

-- | g(x) = 1 for x <= k, 0 for k < x: g = h(1, f(h(x, k))).
gStep :: Integer -> PR
gStep k = Comp hSub [Const 1 1, Comp fMin [Comp hSub [Proj 1 1, Const 1 k]]]

-- Small examples ---------------------------------------------------------

isPrime :: Integer -> Bool
isPrime n = n >= 2 && all (\d -> n `mod` d /= 0) (takeWhile (\d -> d * d <= n) [2 ..])

-- | The least prime proper divisor of x (p. 13), if any.
leastPrimeProperDivisor :: Integer -> Maybe Integer
leastPrimeProperDivisor x =
  case [d | d <- [2 .. max 2 x], isPrime d, d /= x, x `mod` d == 0] of
    (d : _) -> Just d
    [] -> Nothing

-- | The instruction of p. 29 on a finite digit string: the place of the
-- first digit of the first run of at least x fives (places from 1), if
-- the run lies in the string.
firstRun :: String -> Int -> Maybe Int
firstRun ds x = case [i | i <- [0 .. length ds - x], all (== '5') (take x (drop i ds))] of
  (i : _) -> Just (i + 1)
  [] -> Nothing

main :: IO ()
main = do
  c <- newCounter
  group c "p. 22: Fibonacci numbers and their closed form"
    ( ("1, 1, 2, 3, 5, 8, 13", take 7 fib == [1, 1, 2, 3, 5, 8, 13])
    : [("x = " ++ show x, binet x == Q5 (fromInteger (fib !! fromInteger x)) 0) | x <- [0 .. 80]] )
  group c "p. 23: the derivation of lambda x [2x]"
    ( [ ("f1 ... f6 well formed", map arity [f1, f2, f3, f4, f5, f6] ==
          map Just [1, 1, 3, 3, 2, 1]) ]
      ++ [("f5(y, x) = x + y, " ++ show (y, x), eval f5 [y, x] == x + y) | y <- [0 .. 25], x <- [0 .. 25]]
      ++ [("f6(x) = 2x, x = " ++ show x, eval f6 [x] == 2 * x) | x <- [0 .. 100]] )
  group c "p. 23: f6 by (iv), not by (iii) (printed reading refuted)"
    [ ("f6 is not a selection function of one variable", not (isSelection 1 f6))
    , ("f6 = f5(f1, f1), a substitution of 1-variable functions into f5",
       arity (Comp f5 [f1, f1]) == Just 1 && all (\x -> eval f6 [x] == eval f5 [eval f1 [x], eval f1 [x]]) [0 .. 50])
    , ("the selection functions (iii) are f1, f3: they are", isSelection 1 f1 && isSelection 3 f3) ]
  group c "p. 24: the computation of f(2)"
    ( [ ("line " ++ show i ++ " -> line " ++ show (i + 1) ++ " is one step", b `elem` oneStep a)
      | (i, a, b) <- zip3 [1 :: Int ..] printed (drop 1 printed) ]
      ++ [("line " ++ show i ++ " has the value 4", value l == 4) | (i, l) <- zip [1 :: Int ..] printed]
      ++ [("fourteen lines after f(2)", length printed == 15)] )
  group c "p. 25: Ackermann's function, levels 0, 1, 2"
    ( [("f(0, x, y) = y + x " ++ show (x, y), ack 0 x y == y + x) | x <- [0 .. 30], y <- [0 .. 30]]
      ++ [("f(1, x, y) = y x " ++ show (x, y), ack 1 x y == y * x) | x <- [0 .. 20], y <- [0 .. 20]]
      ++ [("f(2, x, y) = y^x " ++ show (x, y), ack 2 x y == y ^ x) | x <- [0 .. 6], y <- [0 .. 4]] )
  group c "p. 25: informal line for x >= 1 (x - 1 applications of level z)"
    ( [ ("z + 1 = " ++ show (z + 1) ++ ", x = " ++ show x ++ ", y = " ++ show y, ack (z + 1) x y == informal z x y)
      | (z, xs, ys) <- [(0, [1 .. 15], [0 .. 15]), (1, [1 .. 6], [0 .. 4]), (2, [1 .. 3], [0 .. 2]), (2, [1, 2], [3])]
      , x <- xs, y <- ys ]
      ++ [("f(3, 3, 2) = 2^(2^2) = 16", ack 3 3 2 == 16)] )
  group c "p. 25: at x = 0 the formal definition, not y"
    ( [("f(1, 0, y) = 0, y = " ++ show y, ack 1 0 y == 0 && (y == 0 || ack 1 0 y /= y)) | y <- [0 .. 10]]
      ++ [("f(z + 2, 0, y) = 1 " ++ show (z, y), ack (z + 2) 0 y == 1 && (y == 1 || ack (z + 2) 0 y /= y))
         | z <- [0 .. 3], y <- [0 .. 10]]
      ++ [("f(0, 0, y) = y", all (\y -> ack 0 0 y == y) [0 .. 10])] )
  group c "exercise 2-1: the derivations of the hint"
    ( [ ("h^, h, f, g well formed", map arity [hHat, hRev, hSub, fMin, gStep 3] ==
          map Just [1, 2, 2, 1, 1]) ]
      ++ [("h^(x) = max(0, x - 1), x = " ++ show x, eval hHat [x] == max 0 (x - 1)) | x <- [0 .. 40]]
      ++ [("h(x, y) = max(0, x - y) " ++ show (x, y), eval hSub [x, y] == max 0 (x - y)) | x <- [0 .. 20], y <- [0 .. 20]]
      ++ [("f(x) = min(x, 1), x = " ++ show x, eval fMin [x] == min x 1) | x <- [0 .. 40]]
      ++ [ ("g: 1 for x <= " ++ show k ++ ", 0 after; x = " ++ show x, eval (gStep k) [x] == (if x <= k then 1 else 0))
         | k <- [0 .. 12], x <- [0 .. 30] ]
      ++ [("g = lambda x [1] by (i)", all (\x -> eval (Const 1 1) [x] == 1) [0 .. 30])] )
  group c "p. 13: the least prime proper divisor of x is defined iff x is not prime and x /= 1"
    ( ("{2, 5, 3}: the first three primes", take 3 (filter isPrime [0 ..]) == [2, 3, 5])
    : [ ("x = " ++ show x, (leastPrimeProperDivisor x /= Nothing) == (not (isPrime x) && x /= 1))
      | x <- [0 .. 3000] ] )
  group c "p. 29: eight fives in a row and no more: the domain {0, ..., 8}"
    [ ("digits " ++ take 12 ds ++ "...", [x | x <- [0 .. 20], firstRun ds x /= Nothing] == [0 .. 8])
    | ds <- [ "1415926" ++ replicate 8 '5' ++ "3" ++ "55" ++ "12555"
            , replicate 8 '5' ++ "0" ++ replicate 7 '5'
            , "3" ++ replicate 8 '5' ] ]
  finish c "ch01-04-primitive"
