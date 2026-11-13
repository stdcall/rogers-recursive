-- | Checks of exercise 2-14 (pp. 64-65, finite-state machines with a
-- one-way input tape and a one-way output tape, no erasing) and of the
-- remark of p. 20 that lambda x [2x] is computable by such a device.
--
-- Run: runghc -ichecks/haskell checks/haskell/CheckCh01Automata.hs
--
-- A machine is modelled as a deterministic transducer: on each input
-- symbol (a digit, then the blank after the input) it writes a finite
-- string and changes its state.
--
-- Exercise 2-14 (c), lambda x [2x] in A_n for every n: true when the
-- digits are written least significant first (the carry is the state);
-- checked for the bases n = 2, ..., 16 and for the unary notation A_1
-- (x + 1 ones).  The book does not fix the order of the digits.  With
-- the usual order (most significant first) the claim holds for even n
-- (one digit of look-ahead decides the carry; checked for n = 2, 4, ...,
-- 16) and fails for odd n: with d = (n - 1)/2 and k digits d,
-- 2 (d...d0)_n = ((n-1)...(n-1)0)_n and 2 (d...d(n-1))_n = (10...0(n-2))_n
-- (for n = 3: 2 (1...10)_3 = (2...20)_3, 2 (1...12)_3 = (10...01)_3;
-- checked for n = 3, 5, ..., 15 and k <= 80), so the first digit of the
-- output (n - 1 or 1) is decided only by the last digit of the input, and
-- before writing it the machine must keep the number k, which no fixed
-- finite set of states can do (two values of k reaching the same state
-- give outputs of the wrong length).  That argument is not computed here.
--
-- Exercise 2-14 (f), the form of the functions of A_1: for random
-- transducers on the unary notation (seeded linear congruential
-- generator, 400 machines with at most 7 states) the output satisfies
-- f(x + n) - f(x) = m for x beyond the pre-period, with n the period of
-- the states: f is m [x/n] + q plus a function of period n, except at
-- finitely many points.  Only this direction, and only on the sample.
module Main (main) where

import Harness

-- | A transducer: start state, transition on a symbol (Nothing = the
-- blank after the input) giving the written string and the next state.
data Fst s a b = Fst s (s -> Maybe a -> ([b], s))

runFst :: Fst s a b -> [a] -> [b]
runFst (Fst s0 delta) xs = go s0 (map Just xs ++ [Nothing])
  where
    go _ [] = []
    go s (c : cs) = let (out, s') = delta s c in out ++ go s' cs

-- | Digits of x in base n, least significant first (0 is "0").
digitsLsb :: Integer -> Integer -> [Integer]
digitsLsb _ 0 = [0]
digitsLsb n x = go x
  where go 0 = []
        go y = y `mod` n : go (y `div` n)

fromLsb :: Integer -> [Integer] -> Integer
fromLsb n = foldr (\d acc -> d + n * acc) 0

-- | Doubling, least significant digit first: the state is the carry.
doubleLsb :: Integer -> Fst Integer Integer Integer
doubleLsb n = Fst 0 delta
  where
    delta c (Just d) = let v = 2 * d + c in ([v `mod` n], v `div` n)
    delta c Nothing = (if c == 1 then [1] else [], 0)

-- | Doubling in unary notation: x + 1 ones in, 2x + 1 ones out.
doubleUnary :: Fst Bool () ()
doubleUnary = Fst False delta
  where
    delta False (Just ()) = ([()], True)
    delta True (Just ()) = ([(), ()], True)
    delta s Nothing = ([], s)

-- | Doubling, most significant digit first, n even: the state keeps the
-- previous input digit; the carry into it is 1 iff the next digit is at
-- least n/2.
doubleMsbEven :: Integer -> Fst (Maybe Integer, Bool) Integer Integer
doubleMsbEven n = Fst (Nothing, True) delta
  where
    delta (Nothing, first) (Just d) = ([1 | first, 2 * d >= n], (Just d, False))
    delta (Just e, _) (Just d) = ([(2 * e + carry d) `mod` n], (Just d, False))
    delta (Just e, _) Nothing = ([(2 * e) `mod` n], (Nothing, False))
    delta st Nothing = ([], st)
    carry d = if 2 * d >= n then 1 else 0

fromMsb :: Integer -> [Integer] -> Integer
fromMsb n = foldl (\acc d -> n * acc + d) 0

-- Random unary transducers ---------------------------------------------

lcg :: Integer -> Integer
lcg x = (6364136223846793005 * x + 1442695040888963407) `mod` (2 ^ (64 :: Int))

-- | A random machine: k states; on a 1 in state i, write out1 !! i ones
-- and go to next !! i; on the blank, write outEnd !! i ones.
data Unary = Unary [Int] [Int] [Int]

randomUnary :: Integer -> (Unary, Integer)
randomUnary seed = (Unary nexts outs ends, s3)
  where
    (k, s0) = pick 7 seed
    (nexts, s1) = picks (k + 1) (k + 1) s0
    (outs, s2) = picks (k + 1) 4 s1
    (ends, s3) = picks (k + 1) 4 s2
    pick m s = let s' = lcg s in (fromInteger ((s' `div` 65536) `mod` toInteger m), s')
    picks 0 _ s = ([], s)
    picks j m s = let (v, s') = pick m s; (vs, s'') = picks (j - 1 :: Int) m s' in (v : vs, s'')

outputUnary :: Unary -> Int -> Int
outputUnary (Unary nexts outs ends) x = go 0 (x + 1) 0
  where
    go st 0 acc = acc + ends !! st
    go st j acc = go (nexts !! st) (j - 1) (acc + outs !! st)

-- | Pre-period and period of the states after 0, 1, 2, ... ones.
cycleOf :: Unary -> (Int, Int)
cycleOf (Unary nexts _ _) = go [] 0
  where
    go seen st = case lookup st (zip seen [0 ..]) of
      Just i -> (length seen - 1 - i, length seen - (length seen - 1 - i))
      Nothing -> go (st : seen) (nexts !! st)

formOk :: Unary -> Bool
formOk u = and [outputUnary u (x + n) - outputUnary u x == m | x <- [pre .. pre + 300]]
  where
    (pre, n) = cycleOf u
    m = outputUnary u (pre + n) - outputUnary u pre

randomMachines :: Int -> Integer -> [Unary]
randomMachines 0 _ = []
randomMachines j s = let (u, s') = randomUnary s in u : randomMachines (j - 1) s'

main :: IO ()
main = do
  c <- newCounter
  group c "2-14 (c): lambda x [2x] in A_n, digits least significant first"
    [ ("n = " ++ show n ++ ", x = " ++ show x,
       fromLsb n (runFst (doubleLsb n) (digitsLsb n x)) == 2 * x)
    | n <- [2 .. 16], x <- [0 .. 600] ]
  group c "2-14 (c): lambda x [2x] in A_1 (x + 1 ones)"
    [ ("x = " ++ show x, length (runFst doubleUnary (replicate (x + 1) ())) == 2 * x + 1)
    | x <- [0 .. 400] ]
  group c "2-14 (c), usual order, n even: one digit of look-ahead"
    [ ("n = " ++ show n ++ ", x = " ++ show x,
       fromMsb n (runFst (doubleMsbEven n) (reverse (digitsLsb n x))) == 2 * x
         && (x == 0 || take 1 (runFst (doubleMsbEven n) (reverse (digitsLsb n x))) /= [0]))
    | n <- [2, 4 .. 16], x <- [0 .. 600] ]
  group c "2-14 (c), usual order, n odd: the first output digit waits for the last input digit"
    ( [ ("n = " ++ show n ++ ", k = " ++ show k,
         let d = (n - 1) `div` 2
         in 2 * fromMsb n (replicate k d ++ [0]) == fromMsb n (replicate k (n - 1) ++ [0])
              && 2 * fromMsb n (replicate k d ++ [n - 1]) == fromMsb n ([1] ++ replicate k 0 ++ [n - 2]))
      | n <- [3, 5 .. 15], k <- [0 .. 80] ]
      ++ [ ("n = " ++ show n ++ ", k = " ++ show k ++ ", first digits n - 1 and 1, lengths k + 1 and k + 2",
            let d = (n - 1) `div` 2
                a = reverse (digitsLsb n (2 * fromMsb n (replicate k d ++ [0])))
                b = reverse (digitsLsb n (2 * fromMsb n (replicate k d ++ [n - 1])))
            in take 1 a == [n - 1] && take 1 b == [1] && length a == k + 1 && length b == k + 2)
         | n <- [3, 5 .. 15], k <- [1 .. 80] ] )
  group c "2-14 (f): A_1 outputs are m [x/n] + q plus a function of period n (sample)"
    [ ("machine " ++ show i, formOk u) | (i, u) <- zip [1 :: Int ..] (randomMachines 400 2026) ]
  finish c "ch01-04-automata"
