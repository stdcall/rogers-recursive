-- | Checks of chapter 5 (pp. 81-105): the procedures of the proofs of
-- theorems I-V run on model sets and model computations, the coding of
-- pairs tau, pi_1, pi_2 and of n-tuples tau^n, pi_i^n (section 5.3, with
-- examples 1 and 2), the canonical indices D_x and the coding tau^* of all
-- n-tuples (section 5.6), and the uniformization of section 5.7 with the
-- reduction principle and the selection theorem on finite models.
--
-- Run: runghc -ichecks/haskell checks/haskell/CheckCh05Codings.hs
--
-- Expected values (printed pages and our labels):
-- * p. 89: tau(x, y) = 1/2 (x^2 + 2xy + y^2 + 3x + y) lists the pairs
--   <0,0>, <0,1>, <1,0>, <0,2>, <1,1>, <2,0>, <0,3>, <1,2>, ... as 0, 1, ...,
--   7, and is one-one onto N (the lemma of section 5.3, also proved for all
--   arguments in checks/lean/RogersRecursive/Ch05_07Pairing.lean); pi_1,
--   pi_2 are its inverses (p. 90); tau^n by the inductive definition of
--   p. 90; example 1: <2, 1, 0> = <<2, 1>, 0> = <8, 0> = 44; example 2:
--   tau^4(A^4) = ((A x A) x A) x A, and x is left associative.
-- * p. 97: D_x by the binary digits of x; D_13 = {0, 2, 3}; theorem XV (a)
--   (th:canonical-index-cardinality): the cardinality of D_x.  P. 119
--   (proof of theorem 7-VII): the canonical index of {f'(m_0)} is
--   2^(f'(m_0)), that of {f'(m_0), f'(m_1)} is 2^(f'(m_0)) + 2^(f'(m_1)).
-- * p. 98: tau^*(empty) = 0, tau^*(<x_1, ..., x_n>) = tau(tau^n(x_1, ...,
--   x_n), n - 1) + 1 = <x_1, ..., x_n, n - 1> + 1, one-one onto N (proved
--   in the Lean file above); exercise 5-30 (ex:tau-star-inverse) asks for
--   the inverse: for z > 0, n = pi_2(z - 1) + 1 and x_i = pi_i^n(pi_1(z -
--   1)) (our answer; the book prints none) is checked here.
-- * Theorem I (p. 82, th:recursive-implies-re), cases (ii), (iii); theorem
--   II (p. 82, th:recursive-iff-complement-re), the zigzag search; theorem
--   III (pp. 83-84, th:re-in-order), the decision procedures of the proof
--   of <=; theorem IV (p. 84, th:infinite-recursive-subset), g(x + 1) =
--   f(mu y [f(y) > g(x)]); theorem V (pp. 84-85, th:basic-theorem-re), the
--   stages of the proof of <= and the function eta, on model computations
--   given by their numbers of steps.
-- * Exercise 5-3 (a) (ex:recursive-sets-isomorphic): the isomorphism of
--   two infinite coinfinite recursive sets (k-th element to k-th element,
--   in the sets and in the complements); exercise 5-22
--   (ex:coding-not-invariant), the sets tau^2({1} x N), tau^2(N x {1}) of
--   the hint (that R, Q themselves are not isomorphic as relations is
--   proved in checks/lean/RogersRecursive/Ch05_07Numbering.lean);
--   exercise 5-14 (a) (ex:product-operation): the questions of the book
--   answered on examples (x is neither associative nor commutative,
--   distributive over union).
-- * Theorem XVI (pp. 99-100, th:single-valuedness): the set A_z of the
--   proof computed from a model enumeration without repetitions of W_z
--   satisfies (i)-(iv); theorem XVII (p. 100, th:reduction-principle) and
--   theorem XVIII (p. 101, th:selection) by the constructions of their
--   proofs on finite models.
--
-- The model computations: a "partial function" psi is given by the
-- number of steps of the computation of psi(k) (Nothing: it diverges), so
-- the stages of theorem V can be run exactly.  Stage n + 1 of the proof
-- adds to the list every k <= n whose computation stops within n + 1
-- steps, also those already listed at an earlier stage; with this reading
-- eta lists Arg psi.  A misreading of "y было добавлено к списку на этапе
-- x + 1" as "first added at stage x + 1" loses elements; it is checked as
-- refuted (the printed stages re-add every element, so the printed text
-- does not mean it).
--
-- Not established: any general statement beyond the finite ranges and
-- the models below; recursiveness, recursive enumerability, uniformity
-- (these are Church's thesis and the s-m-n theorem in the book); the
-- theorems about K.
module Main (main) where

import Data.Bits (popCount, testBit)
import Data.List (nub, sort, sortOn)

import Harness

------------------------------------------------------------------------
-- Pairs and tuples (section 5.3)

numerator :: Integer -> Integer -> Integer
numerator x y = x * x + 2 * x * y + y * y + 3 * x + y

-- | tau of p. 89.
tau :: Integer -> Integer -> Integer
tau x y = numerator x y `div` 2

tri :: Integer -> Integer
tri n = n * (n + 1) `div` 2

-- | The inverse of tau (pi_1, pi_2 of p. 90), found by search.
untau :: Integer -> (Integer, Integer)
untau z = head [(x, s - x) | s <- [0 ..], tri (s + 1) > z, let x = z - tri s]

pi1, pi2 :: Integer -> Integer
pi1 = fst . untau
pi2 = snd . untau

-- | tau^n by the inductive definition of p. 90: tau^1 = lambda x [x],
-- tau^(n+1)(x_1, ..., x_(n+1)) = tau(tau^n(x_1, ..., x_n), x_(n+1)).
tauN :: [Integer] -> Integer
tauN [x] = x
tauN xs = tau (tauN (init xs)) (last xs)

-- | pi_1^n, ..., pi_n^n: tau^n(piN n z) = z.
piN :: Int -> Integer -> [Integer]
piN 1 z = [z]
piN n z = piN (n - 1) (pi1 z) ++ [pi2 z]

-- | tau^* of p. 98, first printed form, and the second form.
tauStar, tauStar' :: [Integer] -> Integer
tauStar [] = 0
tauStar xs = tau (tauN xs) (fromIntegral (length xs) - 1) + 1
tauStar' [] = 0
tauStar' xs = tauN (xs ++ [fromIntegral (length xs) - 1]) + 1

-- | The inverse of tau^* (our answer to exercise 5-30).
tauStarInv :: Integer -> [Integer]
tauStarInv 0 = []
tauStarInv z = piN (fromInteger (pi2 (z - 1)) + 1) (pi1 (z - 1))

-- | A x B = tau(A cross B), cut at m (exact: tau(a, b) >= a + b).
times :: Integer -> [Integer] -> [Integer] -> [Integer]
times m as bs = sort (nub [t | a <- as, b <- bs, let t = tau a b, t <= m])

tuples :: Int -> [Integer] -> [[Integer]]
tuples n xs = mapM (const xs) [1 .. n]

------------------------------------------------------------------------
-- Canonical indices (section 5.6)

dSet :: Integer -> [Integer]
dSet x = [z | z <- [0 .. 64], testBit x (fromInteger z)]

canonical :: [Integer] -> Integer
canonical xs = sum [2 ^ x | x <- nub xs]

subsetsOf :: [a] -> [[a]]
subsetsOf [] = [[]]
subsetsOf (x : xs) = let r = subsetsOf xs in r ++ map (x :) r

------------------------------------------------------------------------
-- Model sets and model computations

-- | A pseudo-random sequence (a linear congruential generator).
lcg :: Integer -> [Integer]
lcg seed = tail (iterate (\s -> (s * 1103515245 + 12345) `mod` 2147483648) seed)

isPrime :: Integer -> Bool
isPrime n = n >= 2 && all (\d -> n `mod` d /= 0) (takeWhile (\d -> d * d <= n) [2 ..])

modelSets :: [(String, Integer -> Bool)]
modelSets =
  [ ("even", even)
  , ("prime", isPrime)
  , ("square", \x -> x == (floor (sqrt (fromInteger x :: Double) :: Double) :: Integer) ^ (2 :: Int))
  , ("x mod 7 in {2, 3}", \x -> x `mod` 7 `elem` [2, 3]) ]

-- | Theorem I, case (iii): f(0) = mu y [g(y) = 1], f(x + 1) = mu y [g(y)
-- = 1 and f(x) < y], for the characteristic function g of an infinite set.
increasingEnum :: (Integer -> Bool) -> [Integer]
increasingEnum p = go (head [y | y <- [0 ..], p y])
  where go v = v : go (head [y | y <- [0 ..], p y, v < y])

-- | Theorem I, case (ii): A = {n_0 < ... < n_k}, f(x) = n_x for x <= k,
-- n_k for k < x.
finiteEnum :: [Integer] -> Integer -> Integer
finiteEnum ns x = let k = fromIntegral (length ns) - 1
                  in if x <= k then ns !! fromInteger x else ns !! fromInteger k

-- | Theorem V: the halting times of a model psi.
type Steps = Integer -> Maybe Integer

-- | The list at stage s >= 1: the k <= s - 1 whose computation stops
-- within s steps (stage n + 1 runs n + 1 steps of psi(0), ..., psi(n)).
stage :: Steps -> Integer -> [Integer]
stage hs s = [k | k <- [0 .. s - 1], Just t <- [hs k], t <= s]

-- | eta of p. 85 (for nonempty Arg psi), given the list of each stage:
-- eta(0) is the first element listed, eta(x + 1) the least y listed at
-- stage x + 1 and not among eta(0), ..., eta(x), else eta(0).
etaFrom :: (Integer -> [Integer]) -> [Integer]
etaFrom listAt = e0 : go 1 [e0]
  where
    e0 = head (concatMap listAt [1 ..])
    go x prev = case [y | y <- sort (listAt x), y `notElem` prev] of
      (y : _) -> y : go (x + 1) (prev ++ [y])
      [] -> e0 : go (x + 1) prev

eta :: Steps -> [Integer]
eta hs = etaFrom (stage hs)

-- | The misreading: only the elements first listed at stage x + 1.
etaNew :: Steps -> [Integer]
etaNew hs = etaFrom (\s -> [k | k <- stage hs s, k `notElem` stage hs (s - 1)])

modelSteps :: [(String, Steps, [Integer])]
modelSteps =
  [ ("psi(0) needs 3 steps, psi(1), psi(2) 1 step, psi(5k) 5k + 2 steps",
      \k -> case k of
              0 -> Just 3
              1 -> Just 1
              2 -> Just 1
              _ | k `mod` 5 == 0 -> Just (k + 2)
                | otherwise -> Nothing,
      [0, 1, 2] ++ [5, 10 .. 60])
  , ("even k, k mod 7 + 1 steps", \k -> if even k then Just (k `mod` 7 + 1) else Nothing, [0, 2 .. 60])
  , ("all k, 1 step", const (Just 1), [0 .. 60])
  , ("k = 3 only, 40 steps", \k -> if k == 3 then Just 40 else Nothing, [3])
  , ("k >= 20, k^2 mod 37 steps", \k -> if k >= 20 then Just (k * k `mod` 37) else Nothing, [20 .. 60]) ]

-- | A uniformization step of theorem XVI: from an enumeration without
-- repetitions of W_z (codes <x, y>), A_z = the <x, y> preceding every
-- <x, y'> with y' /= y.
uniformize :: [Integer] -> [Integer]
uniformize ws = [w | (i, w) <- zip [0 :: Int ..] ws,
                     and [i < j | (j, w') <- zip [0 ..] ws, pi1 w' == pi1 w, pi2 w' /= pi2 w]]

singleValued :: [Integer] -> Bool
singleValued ws = and [pi2 a == pi2 b | a <- ws, b <- ws, pi1 a == pi1 b]

argSet :: [Integer] -> [Integer]
argSet ws = sort (nub (map pi1 ws))

-- | Model enumerations without repetitions of finite sets of codes.
randomEnums :: [[Integer]]
randomEnums = take 300 (go (lcg 2026))
  where
    go rs = let (n : rest) = rs
                len = fromInteger (n `mod` 14)
                (ps, rest') = splitAt (2 * len) rest
                codes = nub [tau (a `mod` 5) (b `mod` 4) | [a, b] <- chunks ps]
            in codes : go rest'
    chunks (a : b : r) = [a, b] : chunks r
    chunks _ = []

------------------------------------------------------------------------

main :: IO ()
main = do
  c <- newCounter

  group c "p. 89: tau, the listing of pairs and one-one onto"
    ( [("numerator even, tau = T(x + y) + x " ++ show (x, y),
        even (numerator x y) && tau x y == tri (x + y) + x && tau x y >= x + y)
      | x <- [0 .. 60], y <- [0 .. 60]]
      ++ [("0, ..., 7 code <0,0>, <0,1>, <1,0>, <0,2>, <1,1>, <2,0>, <0,3>, <1,2>",
           map untau [0 .. 7] == [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0), (0, 3), (1, 2)]
           && [tau 0 0, tau 0 1, tau 1 0, tau 0 2, tau 1 1, tau 2 0, tau 0 3, tau 1 2] == [0 .. 7])]
      ++ [("diagonal x + y = " ++ show s ++ " fills [T(s), T(s + 1))",
           sort [tau x (s - x) | x <- [0 .. s]] == [tri s .. tri (s + 1) - 1])
         | s <- [0 .. 80]] )

  group c "p. 90: pi_1, pi_2 invert tau"
    ( [("tau(pi_1 z, pi_2 z) = z, z = " ++ show z, tau (pi1 z) (pi2 z) == z) | z <- [0 .. 5000]]
      ++ [("pi(tau(x, y)) = (x, y) " ++ show (x, y), untau (tau x y) == (x, y))
         | x <- [0 .. 40], y <- [0 .. 40]] )

  group c "p. 90: tau^n, pi_i^n"
    ( [("tau^2 = tau " ++ show (x, y), tauN [x, y] == tau x y) | x <- [0 .. 30], y <- [0 .. 30]]
      ++ [("pi_1^2 = pi_1, pi_2^2 = pi_2, z = " ++ show z, piN 2 z == [pi1 z, pi2 z]) | z <- [0 .. 2000]]
      ++ [("tau^" ++ show n ++ "(pi^" ++ show n ++ "(z)) = z, z = " ++ show z, tauN (piN n z) == z)
         | n <- [1 .. 4], z <- [0 .. 1500]]
      ++ [("pi^n(tau^n(t)) = t, t = " ++ show t, piN (length t) (tauN t) == t)
         | n <- [1 .. 4], t <- tuples n [0 .. 5]]
      ++ [("tau^" ++ show n ++ " one-one on [0..5]^n", let cs = map tauN (tuples n [0 .. 5])
                                                         in length (nub cs) == length cs)
         | n <- [1 .. 4]] )

  group c "p. 90: example 1, <2, 1, 0> = <<2, 1>, 0> = <8, 0> = 44"
    [ ("<2, 1> = 8", tau 2 1 == 8)
    , ("<8, 0> = 44", tau 8 0 == 44)
    , ("tau^3(2, 1, 0) = 44", tauN [2, 1, 0] == 44) ]

  let m = 4000
      cut p = [x | x <- [0 .. m], p x]
      -- tau(a, b) >= a + b, so the cut at m is exact at every level
      fourth as = sort (nub [ t | a <- as, b <- as, tau a b <= m, d <- as, tau (tau a b) d <= m
                                , e <- as, let t = tauN [a, b, d, e], t <= m ])
  group c "p. 90: example 2, tau^4(A^4) = ((A x A) x A) x A (elements <= 4000)"
    [ ("A = " ++ name, fourth as == times m (times m (times m as as) as) as)
    | (name, as) <- [ ("{0, 2, 3}", [0, 2, 3]), ("{1, 5}", [1, 5]), ("{0}", [0])
                    , ("even", cut even), ("prime", cut isPrime) ] ]

  group c "p. 90: A x B x C means (A x B) x C; exercise 5-14 (a) on examples"
    ( [ ("tau^3(A cross B cross C) = (A x B) x C " ++ show (as, bs, cs),
         sort (nub [t | a <- as, b <- bs, d <- cs, let t = tauN [a, b, d], t <= m])
           == times m (times m as bs) cs)
      | (as, bs, cs) <- [([0, 1], [2], [3, 4]), ([5], [0 .. 3], [1]), ([0 .. 4], [0 .. 4], [0 .. 4])] ]
      ++ [ ("not associative: {1} x ({0} x {0}) = {2}, ({1} x {0}) x {0} = {5}",
            times m [1] (times m [0] [0]) == [2] && times m (times m [1] [0]) [0] == [5])
         , ("not commutative: {0} x {1} = {1}, {1} x {0} = {2}",
            times m [0] [1] == [1] && times m [1] [0] == [2]) ]
      ++ [ ("distributive over union " ++ show (as, bs, cs),
            times m as (sort (nub (bs ++ cs))) == sort (nub (times m as bs ++ times m as cs))
            && times m (sort (nub (as ++ bs))) cs == sort (nub (times m as cs ++ times m bs cs)))
         | as <- subsetsOf [0, 1, 3], bs <- subsetsOf [0, 2], cs <- subsetsOf [1, 4] ] )

  group c "p. 97: canonical indices D_x, D_13 = {0, 2, 3}"
    ( [ ("13 = 1101 in binary, D_13 = {0, 2, 3}", dSet 13 == [0, 2, 3] && canonical [0, 2, 3] == 13) ]
      ++ [("the canonical index of D_x is x, x = " ++ show x, canonical (dSet x) == x) | x <- [0 .. 4096]]
      ++ [("D of the canonical index of " ++ show s, dSet (canonical s) == s) | s <- subsetsOf [0 .. 10]]
      ++ [("empty set: canonical index 0", canonical [] == 0 && null (dSet 0))] )

  group c "p. 97: theorem XV (a), the cardinality of D_x"
    [("|D_x| = number of binary ones, x = " ++ show x, fromIntegral (length (dSet x)) == popCount x)
    | x <- [0 .. 4096 :: Integer]]

  group c "p. 119: the canonical indices of {f'(m_0)} and {f'(m_0), f'(m_1)}"
    ( [("{a}: 2^a, a = " ++ show a, canonical [a] == 2 ^ a && dSet (2 ^ a) == [a]) | a <- [0 .. 40]]
      ++ [("{a, b}: 2^a + 2^b " ++ show (a, b), dSet (2 ^ a + 2 ^ b) == sort [a, b])
         | a <- [0 .. 20], b <- [0 .. 20], a /= b] )

  let allTuples = [] : concat [tuples n [0 .. 4] | n <- [1 .. 4]]
  group c "p. 98: tau^*, its two forms, one-one onto; exercise 5-30"
    ( [("tau(tau^n(x), n - 1) + 1 = <x_1, ..., x_n, n - 1> + 1, " ++ show t, tauStar t == tauStar' t)
      | t <- allTuples]
      ++ [("tau^* one-one on tuples of length <= 4 over [0..4]",
           length (nub (map tauStar allTuples)) == length allTuples)]
      ++ [("inverse: tau^*(inv z) = z, z = " ++ show z, tauStar (tauStarInv z) == z) | z <- [0 .. 3000]]
      ++ [("inverse: inv(tau^*(t)) = t, " ++ show t, tauStarInv (tauStar t) == t) | t <- allTuples]
      ++ [("tau^*(<x>) = <x, 0> + 1, x = " ++ show x, tauStar [x] == tau x 0 + 1) | x <- [0 .. 50]] )

  group c "theorem I, cases (ii) and (iii): enumerations of model sets"
    ( [ ("case (ii), A = " ++ show ns, sort (nub (map (finiteEnum ns) [0 .. 30])) == ns)
      | ns <- [[0], [7], [1, 4, 9], [0, 2, 3, 10, 11]] ]
      ++ [ ("case (iii), " ++ name ++ ": increasing, values = A below 3000",
            let vs = takeWhile (<= 3000) (increasingEnum p)
            in and (zipWith (<) vs (tail vs)) && vs == [x | x <- [0 .. 3000], p x])
         | (name, p) <- modelSets ] )

  group c "theorem II: the zigzag search f(0), g(0), f(1), g(1), ..."
    [ (name ++ ", x = " ++ show x, zigzag x == p x)
    | (name, p) <- modelSets
    , let fs = increasingEnum p
          gs = increasingEnum (not . p)
          zigzag x = head [b | (v, b) <- concat [[(f, True), (g, False)] | (f, g) <- zip fs gs], v == x]
    , x <- [0 .. 400] ]

  group c "theorem III: the decision procedures of the proof of <="
    ( [ ("(a), nondecreasing enumeration with repetitions, " ++ name ++ ", x = " ++ show x,
         let fs = concat [replicate (fromInteger (v `mod` 3) + 1) v | v <- increasingEnum p]
             seen = takeWhile (<= x) fs
         in (x `elem` seen) == p x)
      | (name, p) <- modelSets, x <- [0 .. 400] ]
      ++ [ ("(b), increasing f: x in A iff x in {f(0), ..., f(x)}, " ++ name ++ ", x = " ++ show x,
            (x `elem` take (fromInteger x + 1) (increasingEnum p)) == p x)
         | (name, p) <- modelSets, x <- [0 .. 400] ] )

  group c "theorem IV: g(x + 1) = f(mu y [f(y) > g(x)]) on model enumerations"
    [ (name ++ ": g increasing, values of f",
       let gs = take 40 (go (f 0))
           go v = v : go (f (head [y | y <- [0 ..], f y > v]))
           vals = map f [0 .. 5000]
       in and (zipWith (<) gs (tail gs)) && all (`elem` vals) gs)
    | (name, f) <- [ ("f(n) = 3 pi_2(n) + pi_1(n) mod 3", \n -> 3 * pi2 n + pi1 n `mod` 3)
                   , ("f(n) = (7n mod 11) + 2 (n div 11)", \n -> (7 * n) `mod` 11 + 2 * (n `div` 11))
                   , ("f(n) = pi_1(n)^2 + pi_2(n)", \n -> pi1 n ^ (2 :: Int) + pi2 n) ] ]

  group c "theorem V: eta lists Arg psi (stages re-add every halted k)"
    ( concat
      [ [ (name ++ ": eta(0..400) in Arg psi", all (\v -> hs v /= Nothing) es)
        , (name ++ ": " ++ show ks ++ " are values of eta(0..400)", all (`elem` es) ks)
        , (name ++ ": the lists of stages 1..200 grow and exhaust Arg psi below 60",
           and [all (`elem` stage hs (s + 1)) (stage hs s) | s <- [1 .. 199]]
           && sort (nub (concatMap (stage hs) [1 .. 200])) == [k | k <- [0 .. 199], Just t <- [hs k], t <= 200]
           && all (`elem` concatMap (stage hs) [1 .. 200]) ks) ]
      | (name, hs, ks) <- modelSteps, let es = take 401 (eta hs) ] )

  group c "theorem V: refuted misreading (only the elements first listed at stage x + 1)"
    [ ( "psi(0) 3 steps, psi(1), psi(2) 1 step: 0 and 2 are first listed at stage 3, only 0 is taken; "
        ++ "2 never appears in eta'(0..400)"
      , let (_, hs, _) = head modelSteps
        in stage hs 3 == [0, 1, 2] && stage hs 2 == [1]
           && 2 `notElem` take 401 (etaNew hs) && 2 `elem` take 401 (eta hs) ) ]

  group c "exercise 5-3 (a): the isomorphism of two infinite coinfinite recursive sets"
    [ (na ++ " to " ++ nb,
       let h x = if pa x then eb !! pos pa x else ecb !! pos (not . pa) x
           pos p x = length (filter p [0 .. x - 1])
           eb = filter pb [0 ..]
           ecb = filter (not . pb) [0 ..]
           img = map h [0 .. 600]
       in length (nub img) == length img
          && and [pa x == pb (h x) | x <- [0 .. 600]]
          && all (`elem` img) [0 .. 250])
    | (na, pa) <- [("even", even), ("x mod 3 = 0", \x -> x `mod` 3 == 0)]
    , (nb, pb) <- [("x mod 5 in {1, 2}", \x -> x `mod` 5 `elem` [1, 2]), ("x mod 4 = 3", \x -> x `mod` 4 == 3)] ]

  group c "exercise 5-22: the codes of R = {1} cross N and Q = N cross {1}"
    [ ("tau^2(R) = {<1, y>}, tau^2(Q) = {<x, 1>}: about 200 elements each below 20000, different",
       let r = [tau 1 y | y <- [0 .. 300], tau 1 y <= 20000]
           q = [tau x 1 | x <- [0 .. 300], tau x 1 <= 20000]
       in length r > 150 && length q > 150 && length r < 1000 && length q < 1000
          && r /= q && (tau 1 0 `notElem` q) && (tau 0 1 `notElem` r)) ]

  group c "theorem XVI: A_z of the proof satisfies (i)-(iv) on model enumerations"
    ( concat
      [ [ ("(i) single-valued, " ++ show ws, singleValued a)
        , ("(ii) A_z in W_z", all (`elem` ws) a)
        , ("(iii) Arg A_z = Arg W_z", argSet a == argSet ws)
        , ("(iv) W_z single-valued => A_z = W_z", not (singleValued ws) || sort a == sort ws) ]
      | ws <- randomEnums, let a = uniformize ws ]
      ++ [ ("the models include W_z that are not single-valued (" ++ show n ++ " of 300)", n > 100)
         | let n = length (filter (not . singleValued) randomEnums) ] )

  group c "theorem XVII: A' = psi^(-1)(0), B' = psi^(-1)(1) on model sets"
    ( concat
      [ [ ("A' in A, B' in B " ++ show (as, bs), all (`elem` as) a' && all (`elem` bs) b')
        , ("A' union B' = A union B", sort (a' ++ b') == sort (nub (as ++ bs)))
        , ("A' disjoint B'", null [x | x <- a', x `elem` b']) ]
      | (as, bs) <- zip (map (nub . map pi1) (take 60 randomEnums)) (map (nub . map pi2) (drop 60 randomEnums))
      , let enumC = interleave [tau x 0 | x <- as] [tau x 1 | x <- bs]
            c' = uniformize enumC
            a' = [pi1 w | w <- c', pi2 w == 0]
            b' = [pi1 w | w <- c', pi2 w == 1] ] )

  group c "theorem XVIII: psi(z) by uniformizing {<z, w> | (exists u) [u in W_w & w in W_z]}"
    ( concat
      [ [ ("psi(" ++ show z ++ ") defined iff some w in W_z has W_w nonempty",
           (lookup z psi /= Nothing) == any (\w -> not (null (fam w))) (fam z))
        , ("psi(" ++ show z ++ ") in W_z and W_psi(z) nonempty",
           maybe True (\w -> w `elem` fam z && not (null (fam w))) (lookup z psi)) ]
      | (k, fam) <- zip [0 :: Int ..] families
      , let order = sortOn snd [ (tau z w, (t, z, w, k)) | z <- [0 .. 9], (t, w) <- zip [0 :: Integer ..] (fam z)
                               , not (null (fam w)) ]
            psi = [(pi1 v, pi2 v) | v <- uniformize (map fst order)]
      , z <- [0 .. 9] ]
      ++ [ ("the families give both defined and undefined psi(z)",
            let defined = [ any (\w -> not (null (fam w))) (fam z) | fam <- families, z <- [0 .. 9] ]
            in or defined && not (and defined)) ] )

  finish c "ch05-07-codings"
  where
    interleave (a : as) bs = a : interleave bs as
    interleave [] bs = bs
    families = [ \w -> if w > 9 then [] else take (fromInteger ((r `div` (w + 1)) `mod` 4)) [(r * (w + 3) + 7 * i) `mod` 10 | i <- [0 ..]]
               | r <- take 40 (lcg 7) ]
