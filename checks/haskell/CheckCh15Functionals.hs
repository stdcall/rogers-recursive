-- | Checks of chapter 15, § 15.3 (printed pp. 459-471) and of the hint of
-- exercise 15-36 (pp. 476-477): functionals defined by enumeration
-- operators, the no-counterexample interpretation.  Scope ch15-16.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh15Functionals.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh15Functionals.hs
--      [--verbose]
--
-- Model: partial functions phi on the arguments {0, 1} with values
-- {0, 1, 2} (16 functions, 9 of them total on the model), tau(phi) the
-- set of codes <a, b> = tau(a, b) (§ 5.3); an enumeration operator is a
-- finite list W of pairs (x, D), Phi(A) = {x | (x, D) in W, D subset A}
-- (§ 9.7).  On the model "total" means defined on {0, 1}; every partial
-- function extends to a total one, which is all the arguments below use.
--
-- What is checked, and where the expected values come from:
--
-- * The weak domain of the functional F of Phi (p. 459), in the corrected
--   reading {phi | Phi(tau(phi)) has at most one element} and in the
--   printed one {phi | Phi(tau(phi)) is not empty}.  Corrected: exercise
--   15-26 (a) (ex:recursive-functional-weak-domain: F is recursive iff the
--   weak domain contains all total functions) holds for random W, and (b)
--   (strong domain everything => F constant) for random and constructed
--   W; "F not recursive" is "some Phi(tau(phi)) has two elements", as the
--   proof of th:effective-operations-recursive-functionals (b)(i) uses it;
--   on operators with pairs as outputs, "some <phi, x> is outside the
--   weak domain" is "Phi(tau(phi)) is not single-valued", the
--   correspondence with partial recursive operators of p. 460 (§ 9.8).
--   Printed reading, refuted: the operator with Phi(A) = {0} when A has a
--   code <0, b> (empty otherwise) is nonempty on every total function and
--   empty on the nowhere defined one, so 15-26 (a) fails; the empty
--   operator has no two-element value and still is not "recursive"; the
--   constant operator {0, 1} is "recursive" with no strongly defined
--   value, so psi(x) of the proof of (a) does not exist; on pair outputs
--   the printed reading makes an operator undefined where it is
--   single-valued.
-- * The no-counterexample interpretation (p. 470): on all relations R on
--   a domain of 2 elements and on random relations on 3 elements,
--   (exists x)(forall y)(exists z)(forall w) R <=> (forall f)(forall g)
--   (exists x)(exists z) R(x, f(x), z, g(x, z)) (the first and the fourth
--   lines) <=> the fifth line with a constant F (hence with F depending on
--   f only, as printed; a constant functional is recursive).
-- * The hint of ex:effective-maps-recursive-reals (15-36): intervals of
--   length 1/2^z for z = 0, ..., Z - 1 have total length 2 - 2^(1 - Z),
--   more than 1 once Z >= 2 (printed, refuted); with 1/2^(z + 1)
--   (corrected) the total is 1 - 2^(-Z) <= 1; an open interval of length
--   1/2^(z + 1) centred on a rational interval shorter than 1/2^(z + 1)
--   contains it (condition (iii) unchanged); the bound "length 3" of the
--   hint: 1 + (2 - 2^(-k)) < 3, while with the printed lengths
--   (2 - 2^(1 - Z)) + (2 - 2^(-k)) > 3 for Z, k >= 2.
--
-- Not established: recursiveness of anything; the theorems beyond the
-- finite models; the step of th:friedberg-effective-operation (choice of
-- k) is checked in checks/lean/RogersRecursive/Ch15_16Functionals.lean.
module Main (main) where

import Ch08Coding
import Data.Bits (testBit)
import Data.List (nub)
import Data.Ratio ((%))
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "15.3 p. 459: weak domain, corrected reading (ex. 15-26)" correctedChecks
  group c "15.3 p. 459: weak domain, printed reading refuted" printedChecks
  group c "15.3 p. 460: correspondence with partial recursive operators" operatorChecks
  group c "15.3 p. 470: no-counterexample interpretation" nciChecks
  group c "15.4 ex. 15-36: total length of the covering (p. 476)" coverChecks
  finish c "ch15-functionals"

-- * Partial functions and enumeration operators

type PF = [(Integer, Integer)]

partials :: [PF]
partials = [concat [p0, p1] | p0 <- opt 0, p1 <- opt 1]
  where
    opt a = [] : [[(a, b)] | b <- [0 .. 2]]

totals :: [PF]
totals = [p | p <- partials, length p == 2]

graph :: PF -> [Integer]
graph p = [tau a b | (a, b) <- p]

type Op = [(Integer, [Integer])]

phiOp :: Op -> [Integer] -> [Integer]
phiOp w xs = sortNub [x | (x, d) <- w, all (`elem` xs) d]

codes :: [Integer]
codes = [tau a b | a <- [0, 1], b <- [0 .. 2]]

randomOp :: [Integer] -> Gen -> (Op, Gen)
randomOp outs g0 =
  let (k, g1) = below 5 g0
   in draws (k + 1) entry g1
  where
    entry g =
      let (x, g1) = pick outs g
          (d, g2) = subsetOf 25 codes g1
       in ((x, d), g2)

ops :: [Op]
ops = fst (draws 3000 (randomOp [0, 1, 2]) (mkGen 1503))

size :: Op -> PF -> Int
size w p = length (phiOp w (graph p))

correctedChecks :: [(String, Bool)]
correctedChecks =
  [ ("15-26 (a) for " ++ show w,
     all (\f -> size w f <= 1) totals == all (\p -> size w p <= 1) partials)
  | w <- ops ]
    ++ [ ("15-26 (b) for " ++ show w, constantIfStrong w) | w <- ops ++ constOps ]
    ++ [ ("some strongly total operators", length (filter strongAll constOps) == length constOps) ]
  where
    strongAll w = all (\p -> size w p == 1) partials
    constantIfStrong w =
      not (strongAll w) || length (nub [phiOp w (graph p) | p <- partials]) == 1
    constOps = [ (cv, []) : [(cv, d) | (_, d) <- w] | w <- take 300 ops, cv <- [0, 1, 2] ]

printedChecks :: [(String, Bool)]
printedChecks =
  [ ("Phi(A) = {0} if <0, b> in A: nonempty on all total functions",
     all (\f -> size w0 f > 0) totals)
  , ("... but empty on the nowhere defined function", size w0 [] == 0)
  , ("the empty operator has no two-element value", all (\p -> size [] p <= 1) partials)
  , ("... yet its printed weak domain is empty", not (any (\p -> size [] p > 0) partials))
  , ("constant {0, 1}: printed weak domain everything",
     all (\p -> size wc p > 0) partials)
  , ("... and no strongly defined value", all (\p -> size wc p == 2) partials)
  ]
  where
    w0 = [(0, [tau 0 b]) | b <- [0 .. 2]]
    wc = [(0, []), (1, [])]

-- | Operators with pairs <x, y> as outputs, x in {0, 1}, y in {0, 1, 2}.
operatorChecks :: [(String, Bool)]
operatorChecks =
  [ ("corrected reading for " ++ show w, all (corrected w) partials) | w <- pairOps ]
    ++ [ ("printed reading undefined on a single-valued output",
          any (\p -> printedUndefined [] p && singleValued (phiOp [] (graph p))) partials) ]
  where
    pairOps = fst (draws 1500 (randomOp codes) (mkGen 460))
    values w p x = [b | z <- phiOp w (graph p), let (a, b) = untau z, a == x]
    singleValued zs = and [ b == b' | z <- zs, z' <- zs
                          , let (a, b) = untau z, let (a', b') = untau z', a == a' ]
    corrected w p =
      any (\x -> length (values w p x) > 1) [0, 1] == not (singleValued (phiOp w (graph p)))
    printedUndefined w p = any (\x -> null (values w p x)) [0, 1]

-- * The no-counterexample interpretation

nciChecks :: [(String, Bool)]
nciChecks =
  [ ("|D| = 2, R = " ++ show m, agree 2 (\x y z w -> testBit m (fromIntegral (idx2 x y z w))))
  | m <- [0 .. 65535 :: Integer] ]
    ++ [ ("|D| = 3, random R " ++ show mask, agree 3 (rel3 mask))
       | mask <- fst (draws 20 randomRel (mkGen 470)) ]
    ++ [ ("both truth values met for |D| = 3",
          length (nub [line1 3 (rel3 mask) | mask <- fst (draws 20 randomRel (mkGen 470))]) == 2) ]
    ++ [ ("both truth values met for |D| = 2",
          length (nub [line1 2 (\x y z w -> testBit m (fromIntegral (idx2 x y z w)))
                      | m <- [0, 1, 65535 :: Integer]]) == 2) ]
  where
    idx2 :: Int -> Int -> Int -> Int -> Int
    idx2 x y z w = x * 8 + y * 4 + z * 2 + w
    randomRel g0 =
      let (p, g1) = pick [50, 70, 85, 95] g0
          (bits, g2) = subsetOf p [0 .. 80 :: Int] g1
       in (sum [2 ^ b | b <- bits] :: Integer, g2)
    rel3 mask x y z w = testBit mask (x * 27 + y * 9 + z * 3 + w)
    agree n r = let l1 = line1 n r in l1 == line4 n r && l1 == line5 n r

type Rel = Int -> Int -> Int -> Int -> Bool

dom :: Int -> [Int]
dom n = [0 .. n - 1]

line1 :: Int -> Rel -> Bool
line1 n r = or [and [or [and [r x y z w | w <- dom n] | z <- dom n] | y <- dom n] | x <- dom n]

-- | All functions f : D -> D and g : D x D -> D as tables.
funs1 :: Int -> [Int -> Int]
funs1 n = [\x -> t !! x | t <- sequence (replicate n (dom n))]

funs2 :: Int -> [Int -> Int -> Int]
funs2 n = [\x z -> t !! (x * n + z) | t <- sequence (replicate (n * n) (dom n))]

line4 :: Int -> Rel -> Bool
line4 n r = and [ or [r x (f x) z (g x z) | x <- dom n, z <- dom n]
                | f <- funs1 n, g <- funs2 n ]

-- | The fifth line with F constant x0 and G found by search.
line5 :: Int -> Rel -> Bool
line5 n r = or [ and [ or [r x0 (f x0) z (g x0 z) | z <- dom n] | f <- funs1 n, g <- funs2 n ]
               | x0 <- dom n ]

-- * Exercise 15-36

coverChecks :: [(String, Bool)]
coverChecks =
  [ ("printed lengths, Z = " ++ show z, sum (map printedLen [0 .. z - 1]) == 2 - 1 % 2 ^ (z - 1))
  | z <- [1 .. 30 :: Integer] ]
    ++ [ ("printed total exceeds 1 for Z = " ++ show z, sum (map printedLen [0 .. z - 1]) > 1)
       | z <- [2 .. 30 :: Integer] ]
    ++ [ ("corrected lengths, Z = " ++ show z,
          sum (map correctedLen [0 .. z - 1]) == 1 - 1 % 2 ^ z
            && sum (map correctedLen [0 .. z - 1]) <= 1)
       | z <- [1 .. 30 :: Integer] ]
    ++ [ ("centred interval of length 1/2^(z+1) contains [a, b], z = " ++ show z ++ " " ++ show (a, b),
          let l = correctedLen z; mid = (a + b) / 2 in mid - l / 2 < a && b < mid + l / 2)
       | z <- [0 .. 6 :: Integer], (a, b) <- samples z ]
    ++ [ ("length 3 suffices with total <= 1, k = " ++ show k, 1 + transition k < 3)
       | k <- [0 .. 30 :: Integer] ]
    ++ [ ("but not with the printed lengths, Z = k = " ++ show k,
          sum (map printedLen [0 .. k - 1]) + transition k > 3)
       | k <- [2 .. 30 :: Integer] ]
  where
    printedLen z = 1 % (2 ^ z) :: Rational
    correctedLen z = 1 % (2 ^ (z + 1)) :: Rational
    transition k = sum [1 % (2 ^ j) | j <- [0 .. k]] :: Rational
    samples z = [ (a, a + d) | a <- [0, 1 % 3, 5 % 7], d <- [0, correctedLen z / 2, correctedLen z * 99 / 100] ]
