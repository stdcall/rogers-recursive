-- | Checks of § 13.7, the Medvedev lattice (printed pp. 363-372).
-- Scope ch13-14.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh13Medvedev.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh13Medvedev.hs [--verbose]
--
-- Functions are total functions on N, compared on [0, 200); mass problems
-- are not modelled, only the recursive operators of the proofs.
--
-- * p. 366: n * f (h(0) = n, h(x + 1) = f(x)) and f ^ g (f = lambda x
--   [h(2x)], g = lambda x [h(2x + 1)]); c_A ^ c_B = c_(A (+) B) (p. 367,
--   A (+) B as in § 6.2).
-- * th:medvedev-lattice-distributive (pp. 367-368): Phi^1(f) =
--   Psi_m(f) ^ Psi_n(f); Phi^2(f) applies Psi_p or Psi_q to lambda x
--   [f(x + 1)] by f(0); the distributive law: the operators
--   f ^ (i * g) -> i * (f ^ g) and back map the elements of
--   A ^ (B v C) onto those of (A ^ B) v (A ^ C) and back, each output
--   value reading one input value.
-- * p. 366, the remark on A = B-bar (+) B: from any enumeration of A the
--   characteristic function c_A is computed (2x or 2x + 1 appears), so
--   the problems (1) and (2) of p. 365 are equivalent for such A.
-- * th:medvedev-embeddings (b) (p. 368): iota_A = {<x, x> | x in A}: an
--   enumeration of A gives one of tau(iota_A) by x -> tau(x, x), and back
--   by pi_1.
-- * p. 372, the definition of "not": not A = A -> 1 is 1 for A /= 1 and
--   0 for A = 1 (printed); with "or" the greatest lower bound and 0 the
--   least degree, not A or not not A = 0 for every A (three cases:
--   A = 0, 0 < A < 1, A = 1).  So the expression "not A or not not A" is
--   true in the sense of p. 372.  It is not a theorem of the
--   intuitionistic propositional calculus: on the Kripke frame r < a,
--   r < b with p true at a only, r forces neither not p nor not not p
--   (the frame is not strongly directed; A. Chagrov, M. Zakharyaschev,
--   Modal Logic, Clarendon Press, 1997, § 2.5, Proposition 2.37, and
--   Corollary 2.44 for the calculus).  This refutes the printed claim that
--   with "not" the true expressions are exactly the intuitionistic
--   theorems.  The classical tautologies of p. 372 are checked on the
--   two-element algebra {0, 1}.
--
-- Not established: the lattice properties of the degrees of difficulty,
-- the soundness theorem of the intuitionistic calculus for Kripke frames
-- (quoted), Medvedev's theorems.
module Main (main) where

import Ch08Coding (below, mkGen, pi1, pi2, shuffle, tau)
import Data.Word (Word64)
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "p. 366 n * f and f ^ g" opsChecks
  group c "th:medvedev-lattice-distributive operators" distChecks
  group c "p. 366 remark A = B-bar (+) B" joinChecks
  group c "th:medvedev-embeddings (b) iota_A" iotaChecks
  group c "p. 372 not A or not not A" negationChecks
  finish c "ch13-medvedev"

type Fn = Integer -> Integer

star :: Integer -> Fn -> Fn
star n f x = if x == 0 then n else f (x - 1)

wedge :: Fn -> Fn -> Fn
wedge f g x = if even x then f (x `div` 2) else g (x `div` 2)

range' :: [Integer]
range' = [0 .. 199]

eqOn :: Fn -> Fn -> Bool
eqOn f g = all (\x -> f x == g x) range'

randFn :: Word64 -> Fn
randFn seed x = toInteger (fst (below 5 (mkGen (seed * 1299709 + fromInteger x))))

randSet :: Word64 -> Integer -> Bool
randSet seed x = fst (below 2 (mkGen (seed * 15485863 + fromInteger x))) == 1

charF :: (Integer -> Bool) -> Fn
charF a x = if a x then 1 else 0

joinSet :: (Integer -> Bool) -> (Integer -> Bool) -> Integer -> Bool
joinSet a b y = if even y then a (y `div` 2) else b (y `div` 2)

opsChecks :: [(String, Bool)]
opsChecks =
  [ ("(n * f)(0) = n, (n * f)(x + 1) = f(x), seed " ++ show s, star 3 f 0 == 3 && all (\x -> star 3 f (x + 1) == f x) range')
  | s <- [1 .. 20], let f = randFn s
  ]
    ++ [ ("f ^ g has the even part f and the odd part g, seed " ++ show s
         , all (\x -> wedge f g (2 * x) == f x && wedge f g (2 * x + 1) == g x) range' )
       | s <- [1 .. 20], let f = randFn s; g = randFn (s + 100)
       ]
    ++ [ ("c_A ^ c_B = c_(A (+) B), seed " ++ show s, eqOn (wedge (charF a) (charF b)) (charF (joinSet a b)))
       | s <- [1 .. 40], let a = randSet s; b = randSet (s + 500)
       ]

-- | Model operators Psi: shifts and pointwise maps (each a recursive operator).
psiOps :: [Fn -> Fn]
psiOps = [\f x -> f (x + 1), \f x -> f (2 * x), \f x -> f x + 1, \f x -> f (x `div` 2) * 2]

distChecks :: [(String, Bool)]
distChecks =
  [ ("Phi^1(f) = Psi_m(f) ^ Psi_n(f), seed " ++ show s
    , eqOn phi1 (wedge (pm f) (pn f)) )
  | s <- [1 .. 10], pm <- psiOps, pn <- psiOps
  , let f = randFn s
        phi1 x = if even x then pm f (x `div` 2) else pn f (x `div` 2)
  ]
    ++ [ ( "Phi^2 on A v B uses Psi_p for 0 * g and Psi_q for 1 * h, seed " ++ show s
         , eqOn (phi2 (star 0 g)) (pp g) && eqOn (phi2 (star 1 h)) (pq h) )
       | s <- [1 .. 10], pp <- psiOps, pq <- psiOps
       , let g = randFn s
             h = randFn (s + 50)
             phi2 f = (if f 0 == 0 then pp else pq) (\x -> f (x + 1))
       ]
    ++ [ ( "f ^ (i * g) -> i * (f ^ g) and back, i = " ++ show i ++ ", seed " ++ show s
         , eqOn (theta1 (wedge f (star i g))) (star i (wedge f g))
             && eqOn (theta2 (star i (wedge f g))) (wedge f (star i g)) )
       | s <- [1 .. 30], i <- [0, 1]
       , let f = randFn s
             g = randFn (s + 70)
       ]
  where
    -- (theta1 F)(0) = F(1); (theta1 F)(x + 1) = (f ^ g)(x) with f(k) = F(2k),
    -- g(k) = F(2k + 3).
    theta1 bigF x
      | x == 0 = bigF 1
      | even (x - 1) = bigF (x - 1)
      | otherwise = bigF (x + 1)
    -- (theta2 H)(2k) = (f ^ g)(2k) = H(2k + 1); (theta2 H)(1) = H(0);
    -- (theta2 H)(2k + 3) = H(2k + 2).
    theta2 bigH x
      | even x = bigH (x + 1)
      | x == 1 = bigH 0
      | otherwise = bigH (x - 1)

-- | From an enumeration of A = B-bar (+) B decide A.
decideFromEnum :: [Integer] -> Integer -> Maybe Bool
decideFromEnum enum y =
  let x = y `div` 2
   in case [v | v <- enum, v == 2 * x || v == 2 * x + 1] of
        (v : _) -> Just (v == y)
        [] -> Nothing

joinChecks :: [(String, Bool)]
joinChecks =
  [ ( "an enumeration of B-bar (+) B decides it, seed " ++ show s
    , all (\y -> decideFromEnum enum y == Just (aSet y)) [0 .. 2 * n - 1] )
  | s <- [1 .. 60]
  , let n = 60
        b = randSet s
        aSet = joinSet (not . b) b
        enum = fst (shuffle [y | y <- [0 .. 2 * n - 1], aSet y] (mkGen (s + 9)))
  ]

iotaChecks :: [(String, Bool)]
iotaChecks =
  [ ( "x -> tau(x, x) and pi_1 translate the enumerations, seed " ++ show s
    , map pi1 (map (\x -> tau x x) enum) == enum
        && all (\x -> pi2 (tau x x) == x) enum )
  | s <- [1 .. 30]
  , let enum = fst (shuffle [x | x <- [0 .. 80], randSet s x] (mkGen s))
  ]

-- * not A or not not A

-- | Degrees: 0 (least), a middle degree, 1 (greatest); "or" is the greatest
-- lower bound.
data D = Zero | Mid | One deriving (Eq, Show)

glb :: D -> D -> D
glb Zero _ = Zero
glb _ Zero = Zero
glb Mid _ = Mid
glb _ Mid = Mid
glb One One = One

-- | The printed values of not A = A -> 1 (p. 372).
neg :: D -> D
neg One = Zero
neg _ = One

-- | Kripke frame r < a, r < b; upsets as lists of worlds.
data W = R | Wa | Wb deriving (Eq, Show)

worlds :: [W]
worlds = [R, Wa, Wb]

above :: W -> [W]
above R = [R, Wa, Wb]
above w = [w]

kNeg :: [W] -> [W]
kNeg u = [w | w <- worlds, all (`notElem` u) (above w)]

upsets :: [[W]]
upsets = [u | u <- map (\bs -> [w | (w, True) <- zip worlds bs]) (sequence (replicate 3 [False, True])), all (\w -> all (`elem` u) (above w)) u]

negationChecks :: [(String, Bool)]
negationChecks =
  [ ("not A or not not A = 0 for A = " ++ show a, glb (neg a) (neg (neg a)) == Zero) | a <- [Zero, Mid, One] ]
    ++ [ ("not 0 = 1 and not 1 = 0 (0 /= 1)", neg Zero == One && neg One == Zero) ]
    ++ [ ("p = {a} is an upset", [Wa] `elem` upsets)
       , ("r does not force not p", R `notElem` kNeg [Wa])
       , ("r does not force not not p", R `notElem` kNeg (kNeg [Wa]))
       , ("r does not force not p or not not p", R `notElem` (kNeg [Wa] ++ kNeg (kNeg [Wa])))
       , ("the frame is not strongly directed (a and b have no common successor)", null [w | w <- above Wa, w `elem` above Wb])
       ]
    ++ [ ("on the two-element algebra not p or not not p holds, p = " ++ show p, (not p || not (not p)) == True) | p <- [False, True] ]
    ++ [ ("on the two-element algebra Peirce's law ((p -> q) -> p) -> p holds, " ++ show (p, q), imp (imp (imp p q) p) p)
       | p <- [False, True], q <- [False, True]
       ]
  where
    imp x y = not x || y
