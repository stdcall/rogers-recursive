-- | Checks of chapter 14, §§ 14.1-14.8 (printed pp. 387-424), and of the
-- exercises 14-1 and 14-21.  Scope ch13-14.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh14Hierarchy.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh14Hierarchy.hs [--verbose]
--
-- * § 14.3, points 2 and 4 (p. 395): every pair of point 2 and point 4 is
--   equivalent on the domains {0}, {0, 1}, {0, 1, 2} for every F and G
--   (G without a); on the empty domain "(forall a) F => G" and
--   "(exists a)[F => G]" differ (point 2 needs a nonempty domain, N).
-- * The example of pp. 396-397, B = {z | W_z recursive}: the six formulas
--   of stage 2 (with the brackets as corrected on pp. 396, 397) and the
--   prefix forall-forall-forall-exists-exists of the second derivation
--   define the same set of z on finite models (T_1 a relation on two
--   indices, two arguments, two or three steps; all relations).
-- * The Tarski-Kuratowski algorithm on prefix skeletons: all derivations
--   of points 2-4 (pulling the quantifiers out of either side, a quantifier
--   of an antecedent or under a negation reversed) and contraction:
--   B = {z | W_z recursive}: the printed derivations give
--   E A E A E A (Sigma_6) and E A A A E E, the best class is Sigma_3;
--   {z | (exists y)[y in W_z^A & W_y^A infinite]}: Sigma_3;
--   R = {<u, z> | D_u subset W_z}: Pi_2, and Sigma_1 after the bounded
--   quantifier (forall x <= u) is dropped (x in D_u => x < u, checked for
--   u < 2^14); {z | W_z simple}: Pi_3; {z | W_z infinite}: Pi_2;
--   th:strong-hierarchy, part (a), n = k + 1: the form
--   E E E [E & Sigma_(k+1) & Pi_(k+1)] gives Sigma_(k+2) (k <= 4).
-- * ex:projection-complement-sequences: (a) CPPCP gives forall forall
--   exists on R, (b) CPPCPC gives it on not R; (c) PCP: exists forall on
--   not R; CCCP: forall on not R; PCPCPCP: exists forall exists forall on
--   not R; (d) shortest sequences for exists forall exists, exists forall
--   exists forall, forall (found by search).
-- * cor:pi-n-plus-two-sentence (p. 411): with Davis' form
--   (exists y)(forall u)(exists v_1) ... (exists v_k) for the r.e.
--   relation (exists x_n) T_n(f(n), z_2, x_1, ..., x_n) (n odd) or its
--   negation (n even), the Sigma_n form gives a Sigma_(n+2) prefix
--   (n <= 8, k = 1, 2, 4).  th:kreisel-shoenfield-wang (pp. 422-423):
--   Pi_(2n+2) = forall exists forall Sigma_(2n-1); U forall forall exists
--   Pi_(2n-2) contracts to U Pi_(2n), U forall forall exists Pi_(2n-1) to
--   U Pi_(2n+1) (n <= 5).
-- * § 14.3, p. 398, property 1 of bounded quantifiers, as corrected:
--   (forall a <= b)(exists c)(forall d) R(a, b, c, d) <=>
--   (exists c)(forall a <= b)(forall d) R(a, b, pi_(a+1)^(b+1)(c), d) on
--   random finite R (b <= 2), with pi_j^n of § 5.3 (1 <= j <= n).  As
--   printed, pi_a^b, the function pi_0^b does not exist and a b-tuple has
--   one component fewer than the b + 1 values of a.
-- * § 14.4, the editorial footnote of th:goedel-polynomial (p. 401):
--   alpha * beta = 0 <=> alpha = 0 or beta = 0, and, as corrected,
--   not (alpha = 0) <=> (exists c)(alpha * alpha = c + 1) for integers
--   |alpha| <= 60; as printed, (exists c)(alpha = c + 1) fails for
--   alpha = -1, e.g. for not (0 = 1) with gamma = 0 - 1.  The count of
--   variables of the footnote of p. 402: q = n + k + 3 = 8 for n = 1,
--   k = n + 3.
-- * § 14.7, p. 414: the printed formula for Fermat's theorem is false at
--   x = 0, y = z = 1, w = 3; with x > 0 & y > 0 (as corrected) there is
--   no solution with x, y <= 30, z <= 60, 3 <= w <= 6 (a finite search,
--   not Fermat's theorem).
-- * th:pi-two-u-form (p. 422): S = {<z, y> | phi_z(pi_1(y)) converges in
--   exactly pi_2(y) steps}: y -> pi_1(y) maps {y | S(z, y)} one-one onto
--   the domain of phi_z (model halting times).
-- * th:infinite-member-complete (p. 419): psi(0) = 0 if (exists x_3)
--   R(.., 0, x_3), psi(n + 1) = 0 if psi(n) is defined and (exists x_3)
--   R(.., n + 1, x_3): the domain of psi is the initial segment
--   {n | (forall m <= n)(exists x_3) R(.., m, x_3)} (model R).
-- * th:recursive-index-complete (pp. 419-421), the marker construction on
--   model enumerations: if every W_y, y in W_z, is finite, every marker
--   moves finitely often and for its last position x_n: x_n in A <=>
--   x_n in W_n; if W_(y*) is infinite (y* least), marker y* moves at every
--   new element of W_(y*), every number after the first position of a
--   marker attached after the last move of the markers below y* is in A
--   once its marker has moved on.  The model also has a number after the
--   first position of marker y* that stays outside A (a marker below y*
--   moved there late): "некоторый маркер" of p. 421 is a suitably late
--   marker, not necessarily y*.
-- * Rice-Shapiro, example 2 (p. 417): D_0 is empty, D_(u+1) is not, and
--   {a} = D_(2^a).
--
-- Not established: recursiveness, the hierarchy and completeness theorems,
-- Davis' and Goedel's theorems; the models are finite.
module Main (main) where

import Ch08Coding (below, dset, mkGen, pi1, pi2, piN, sortNub, tau, tauN)
import Data.Word (Word64)
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "14.3 points 2 and 4 on finite domains" rulesChecks
  group c "14.3 example of pp. 396-397 on finite models" chainChecks
  group c "14.3 Tarski-Kuratowski derivations" tkChecks
  group c "ex:projection-complement-sequences" opsChecks
  group c "cor:pi-n-plus-two-sentence and th:kreisel-shoenfield-wang prefixes" prefixChecks
  group c "14.3 bounded quantifiers (p. 398, p. 399)" boundedChecks
  group c "14.4 footnote of th:goedel-polynomial" footnoteChecks
  group c "14.7 Fermat's formula (p. 414)" fermatChecks
  group c "th:pi-two-u-form S(z, y)" uFormChecks
  group c "th:infinite-member-complete psi" psiChecks
  group c "th:recursive-index-complete markers" markerChecks
  group c "th:rice-shapiro example 2" riceChecks
  finish c "ch14-hierarchy"

-- * Points 2 and 4

domains :: [[Int]]
domains = [[0], [0, 1], [0, 1, 2]]

preds :: [Int] -> [Int -> Bool]
preds dom = [\a -> a `elem` s | s <- subsets dom]
  where
    subsets [] = [[]]
    subsets (x : xs) = [r | s <- subsets xs, r <- [s, x : s]]

imp :: Bool -> Bool -> Bool
imp p q = not p || q

rulesChecks :: [(String, Bool)]
rulesChecks =
  [ (name ++ ", domain " ++ show dom, and [l f g == r f g | f <- preds dom, g <- [False, True]])
  | dom <- domains
  , let ex f = any f dom
        al f = all f dom
  , (name, l, r) <-
      [ ("(E a) F or G", \f g -> ex f || g, \f g -> ex (\a -> f a || g))
      , ("(A a) F or G", \f g -> al f || g, \f g -> al (\a -> f a || g))
      , ("(E a) F & G", \f g -> ex f && g, \f g -> ex (\a -> f a && g))
      , ("(A a) F & G", \f g -> al f && g, \f g -> al (\a -> f a && g))
      , ("(E a) F => G", \f g -> imp (ex f) g, \f g -> al (\a -> imp (f a) g))
      , ("(A a) F => G", \f g -> imp (al f) g, \f g -> ex (\a -> imp (f a) g))
      , ("G => (E a) F", \f g -> imp g (ex f), \f g -> ex (\a -> imp g (f a)))
      , ("G => (A a) F", \f g -> imp g (al f), \f g -> al (\a -> imp g (f a)))
      , ("not (A a) F", \f _ -> not (al f), \f _ -> ex (not . f))
      , ("not (E a) F", \f _ -> not (ex f), \f _ -> al (not . f))
      ]
  ]
    ++ [ ("F <=> G is [F => G] & [G => F]", and [(p == q) == (imp p q && imp q p) | p <- [False, True], q <- [False, True]])
       , ("on the empty domain (A a) F => G and (E a)[F => G] differ", imp (all (const False) ([] :: [Int])) True /= any (const True) ([] :: [Int]))
       ]

-- * The example of pp. 396-397

-- | T(i, x, s) on indices i in [0, 2), arguments x in [0, 2), steps s.
type T = Int -> Int -> Int -> Bool

relations :: Int -> [T]
relations steps =
  [ \i x s -> (m `div` (2 ^ (i * 2 * steps + x * steps + s))) `mod` 2 == (1 :: Integer)
  | m <- [0 .. 2 ^ (4 * steps) - 1]
  ]

chainChecks :: [(String, Bool)]
chainChecks =
  [ ( "the formulas of stage 2 agree, steps = " ++ show steps ++ ", z = " ++ show z
    , and [allSame [f t z | f <- formulas] | t <- relations steps] )
  | steps <- [2, 3]
  , let ids = [0, 1]
        xs = [0, 1]
        ss = [0 .. steps - 1]
        ex p = any p
        al p = all p
        f1 t z = ex (\y -> al (\x -> imp (ex (t z x) ss) (not (ex (t y x) ss)) && imp (not (ex (t y x) ss)) (ex (t z x) ss)) xs) ids
        f3 t z = ex (\y -> al (\x -> imp (ex (t z x) ss) (al (\v -> not (t y x v)) ss) && imp (al (\w -> not (t y x w)) ss) (ex (t z x) ss)) xs) ids
        f4 t z = ex (\y -> al (\x -> al (\u -> al (\v -> imp (t z x u) (not (t y x v))) ss) ss && ex (\w -> ex (\s -> imp (not (t y x w)) (t z x s)) ss) ss) xs) ids
        f5 t z = ex (\y -> al (\x -> ex (\w -> al (\u -> ex (\s -> al (\v -> matrix t z y x u v w s) ss) ss) ss) ss) xs) ids
        f6 t z = ex (\y -> al (\x -> al (\u -> al (\v -> ex (\w -> ex (\s -> matrix t z y x u v w s) ss) ss) ss) ss) xs) ids
        formulas = [f0', f1, f3, f4, f5, f6]
        f0' t z = ex (\y -> al (\x -> ex (t z x) ss == not (ex (t y x) ss)) xs) ids
  , z <- ids
  ]
  where
    matrix t z y x u v w s = imp (t z x u) (not (t y x v)) && imp (not (t y x w)) (t z x s)
    allSame (a : rest) = all (== a) rest
    allSame [] = True

-- * Tarski-Kuratowski

data Q = E | A | U deriving (Eq, Show)

data Sk = Qn Q Sk | Neg Sk | And Sk Sk | Or Sk Sk | Imp Sk Sk | Iff Sk Sk | Bd Sk | At

flipQ :: Q -> Q
flipQ E = A
flipQ A = E
flipQ U = U

interleavings :: [a] -> [a] -> [[a]]
interleavings [] ys = [ys]
interleavings xs [] = [xs]
interleavings (x : xs) (y : ys) = map (x :) (interleavings xs (y : ys)) ++ map (y :) (interleavings (x : xs) ys)

-- | All prefixes obtainable by points 2-4 (positive polarity: True).
prefixes :: Bool -> Sk -> [[Q]]
prefixes _ At = [[]]
prefixes pol (Qn q s) = map ((if pol then q else flipQ q) :) (prefixes pol s)
prefixes pol (Neg s) = prefixes (not pol) s
prefixes pol (And a b) = both pol a pol b
prefixes pol (Or a b) = both pol a pol b
prefixes pol (Imp a b) = both (not pol) a pol b
prefixes pol (Iff a b) = prefixes pol (And (Imp a b) (Imp b a))
prefixes pol (Bd s) = prefixes pol s

both :: Bool -> Sk -> Bool -> Sk -> [[Q]]
both pa a pb b = sortNubQ [r | p <- prefixes pa a, q <- prefixes pb b, r <- interleavings p q]

sortNubQ :: [[Q]] -> [[Q]]
sortNubQ = map (map toQ) . sortNub . map (map fromQ)
  where
    fromQ q = case q of E -> 0 :: Int; A -> 1; U -> 2
    toQ k = case k of 0 -> E; 1 -> A; _ -> U

-- | Contraction: adjacent E E or A A merge (U U do not).
contract :: [Q] -> [Q]
contract (x : y : rest) | x == y && x /= U = contract (y : rest)
contract (x : rest) = x : contract rest
contract [] = []

-- | (starts with E, number of blocks).
classOf :: [Q] -> (Bool, Int)
classOf p = case contract p of
  [] -> (True, 0)
  (q : _) -> (q == E, length (contract p))

best :: Sk -> [(Bool, Int)]
best s =
  let cs = sortNub [classOf p | p <- prefixes True s]
      m = minimum (map snd cs)
   in [c | c <- cs, snd c == m]

sigmaSk :: Int -> Sk
sigmaSk 0 = At
sigmaSk k = Qn E (piSk (k - 1))

piSk :: Int -> Sk
piSk 0 = At
piSk k = Qn A (sigmaSk (k - 1))

tkChecks :: [(String, Bool)]
tkChecks =
  [ ("B_rec: E A E A E A is a derivation (Sigma_6)", [E, A, E, A, E, A] `elem` prefixes True recSk)
  , ("B_rec: E A A A E E is a derivation", [E, A, A, A, E, E] `elem` prefixes True recSk)
  , ("B_rec: contraction gives E A E", contract [E, A, A, A, E, E] == [E, A, E])
  , ("B_rec: the best class is Sigma_3", best recSk == [(True, 3)])
  , ("W^A infinite member: Sigma_3", best wASk == [(True, 3)])
  , ("D_u subset W_z: Pi_2", best (Qn A (Imp At (Qn E At))) == [(False, 2)])
  , ("D_u subset W_z with a bounded quantifier: Sigma_1", best (Bd (Imp At (Qn E At))) == [(True, 1)])
  , ("W_z simple: Pi_3", best simpleSk == [(False, 3)])
  , ("W_z infinite: Pi_2", best (Qn A (Qn E (And At (Qn E At)))) == [(False, 2)])
  ]
    ++ [ ("th:strong-hierarchy (a), k = " ++ show k ++ ": Sigma_(k+2)", best (hierSk k) == [(True, k + 2)])
       | k <- [0 .. 4]
       ]
  where
    recSk = Qn E (Qn A (Iff (Qn E At) (Neg (Qn E At))))
    wASk = Qn E (And (Qn E At) (Qn A (Qn E (And At (Qn E At)))))
    simpleSk =
      And
        (Qn A (Qn E (And At (Qn A At))))
        (Qn A (Imp (Qn A (Qn E (And At (Qn E At)))) (Qn E (And (Qn E At) (Qn E At)))))
    hierSk k = Qn E (Qn E (Qn E (And (Qn E At) (And (sigmaSk (k + 1)) (piSk (k + 1))))))

-- * Exercise 14-1

-- | Apply a sequence of P (projection) and C (complement), written in the
-- reverse order of application, to R: (prefix, the matrix is not R).
applyOps :: String -> ([Q], Bool)
applyOps ops =
  let (neg, pre, mneg) = foldr step (False, [], False) ops
   in if neg then (map flipQ pre, not mneg) else (pre, mneg)
  where
    step 'C' (neg, pre, mneg) = (not neg, pre, mneg)
    step _ (neg, pre, mneg)
      | neg = (False, E : map flipQ pre, not mneg)
      | otherwise = (False, E : pre, mneg)

opsChecks :: [(String, Bool)]
opsChecks =
  [ ("(a) CPPCP: forall forall exists on R", applyOps "CPPCP" == ([A, A, E], False))
  , ("(b) CPPCPC: forall forall exists on not R", applyOps "CPPCPC" == ([A, A, E], True))
  , ("(c) PCP: exists forall on not R", applyOps "PCP" == ([E, A], True))
  , ("(c) CCCP: forall on not R", applyOps "CCCP" == ([A], True))
  , ("(c) PCPCPCP: exists forall exists forall on not R", applyOps "PCPCPCP" == ([E, A, E, A], True))
  , ("(d) exists forall exists: PCPCP", shortest [E, A, E] == "PCPCP" && applyOps "PCPCP" == ([E, A, E], False))
  , ("(d) exists forall exists forall: PCPCPCPC", applyOps "PCPCPCPC" == ([E, A, E, A], False))
  , ("(d) forall: CPC", shortest [A] == "CPC" && applyOps "CPC" == ([A], False))
  ]
  where
    shortest p = case [s | n <- [0 .. 9 :: Int], s <- sequence (replicate n "PC"), applyOps s == (p, False)] of
      (s : _) -> s
      [] -> ""

-- * Prefixes of cor:pi-n-plus-two-sentence and th:kreisel-shoenfield-wang

sigmaP :: Int -> [Q]
sigmaP n = take n (cycle [E, A])

piP :: Int -> [Q]
piP n = take n (cycle [A, E])

prefixChecks :: [(String, Bool)]
prefixChecks =
  [ ( "Sigma_" ++ show n ++ " form with Davis' block (k = " ++ show k ++ "): Sigma_" ++ show (n + 2)
    , let qs = sigmaP n
          davis = if odd n then [E, A] ++ replicate k E else [A, E] ++ replicate k A
       in classOf (take (n - 1) qs ++ davis) == (True, n + 2) )
  | n <- [1 .. 8], k <- [1, 2, 4]
  ]
    ++ [ ("Pi_(2n+2) = forall exists forall Sigma_(2n-1), n = " ++ show n, piP (2 * n + 2) == [A, E, A] ++ sigmaP (2 * n - 1))
       | n <- [1 .. 5]
       ]
    ++ [ ("U forall forall exists Pi_(2n-2) = U Pi_(2n), n = " ++ show n, contract (U : A : piP (2 * n)) == contract (U : piP (2 * n)))
       | n <- [1 .. 5]
       ]
    ++ [ ("U forall Pi_(2n+1) = U Pi_(2n+1), n = " ++ show n, contract (U : A : piP (2 * n + 1)) == contract (U : piP (2 * n + 1)))
       | n <- [1 .. 5]
       ]
    ++ [("U U does not contract", contract [U, U, A] == [U, U, A])]

-- * Bounded quantifiers

boundedChecks :: [(String, Bool)]
boundedChecks =
  [ ( "swap with pi_(a+1)^(b+1), b = " ++ show b ++ ", seed " ++ show s
    , lhs == rhs )
  | b <- [0, 1, 2]
  , s <- [1 .. 150 :: Word64]
  , let r :: Integer -> Integer -> Integer -> Bool
        r a c d = c < 4 && fst (below 3 (mkGen (s * 7919 + fromIntegral (a * 100 + c * 10 + d)))) /= (0 :: Int)
        lhs = all (\a -> any (\c -> all (r a c) [0 .. 2]) [0 .. 3]) [0 .. b]
        top = tauN (replicate (fromIntegral b + 1) 3)
        comps c = piN (fromIntegral b + 1) c
        rhs = any (\c -> and [all (r a ci) [0 .. 2] | (a, ci) <- zip [0 .. b] (comps c)]) [0 .. top]
  ]
    ++ [ ("pi_(a+1)^(b+1)(tau^(b+1)(t)) = t_a, t = " ++ show t, piN (length t) (tauN t) == t)
       | b <- [0 .. 3 :: Int], t <- sequence (replicate (b + 1) [0 .. 3])
       ]
    ++ [("x in D_u => x < u, u < 2^14", and [all (< u) (dset u) | u <- [1 .. 2 ^ (14 :: Int)]])]
    ++ [("D_0 is empty", null (dset 0))]

-- * The footnote of th:goedel-polynomial

footnoteChecks :: [(String, Bool)]
footnoteChecks =
  [ ("alpha /= 0 <=> (exists c)(alpha * alpha = c + 1), alpha = " ++ show a, (a /= 0) == (a * a >= 1))
  | a <- [-60 .. 60 :: Integer]
  ]
    ++ [ ("alpha * beta = 0 <=> alpha = 0 or beta = 0, " ++ show (a, b), (a * b == 0) == (a == 0 || b == 0))
       | a <- [-12 .. 12 :: Integer], b <- [-12 .. 12]
       ]
    ++ [ ("printed (exists c)(alpha = c + 1) fails at alpha = -1", let a = -1 :: Integer in a /= 0 && not (any (\c -> a == c + 1) [0 .. 100]))
       , ("not (0 = 1) is true but gamma = 0 - 1 = -1 is not c + 1", (0 :: Integer) /= 1 && not (any (\c -> 0 - 1 == c + 1) [0 .. 100 :: Integer]))
       , ("the printed rule is right exactly for alpha >= 0 (|alpha| <= 60)", and [((a /= 0) == any (\c -> a == c + 1) [0 .. 100]) == (a >= 0) | a <- [-60 .. 60 :: Integer]])
       , ("q = n + k + 3 = 8 for n = 1, k = n + 3", let n = 1 :: Int; k = n + 3 in n + k + 3 == 8)
       ]

-- * Fermat's formula

fermatChecks :: [(String, Bool)]
fermatChecks =
  [ ("printed formula false at x = 0, y = z = 1, w = 3", (0 :: Integer) ^ (3 :: Int) + 1 ^ (3 :: Int) == 1 ^ (3 :: Int))
  , ("x = y = z = 0, w = 3 also", (0 :: Integer) ^ (3 :: Int) + 0 == 0)
  , ( "with x > 0 and y > 0 no solution in the range"
    , null [() | w <- [3 .. 6 :: Int], x <- [1 .. 30 :: Integer], y <- [1 .. 30], z <- [1 .. 60], x ^ w + y ^ w == z ^ w] )
  , ("x, y > 0 force z > 0", and [x ^ w + y ^ w > (0 :: Integer) | w <- [3 .. 6 :: Int], x <- [1 .. 5], y <- [1 .. 5]])
  ]

-- * th:pi-two-u-form

uFormChecks :: [(String, Bool)]
uFormChecks =
  [ ( "pi_1 maps {y | S(z, y)} one-one onto the domain, seed " ++ show s
    , let halt :: Integer -> Maybe Integer
          halt x = let (r, _) = below 4 (mkGen (s * 31 + fromInteger x)) in if r == 0 then Nothing else Just (toInteger r * x `mod` 17)
          sSet = [y | y <- [0 .. tau 29 17], pi1 y < 30, halt (pi1 y) == Just (pi2 y)]
          dom = [x | x <- [0 .. 29], halt x /= Nothing]
       in sortNub (map pi1 sSet) == dom && length sSet == length dom )
  | s <- [1 .. 60 :: Word64]
  ]

-- * th:infinite-member-complete: psi

psiChecks :: [(String, Bool)]
psiChecks =
  [ ( "dom psi = {n | (forall m <= n)(exists x_3) R(m, x_3)}, seed " ++ show s
    , dom == closed && dom == takeWhile (`elem` dom) [0 .. 29] )
  | s <- [1 .. 200 :: Word64]
  , let r m x3 = fst (below 5 (mkGen (s * 104729 + fromIntegral (m * 10 + x3)))) == (0 :: Int)
        ex m = any (r m) [0 .. 4 :: Int]
        psiDef = stepDef 0
        stepDef m = if m < 30 && ex m then m : stepDef (m + 1) else []
        dom = psiDef
        closed = [n | n <- [0 .. 29], all ex [0 .. n]]
  ]

-- * th:recursive-index-complete: markers

-- | A model numbering: W i = [(element, step at which it appears)].
type Numbering = Int -> [(Int, Int)]

randomW :: Int -> [(Int, Int)]
randomW i =
  let g0 = mkGen (fromIntegral i * 6700417 + 3)
      (k, g1) = below 5 g0
      go 0 _ = []
      go j g = let (e, ga) = below 300 g; (t, gb) = below 100 ga in (e, t + 1) : go (j - 1 :: Int) gb
   in go k g1

data Run = Run
  { rMarkers :: [(Int, Bool)] -- ^ position, has a plus
  , rPlus :: [Int]
  , rFree :: Int
  , rMoves :: [(Int, Int)] -- ^ (marker, stage of a move)
  , rFirst :: [Int] -- ^ first positions
  }

-- | Stages 0..2N+1 of the main procedure for the index z.
runMarkers :: Numbering -> Int -> Int -> Run
runMarkers w z bigN = go 0 (Run [] [] 0 [] [])
  where
    inW i e n = any (\(e', t) -> e' == e && t <= n) (w i)
    go st run
      | st > 2 * bigN + 1 = run
      | even st =
          let n = st `div` 2
              ms = rMarkers run ++ [(rFree run, False)]
              (ms', pl) = unzip [if not p && inW i x n then ((x, True), [x]) else ((x, p), []) | (i, (x, p)) <- zip [0 ..] ms]
           in go (st + 1) run {rMarkers = ms', rPlus = concat pl ++ rPlus run, rFree = rFree run + 1, rFirst = rFirst run ++ [rFree run]}
      | otherwise =
          let n = st `div` 2
              candidates =
                [ y
                | y <- [0 .. n]
                , any (\(e, t) -> e == y && t <= n) (w z)
                , any (\(_, t) -> t == n) (w y)
                ]
           in case candidates of
                [] -> go (st + 1) run
                (yn : _) ->
                  let ms = rMarkers run
                      plus = [x | (i, (x, p)) <- zip [0 ..] ms, i >= yn, i <= n, not p]
                      newPos = [rFree run ..]
                      ms' = [if i >= yn && i <= n then (pos, False) else m | (i, m, pos) <- zip3 [0 ..] ms (replicate yn 0 ++ newPos)]
                   in go (st + 1) run
                        { rMarkers = ms'
                        , rPlus = plus ++ rPlus run
                        , rFree = rFree run + (n - yn + 1)
                        , rMoves = [(i, st) | i <- [yn .. n]] ++ rMoves run
                        }

-- | Scenario A: z = 900, W_z = {2, 4, 5}; W_2, W_4 finite, W_5 empty.
finiteW :: Numbering
finiteW i
  | i == 900 = [(2, 3), (4, 10), (5, 1)]
  | i == 2 = [(10, 5), (11, 40), (12, 61)]
  | i == 4 = [(3, 20), (7, 99)]
  | i == 5 = []
  | otherwise = randomW i

-- | Scenario B: z = 901, W_z = {1, 3, 6}; W_1 finite with late elements,
-- W_3 infinite (one new element every 4 steps), W_6 finite.
infiniteW :: Numbering
infiniteW i
  | i == 901 = [(3, 5), (1, 2), (6, 30)]
  | i == 1 = [(50, 150), (51, 170)]
  | i == 3 = [(5000 + j, 4 * j + 7) | j <- [0 .. 200]]
  | i == 6 = [(8, 12)]
  | otherwise = randomW i

markerChecks :: [(String, Bool)]
markerChecks =
  [ ("A: no marker moves after stage 2 * 99 + 1", all ((<= 2 * 99 + 1) . snd) (rMoves runA))
  , ("A: some markers move", not (null (rMoves runA)))
  , ( "A: last positions: x_n in A <=> x_n in W_n"
    , and [p == (x `elem` map fst (finiteW i)) && (x `elem` rPlus runA) == p | (i, (x, p)) <- zip [0 ..] (rMarkers runA)] )
  , ("A: both cases x_n in A and x_n not in A occur", any snd (rMarkers runA) && any (not . snd) (rMarkers runA))
  , ("A: pluses only at positions that had a marker", all (< rFree runA) (rPlus runA))
  , ("B: marker 3 moves at least 40 times", length [() | (3, _) <- rMoves runB] >= 40)
  , ("B: markers below 3 stop moving (after stage 341)", all (\(i, st) -> i >= 3 || st <= 341) (rMoves runB))
  , ( "B: after the first position of a marker attached after stage 341, every number whose marker moved on is in A"
    , let k = 171
          start = rFirst runB !! k
          current = map fst (rMarkers runB)
       in and [e `elem` rPlus runB | e <- [start .. rFree runB - 1], e `notElem` current] )
  , ( "B: a number after the first position of marker 3 stays outside A (a lower marker moved there)"
    , let start3 = rFirst runB !! 3
       in or [x > start3 && not p | (i, (x, p)) <- zip [0 :: Int ..] (rMarkers runB), i < 3] )
  ]
  where
    runA = runMarkers finiteW 900 240
    runB = runMarkers infiniteW 901 240

-- * Rice-Shapiro, example 2

riceChecks :: [(String, Bool)]
riceChecks =
  [("D_(u+1) is not empty, u < 4096", all (\u -> not (null (dset (u + 1)))) [0 .. 4095])]
    ++ [("{" ++ show a ++ "} = D_(2^a)", dset (2 ^ a) == [a]) | a <- [0 .. 40]]
