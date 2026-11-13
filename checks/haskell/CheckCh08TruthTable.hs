-- | Checks of chapter 8 (printed pp. 140-166): simple sets and the
-- truth-table reducibilities.  Scope ch08-09.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh08TruthTable.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh08TruthTable.hs
--      [--verbose]
--
-- What is checked, and where the expected values come from (printed pages
-- and our labels):
--
-- * The codings the models use (§ 5.3, pp. 89-90): tau, its order
--   <0,0>, <0,1>, <1,0>, ... (p. 89), <2, 1, 0> = 44 (example 1, p. 90),
--   the inverses, canonical indices.
-- * § 8.1, th:simple-set-exists (p. 141), part (ii): if each x selects at
--   most one y > 2x, at most k of {0, ..., 2k} are selected; all
--   selections for k <= 5.  The general statement is the Lean lemma
--   post_selection_card (Ch08_09Counting.lean).
-- * § 8.4, th:simple-tt-complete (pp. 148-149): the blocks
--   S_x = {2^x - 1, ..., 2^(x+1) - 2} (the printed {0}, {1, 2},
--   {3, ..., 6}, {7, ..., 14}), a partition of {0, ..., 2^21 - 2}; S_x has
--   k + 1 elements in {0, ..., 2k}, k = 2^x - 1, so it meets the complement
--   of every selection; on models of S and K (S missing a point of every
--   block): x in K <=> S_x subset S* and x not in K <=> S_x meets the
--   complement of S* (the q-reduction of ex:q-reducibility (vii)); the
--   tt-condition of order 2^x.
-- * § 8.3 (pp. 145-146): reduced polynomials over the field {0, 1} give
--   every n-ary boolean function exactly once (n <= 4); the polynomial
--   w1 w2 + w1 + 1 of p. 152 is the condition "4 not in X or 17 in X"; the
--   disjunctive polynomial 1 + prod (w_i + 1) of ex:q-reducibility is the
--   disjunction, prod w_i the conjunction.
-- * th:tt-reflexive-transitive (pp. 146-147) and th:btt-reflexive-transitive
--   (p. 151): the composed condition h(x) of the printed formula is
--   satisfied on C exactly when x in A, its order is n_1 + ... + n_m <=
--   m_1 m_2 (random reductions over {0, ..., 7}); the examples
--   K-bar <=_btt K (order 1), K x K-bar <=_btt K (order 2), A x A <=_btt A,
--   and the disjunctive reduction of the complement of A-bar x A-bar to A
--   (ex:q-reducibility), on random sets standing for K and A.
-- * th:tt-cylinders (c) (p. 149): a widened condition is satisfied on the
--   same sets (all conditions of order <= 2 over {0, ..., 3}).
-- * The lemma of th:btt-complete-not-simple (pp. 151-154): the example of
--   derivability of p. 152; the count sum_(i<=m) 2^(2^i) < 2^(2^(m+1))
--   (m <= 6; general: Lean boolean_count_lt); the step of p. 154 and
--   ex:derivable-conditions on all conditions of order <= 3 with
--   associated elements in {10, 11, 12} (outside A) and {0, 1} (in A),
--   arranged as in the proof: with no repeated numbers, the same boolean
--   function and the same T cap A-bar, t'_(j2) is derivable from
--   C u {t'_(j1)}; with repeated numbers (allowed by the definition of
--   p. 146 and by "в порядке неубывания") a counterexample exists, and
--   without the same boolean function (ex:derivable-conditions as printed)
--   another one; under C every condition reduces to a function of the
--   variables in T cap A-bar, 2^(2^k) of them for |T cap A-bar| = k.
-- * th:btt-not-m (Fischer, p. 155): the printed f(0), ..., f(3) are the
--   balanced trees of g over S_x; on models with
--   [x in X & y in X] <=> g(x, y) in X: f(x) in X <=> S_x subset X.
-- * th:complete-tt-degree (Fischer, p. 157): the printed f(0), ..., f(5)
--   for A_4 <=_m A_2 via h are the values of one procedure (cut the list
--   into pieces of 16, pad cyclically, apply h, repeat until at most 4
--   numbers remain, pad cyclically to 4), compared as terms with h
--   uninterpreted; on models of h: f(x) in A_u <=> S_x subset X, for
--   (u, v) = (2, 4) and (0, 1), (1, 2), (1, 3), (2, 3) ("Мы опускаем
--   детали задания f в общем случае").
-- * The lemma of th:simple-m-degree (p. 156): f gives A <=_m B and g is
--   one-one and gives B <=_1 A, on random A containing C (the multiples
--   of 3), with p(m) = 0, p(3k) = 3k + 3.
-- * ex:join-of-cylinders (b) (p. 163), as corrected (A (+) A <=_1 A): on
--   cylinders C x N, f(2x) = <pi_1 x, 2 pi_2 x>, f(2x + 1) =
--   <pi_1 x, 2 pi_2 x + 1> is a one-one reduction, and
--   h(x, n) = f_1^n(f_0(x)) is one-one and keeps membership (general
--   proof: Lean Ch08_09Cylinder.lean).  The printed A (+) B <=_1 A:
--   the empty cylinder with B = N fails (1 in A (+) B); and A (+) N <=_1 A
--   for every A containing the multiples of 3 by an explicit one-one map
--   (so for simple sets, which are not cylinders by th:simple-sets-properties
--   (d)).
-- * ex:semicreative-not-creative (p. 165): S_x subset B <=> S_x in the
--   family (as corrected; the printed complement of S_x is never one of the
--   finite S_y), on random S missing a point of each block and random
--   families; for its hint (vi): A-bar - (B - A) = B-bar when A subset B.
--
-- Not established: anything about recursive enumerability, productiveness
-- or simplicity of the actual sets; the models only check the finite
-- combinatorics of the constructions in the stated bounds.
module Main (main) where

import Ch08Coding
import Data.List (nub, sort)
import Data.Maybe (catMaybes)
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "5.3 codings used by the models (pp. 89-90)" codingChecks
  group c "8.1 Th. II (ii): at most k of {0..2k} selected (p. 141)" postBound
  group c "8.4 Th. VI: the blocks S_x and S* (pp. 148-149)" blockChecks
  group c "8.3 boolean functions and polynomials (pp. 145-146, 152)" polyChecks
  group c "8.3-8.5 Th. VIII, XI: composition of tt-conditions (pp. 146-151)"
    compositionChecks
  group c "8.4 Th. X (c): widened conditions (p. 149)" widenChecks
  group c "8.5 lemma of Th. XII: derivability (pp. 151-154), ex. 8-25"
    derivabilityChecks
  group c "8.5 Th. XIII (Fischer): f by g (p. 155)" fischer13Checks
  group c "8.6 Th. XV (Fischer): f by h (p. 157)" fischer15Checks
  group c "8.6 lemma of Th. XIV: f and g (p. 156)" dekkerLemmaChecks
  group c "8.8 ex. 8-29 (b): A (+) A <=_1 A, the printed A (+) B (p. 163)"
    cylinderChecks
  group c "8.8 ex. 8-42: S_x subset B, the hint of (vi) (p. 165)" shoenfieldChecks
  finish c "ch08-truth-table"

member :: [Integer] -> Integer -> Bool
member xs n = n `elem` xs

subset :: [Integer] -> [Integer] -> Bool
subset xs ys = all (`elem` ys) xs

chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks k xs = take k xs : chunks k (drop k xs)

tuples :: Int -> [a] -> [[a]]
tuples 0 _ = [[]]
tuples n xs = [y : ys | y <- xs, ys <- tuples (n - 1) xs]

-- * Codings

codingChecks :: [(String, Bool)]
codingChecks =
  [ ("tau order, p. 89, n = " ++ show n, tau x y == n)
  | (n, (x, y)) <-
      zip [0 ..] [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0), (0, 3), (1, 2)]
  ]
    ++ [ ("<2, 1> = 8 (p. 90)", tau 2 1 == 8)
       , ("<2, 1, 0> = 44 (p. 90)", tauN [2, 1, 0] == 44)
       , ( "tau maps pairs onto {0..2000}"
         , sort [tau x y | x <- [0 .. 70], y <- [0 .. 70], tau x y <= 2000]
             == [0 .. 2000]
         )
       ]
    ++ [ ("untau (tau " ++ show (x, y) ++ ")", untau (tau x y) == (x, y))
       | x <- [0 .. 40], y <- [0 .. 40]
       ]
    ++ [ ("piN (tauN " ++ show xs ++ ")", piN (length xs) (tauN xs) == xs)
       | n <- [1 .. 4], xs <- tuples n [0 .. 4]
       ]
    ++ [("canon (dset " ++ show u ++ ")", canon (dset u) == u) | u <- [0 .. 1023]]

-- * Post's simple set: the selections of th:simple-set-exists

-- | All selections of the numbers x < k: none, or one y with
-- 2x < y <= 2k (selections above 2k do not matter in {0, ..., 2k}).
selections :: Integer -> [[Maybe Integer]]
selections k = mapM (\x -> Nothing : map Just [2 * x + 1 .. 2 * k]) [0 .. k - 1]

postBound :: [(String, Bool)]
postBound =
  [ ( "k = " ++ show k ++ ", selection " ++ show s
    , toInteger (length (nub (catMaybes s))) <= k
    )
  | k <- [0 .. 5], s <- selections k
  ]
    ++ [ ( "the bound k is attained (y = 2x + 1), k = " ++ show k
         , let ys = [2 * x + 1 | x <- [0 .. k - 1]] in length (nub ys) == fromInteger k && all (<= 2 * k) ys
         )
       | k <- [0 .. 30 :: Integer]
       ]

-- * The blocks of th:simple-tt-complete

block :: Integer -> [Integer]
block x = [2 ^ x - 1 .. 2 ^ (x + 1) - 2]

-- | A random set S over {0, ..., 2^(n+1) - 2} with a point of each block
-- S_0, ..., S_n outside S, a random set K over {0, ..., n}, and S*.
starModel :: Integer -> Gen -> (([Integer], [Integer], Integer -> Bool), Gen)
starModel n g0 =
  let (s0, g1) = subsetOf 70 [0 .. 2 ^ (n + 1) - 2] g0
      (ws, g2) = draws (fromInteger n + 1) next g1
      holePts = [b !! (fromIntegral w `mod` length b) | (x, w) <- zip [0 .. n] ws, let b = block x]
      s = [m | m <- s0, m `notElem` holePts]
      (k, g3) = subsetOf 50 [0 .. n] g2
      sStar m = member s m || any (\x -> member (block x) m) k
   in ((s, k, sStar), g3)

blockChecks :: [(String, Bool)]
blockChecks =
  [ ("printed blocks {0}, {1, 2}, {3..6}, {7..14}", map block [0 .. 3] == [[0], [1, 2], [3 .. 6], [7 .. 14]])
  , ("S_0, ..., S_20 partition {0, ..., 2^21 - 2}", concatMap block [0 .. 20] == [0 .. 2 ^ (21 :: Integer) - 2])
  ]
    ++ [ ("|S_" ++ show x ++ "| = 2^x = k + 1 in {0..2k}, k = 2^x - 1"
         , let k = 2 ^ x - 1 in toInteger (length (block x)) == k + 1 && maximum (block x) == 2 * k)
       | x <- [0 .. 20]
       ]
    ++ [ ("S_" ++ show x ++ " not inside the selection " ++ show s
         , not (block x `subset` catMaybes s)
         )
       | x <- [0 .. 2], s <- selections (2 ^ x - 1)
       ]
    ++ concat [starRun t | t <- [1 .. 60]]
    ++ [ ("tt-condition of S_" ++ show x ++ " of order 2^x on a set", order cond == 2 ^ x && sat (member xs) cond == (block x `subset` xs))
       | t <- [1 .. 40 :: Int]
       , x <- [0 .. 4]
       , let cond = TT (block x) (fromFn (2 ^ x) and)
       , let (xs0, g1) = subsetOf 80 [0 .. 126] (mkGen (fromIntegral (1000 + t)))
       , let (extra, _) = pick [0 .. 6] g1
       , let xs = if even t then xs0 else sortNub (xs0 ++ block extra)
       ]
  where
    starRun t =
      let ((s, k, sStar), _) = starModel 6 (mkGen (fromIntegral t))
       in [ ("model " ++ show t ++ ": every S_x meets the complement of S", all (\x -> not (block x `subset` s)) [0 .. 6])
          ]
            ++ [ ("model " ++ show t ++ ": x in K <=> S_x subset S*, x = " ++ show x, (x `elem` k) == all sStar (block x))
               | x <- [0 .. 6]
               ]
            ++ [ ("model " ++ show t ++ ": x not in K <=> S_x meets the complement of S*, x = " ++ show x
                 , (x `notElem` k) == any (not . sStar) (block x)
                 )
               | x <- [0 .. 6]
               ]

-- * Boolean functions and reduced polynomials

-- | A reduced polynomial: the set of its monomials, each monomial a set of
-- variables (bit i - 1 for w_i), kept as a mask over the 2^n monomials.
polyBF :: Int -> Integer -> BF
polyBF n mask = fromFn n value
  where
    value ws =
      odd
        ( length
            [ ()
            | m <- [0 .. 2 ^ n - 1 :: Int]
            , odd (mask `div` (2 ^ m))
            , and [w | (i, w) <- zip [0 :: Int ..] ws, odd (m `div` (2 ^ i))]
            ]
        )

polyChecks :: [(String, Bool)]
polyChecks =
  [ ( "reduced polynomials of " ++ show n ++ " variables give each boolean function once"
    , let tables = [m | p <- [0 .. 2 ^ (2 ^ n :: Integer) - 1], let BF _ m = polyBF n p]
       in length (nub tables) == 2 ^ (2 ^ n :: Int) && length tables == 2 ^ (2 ^ n :: Int)
    )
  | n <- [1 .. 4]
  ]
    ++ [ ( "w1 w2 + w1 + 1 is 'not w1 or w2' (p. 152)"
         , polyBF 2 (2 ^ (0 :: Int) + 2 ^ (1 :: Int) + 2 ^ (3 :: Int)) == fromFn 2 (\ws -> not (arg 1 ws) || arg 2 ws)
         )
       ]
    ++ [ ( "<<4, 17>, w1 w2 + w1 + 1> on " ++ show xs ++ " is '4 not in X or 17 in X'"
         , sat (member xs) (TT [4, 17] (polyBF 2 11)) == (4 `notElem` xs || 17 `elem` xs)
         )
       | xs <- subsetsOf [4, 17]
       ]
    ++ [ ( "1 + prod (w_i + 1) is the disjunction, n = " ++ show n
         , polyBF n (2 ^ (2 ^ n :: Integer) - 2) == fromFn n or
         )
       | n <- [1 .. 4]
       ]
    ++ [ ("prod w_i is the conjunction, n = " ++ show n, polyBF n (2 ^ (2 ^ n - 1 :: Integer)) == fromFn n and)
       | n <- [1 .. 4]
       ]

-- * Composition of tt-conditions

randomTT :: [Integer] -> Int -> Gen -> (TT, Gen)
randomTT univ maxOrder g0 =
  let (n0, g1) = below maxOrder g0
      n = n0 + 1
      (xs, g2) = draws n (pick univ) g1
      (w, g3) = next g2
      m = toInteger w `mod` (2 ^ (2 ^ n :: Integer))
   in (TT xs (BF n m), g3)

-- | The condition h(x) of the proof of th:tt-reflexive-transitive.
compose :: TT -> (Integer -> TT) -> TT
compose (TT ys a) g = TT (concat zss) (fromFn q value)
  where
    conds = map g ys
    zss = [zs | TT zs _ <- conds]
    ns = map length zss
    q = sum ns
    value ws = apply a [apply b part | (TT _ b, part) <- zip conds (split ns ws)]
    split [] _ = []
    split (k : ks) ws = take k ws : split ks (drop k ws)

compositionChecks :: [(String, Bool)]
compositionChecks =
  concat [run t | t <- [1 .. 200 :: Int]]
    ++ [ ("reflexivity: <<x>, identity> on " ++ show xs ++ ", x = " ++ show x, sat (member xs) (TT [x] (fromFn 1 (arg 1))) == (x `elem` xs))
       | xs <- subsetsOf [0 .. 3], x <- [0 .. 3]
       ]
    ++ concat [examples t | t <- [1 .. 20 :: Int]]
  where
    univ = [0 .. 7]
    run t =
      let g0 = mkGen (fromIntegral (5000 + t))
          (c, g1) = subsetOf 50 univ g0
          (gs, g2) = draws 8 (randomTT univ 3) g1
          (fs, _) = draws 8 (randomTT univ 3) g2
          g y = gs !! fromInteger y
          f x = fs !! fromInteger x
          b y = sat (member c) (g y)
          a x = sat b (f x)
       in [ ( "model " ++ show t ++ ", x = " ++ show x ++ ": h(x) on C <=> x in A, order n_1 + ... + n_m <= 3 * 3"
            , let h = compose (f x) g
               in sat (member c) h == a x
                    && order h == sum [order (g y) | y <- let TT ys _ = f x in ys]
                    && order h <= 9
            )
          | x <- univ
          ]
    examples t =
      let (k, _) = subsetOf 50 [0 .. 20] (mkGen (fromIntegral (7000 + t)))
          kk = member k
       in [ ("K-bar <=_btt K, order 1, x = " ++ show x, sat kk (TT [x] (fromFn 1 (not . arg 1))) == not (kk x))
          | x <- [0 .. 20]
          ]
            ++ [ ( "K x K-bar <=_btt K, order 2, z = " ++ show z
                 , sat kk (TT [pi1 z, pi2 z] (fromFn 2 (\ws -> arg 1 ws && not (arg 2 ws)))) == timesSet kk (not . kk) z
                 )
               | z <- [0 .. 200]
               ]
            ++ [ ("A x A <=_btt A (ex. 8-22 (a)), z = " ++ show z, sat kk (TT [pi1 z, pi2 z] (fromFn 2 and)) == timesSet kk kk z)
               | z <- [0 .. 200]
               ]
            ++ [ ( "complement of A-bar x A-bar <=_q A (ex. 8-26), z = " ++ show z
                 , not (timesSet (not . kk) (not . kk) z) == any kk [pi1 z, pi2 z]
                     && sat kk (TT [pi1 z, pi2 z] (polyBF 2 (2 ^ (4 :: Int) - 2))) == any kk [pi1 z, pi2 z]
                 )
               | z <- [0 .. 200]
               ]

-- * Widened conditions

widenChecks :: [(String, Bool)]
widenChecks =
  [ ( "<<" ++ show xs ++ ", " ++ show e ++ ">, beta> with beta(w) = alpha(w_1..w_n), alpha = " ++ show m
    , and [sat (member ys) (TT xs a) == sat (member ys) (TT (xs ++ [e]) beta) | ys <- subsetsOf univ]
    )
  | n <- [1, 2]
  , xs <- tuples n univ
  , a@(BF _ m) <- allBF n
  , e <- univ
  , let beta = fromFn (n + 1) (apply a . take n)
  ]
  where
    univ = [0 .. 3]

-- * Derivability (lemma of th:btt-complete-not-simple)

-- | The model: A contains 0, 1 and not 10, 11, 12; C is the set of
-- conditions "x in X" for x in A, so the sets on which all of C holds
-- are the sets containing 0, 1.
outside, inside :: [Integer]
outside = [10, 11, 12]
inside = [0, 1]

onA :: Integer -> Bool
onA = member inside

cSets :: [Integer -> Bool]
cSets = [member (inside ++ s) | s <- subsetsOf outside]

derivable :: TT -> TT -> Bool
derivable t1 t2 = and [not (sat x t1) || sat x t2 | x <- cSets]

-- | Tuples arranged as in the proof: the elements outside A first (in
-- increasing order), then those of A; with or without repetitions.
arranged :: Bool -> Int -> [[Integer]]
arranged repeats n =
  [ out ++ ins
  | k <- [1 .. n]
  , out <- if repeats then nondecreasing k outside else increasing k outside
  , ins <- if repeats then tuples (n - k) inside else distinctTuples (n - k) inside
  ]
  where
    increasing 0 _ = [[]]
    increasing _ [] = []
    increasing j (y : ys) = map (y :) (increasing (j - 1) ys) ++ increasing j ys
    nondecreasing 0 _ = [[]]
    nondecreasing _ [] = []
    nondecreasing j (y : ys) = map (y :) (nondecreasing (j - 1) (y : ys)) ++ nondecreasing j ys
    distinctTuples 0 _ = [[]]
    distinctTuples j ys = [y : rest | y <- ys, rest <- distinctTuples (j - 1) (filter (/= y) ys)]

sameOutside :: [Integer] -> [Integer] -> Bool
sameOutside xs ys = sortNub (filter (`elem` outside) xs) == sortNub (filter (`elem` outside) ys)

-- | Pairs of conditions with the same boolean function and the same
-- T cap A-bar, both satisfied on A.
samePairs :: Bool -> [(TT, TT)]
samePairs repeats =
  [ (t1, t2)
  | n <- [1 .. 3]
  , let tups = arranged repeats n
  , xs <- tups
  , ys <- tups
  , sameOutside xs ys
  , a <- allBF n
  , let t1 = TT xs a
  , let t2 = TT ys a
  , sat onA t1
  , sat onA t2
  ]

-- | The function of the variables outside A to which a condition reduces
-- under C (its truth table over the assignments of 10, 11 in X).
reduced :: TT -> [Bool]
reduced t = [sat (member (inside ++ s)) t | s <- subsetsOf [10, 11]]

derivabilityChecks :: [(String, Bool)]
derivabilityChecks =
  [ ( "p. 152: '9 not in X or 17 in X' follows from '4 in X', '9 in X', '4 not in X or 17 in X', X = " ++ show xs
    , let x = member xs
       in not (x 4 && x 9 && (not (x 4) || x 17)) || (not (x 9) || x 17)
    )
  | xs <- subsetsOf [4, 9, 17]
  ]
    ++ [ ("sum_(i<=m) 2^(2^i) < 2^(2^(m+1)), m = " ++ show m, sum [2 ^ (2 ^ i :: Integer) | i <- [0 .. m]] < (2 :: Integer) ^ (2 ^ (m + 1) :: Integer))
       | m <- [0 .. 6 :: Integer]
       ]
    ++ [ ("no repeated numbers: " ++ show t1 ++ " derives " ++ show t2, derivable t1 t2)
       | (t1, t2) <- samePairs False
       ]
    ++ [ ( "with repeated numbers some pair is not derivable (the printed arrangement)"
         , any (\(t1, t2) -> not (derivable t1 t2)) (samePairs True)
         )
       , ( "repeated numbers: <<10, 11, 0>, a>, <<10, 10, 11>, a> with a(0,0,0) = a(0,0,1) = a(1,0,1) = 1, a(1,1,0) = 0"
         , let a = fromFn 3 (\ws -> ws `elem` [[False, False, False], [False, False, True], [True, False, True]])
               t1 = TT [10, 11, 0] a
               t2 = TT [10, 10, 11] a
            in sat onA t1 && sat onA t2 && sameOutside [10, 11, 0] [10, 10, 11] && not (derivable t1 t2)
         )
       , ( "ex. 8-25 as printed (no common boolean function): <<10, 11>, not w1>, <<10, 11>, not w2>"
         , let t1 = TT [10, 11] (fromFn 2 (not . arg 1))
               t2 = TT [10, 11] (fromFn 2 (not . arg 2))
            in sat onA t1 && sat onA t2 && not (derivable t1 t2)
         )
       , ( "conditions with T cap A-bar = {10, 11} reduce to all 2^(2^2) = 16 functions, satisfied on A: 8"
         , let ts = [ TT xs a | n <- [1 .. 3], xs <- tuples n (inside ++ [10, 11]), sortNub (filter (`elem` outside) xs) == [10, 11], a <- allBF n]
               rs = nub (map reduced ts)
               rsA = nub [reduced t | t <- ts, sat onA t]
            in length rs == 16 && length rsA == 8
         )
       ]

-- * Fischer's theorem XIII: terms in g

data GT = L Integer | G GT GT deriving (Eq, Show)

printed13 :: [GT]
printed13 =
  [ L 0
  , G (L 1) (L 2)
  , G (G (L 3) (L 4)) (G (L 5) (L 6))
  , G (G (G (L 7) (L 8)) (G (L 9) (L 10))) (G (G (L 11) (L 12)) (G (L 13) (L 14)))
  ]

balanced :: [GT] -> GT
balanced [t] = t
balanced ts = let (a, b) = splitAt (length ts `div` 2) ts in G (balanced a) (balanced b)

general13 :: Integer -> GT
general13 x = balanced (map L (block x))

evalG :: (Integer -> Integer -> Integer) -> GT -> Integer
evalG _ (L n) = n
evalG g (G a b) = g (evalG g a) (evalG g b)

fischer13Checks :: [(String, Bool)]
fischer13Checks =
  [("printed f(" ++ show x ++ ") is the tree over S_x", general13 x == printed13 !! fromInteger x) | x <- [0 .. 3]]
    ++ concat
      [ [ ("gadget model " ++ show t ++ ": f(" ++ show x ++ ") in X <=> S_x subset X", xx (evalG g (general13 x)) == all xx (block x))
        | x <- [0 .. 8]
        ]
      | t <- [1 .. 40 :: Int]
      , let (xs, _) = subsetOf 92 [0 .. 510] (mkGen (fromIntegral (9000 + t)))
      , let xx = member xs
      , let g a b = if not (xx a) then a else b
      ]
    ++ [ ("product model (X = non-multiples of 3, g = *): f(" ++ show x ++ ")", nm3 (evalG (*) (general13 x)) == all nm3 (block x))
       | x <- [0 .. 6]
       ]
  where
    nm3 n = n `mod` 3 /= 0

-- * Fischer's theorem XV: terms in h

-- | A number, h applied to a list, and the i-th component (from 1) of a
-- tuple given by a term.
data HT = HL Integer | H [HT] | P Int HT deriving (Eq, Show)

components :: Int -> HT -> [HT]
components k t = [P i t | i <- [1 .. k]]

-- | The procedure for A_v <=_m A_u via h (u < v): 2^v numbers go into h,
-- 2^u come out.
generalF :: Int -> Int -> Integer -> [HT]
generalF u v x = go (map HL (block x))
  where
    inN = 2 ^ v
    outN = 2 ^ u
    go ts
      | length ts <= outN = take outN (cycle ts)
      | otherwise = go (concatMap (\c -> components outN (H (take inN (cycle c)))) (chunks inN ts))

printed15 :: [[HT]]
printed15 =
  [ map HL [0, 0, 0, 0]
  , map HL [1, 2, 1, 2]
  , map HL [3, 4, 5, 6]
  , components 4 (H (map HL ([7 .. 14] ++ [7 .. 14])))
  , components 4 (H (map HL [15 .. 30]))
  , components 4 (H (ws ++ ws))
  ]
  where
    ws = components 4 (H (map HL [31 .. 46])) ++ components 4 (H (map HL [47 .. 62]))

-- | A model of h: each group of 2^(v-u) numbers is replaced by a number in
-- X exactly when the whole group is in X.
hModel :: (Integer -> Bool) -> Int -> Int -> [Integer] -> [Integer]
hModel xx u v as = map gadget (chunks (2 ^ (v - u)) as)
  where
    gadget grp = case filter (not . xx) grp of
      (y : _) -> y
      [] -> case grp of { (y : _) -> y; [] -> 0 }

evalH :: (Integer -> Bool) -> Int -> Int -> HT -> Integer
evalH _ _ _ (HL n) = n
evalH xx u v (P i t) = case t of
  H ts -> hModel xx u v (map (evalH xx u v) ts) !! (i - 1)
  _ -> error "P of a non-h term"
evalH _ _ _ (H _) = error "a tuple of h is used only through its components"

fischer15Checks :: [(String, Bool)]
fischer15Checks =
  [("printed f(" ++ show x ++ ") for A_4 <=_m A_2", generalF 2 4 x == printed15 !! fromInteger x) | x <- [0 .. 5]]
    ++ concat
      [ [ ( "model " ++ show t ++ ", A_" ++ show v ++ " <=_m A_" ++ show u ++ ": f(" ++ show x ++ ") in A_u <=> S_x subset X"
          , all xx (map (evalH xx u v) (generalF u v x)) == all xx (block x)
          )
        | x <- [0 .. 8]
        ]
          ++ [ ( "model " ++ show t ++ ": the model h reduces A_" ++ show v ++ " to A_" ++ show u
               , and [all xx as == all xx (hModel xx u v as) | k <- [0 .. 20 :: Int], let as = take (2 ^ v) (drop (k * 3) xs ++ [0 ..])]
               )
             ]
      | t <- [1 .. 30 :: Int]
      , (u, v) <- [(2, 4), (0, 1), (1, 2), (1, 3), (2, 3)]
      , let (xs, _) = subsetOf 95 [0 .. 510] (mkGen (fromIntegral (11000 + t)))
      , let xx = member xs
      ]

-- * The lemma of Dekker's theorem XIV

dekkerLemmaChecks :: [(String, Bool)]
dekkerLemmaChecks = concat [run t | t <- [1 .. 40 :: Int]]
  where
    bound = 300
    run t =
      let g0 = mkGen (fromIntegral (13000 + t))
          (rest, g1) = subsetOf 50 [n | n <- [0 .. bound + 10], n `mod` 3 /= 0] g0
          aSet = sortNub ([0, 3 .. bound + 10] ++ rest)
          outsideA = [n | n <- [1 .. bound], n `notElem` aSet]
          (m, g2) = pick outsideA g1
          (n, _) = pick (filter (/= m) outsideA) g2
          a = member aSet
          b x = a x || x == m
          inC x = x `mod` 3 == 0
          f x = if x == m then n else x
          p x = if x == m then 0 else x + 3
          gg x = if inC x || x == m then p x else x
       in [ ("model " ++ show t ++ ": m, n outside A, m /= n", not (a m) && not (a n) && m /= n)
          , ("model " ++ show t ++ ": A <=_m B by f", and [a x == b (f x) | x <- [0 .. bound]])
          , ("model " ++ show t ++ ": B <=_1 A by g", and [b x == a (gg x) | x <- [0 .. bound]])
          , ("model " ++ show t ++ ": g one-one", let vs = map gg [0 .. bound] in length (nub vs) == length vs)
          , ( "model " ++ show t ++ ": p maps C u {m} onto C"
            , sort [p x | x <- [0 .. bound], inC x || x == m] == [0, 3 .. 3 * (bound `div` 3) + 3]
            )
          ]

-- * Exercise 8-29 (b)

cylinderChecks :: [(String, Bool)]
cylinderChecks =
  concat [run t | t <- [1 .. 20 :: Int]]
    ++ [ ( "printed: the cylinder A = empty set and B = N; 1 is in A (+) B, so no map reduces A (+) B to A"
         , join (const False) (const True) 1
         )
       ]
    ++ concat [printedForward t | t <- [1 .. 20 :: Int]]
  where
    run t =
      let (cs, _) = subsetOf 50 [0 .. 9] (mkGen (fromIntegral (15000 + t)))
          a z = pi1 z `elem` cs
          f0 x = tau (pi1 x) (2 * pi2 x)
          f1 x = tau (pi1 x) (2 * pi2 x + 1)
          f k = if even k then f0 (k `div` 2) else f1 (k `div` 2)
          h x k = iterate f1 (f0 x) !! k
          dom = [0 .. 400]
          hs = [h x k | x <- [0 .. 30], k <- [0 .. 6]]
       in [ ("cylinder model " ++ show t ++ ": f reduces A (+) A to A", and [join a a k == a (f k) | k <- dom])
          , ("cylinder model " ++ show t ++ ": f one-one", let vs = map f dom in length (nub vs) == length vs)
          , ("cylinder model " ++ show t ++ ": h(x, n) = f_1^n(f_0(x)) one-one", length (nub hs) == length hs)
          , ("cylinder model " ++ show t ++ ": x in A <=> h(x, n) in A", and [a x == a (h x k) | x <- [0 .. 30], k <- [0 .. 6]])
          ]
    -- A (+) N <=_1 A for every A containing the multiples of 3.
    printedForward t =
      let (rest, _) = subsetOf 40 [n | n <- [0 .. 700], n `mod` 3 /= 0] (mkGen (fromIntegral (17000 + t)))
          a n = n `mod` 3 == 0 || n `elem` rest
          g k
            | even k = let x = k `div` 2 in if x `mod` 3 == 0 then 2 * x else x
            | otherwise = 6 * (k `div` 2) + 3
          dom = [0 .. 200]
       in [ ("printed (=>) fails: A (+) N <=_1 A by g, model " ++ show t, and [join a (const True) k == a (g k) | k <- dom])
          , ("printed (=>) fails: g one-one, model " ++ show t, let vs = map g dom in length (nub vs) == length vs)
          ]

-- * Exercise 8-42

shoenfieldChecks :: [(String, Bool)]
shoenfieldChecks = concat [run t | t <- [1 .. 60 :: Int]]
  where
    run t =
      let ((s, fam, _), g1) = starModel 6 (mkGen (fromIntegral (19000 + t)))
          e = concatMap block fam
          b m = member s m || member e m
          (aa, _) = subsetOf 40 [0 .. 30] g1
          (bExtra, _) = subsetOf 40 [0 .. 30] (snd (next g1))
          bb = sortNub (aa ++ bExtra)
          univ = [0 .. 31]
          compl xs = [n | n <- univ, n `notElem` xs]
          minus xs ys = [n | n <- xs, n `notElem` ys]
       in [ ("model " ++ show t ++ ": S_x subset B <=> S_x in the family, x = " ++ show x, all b (block x) == (x `elem` fam))
          | x <- [0 .. 6]
          ]
            ++ [ ( "model " ++ show t ++ ": the printed reading ('complement of S_x in the family') never holds, yet some S_x subset B"
                 , null fam || any (\x -> all b (block x)) [0 .. 6]
                 )
               , ("model " ++ show t ++ ": A-bar - (B - A) = B-bar for A subset B", minus (compl aa) (minus bb aa) == compl bb)
               ]
