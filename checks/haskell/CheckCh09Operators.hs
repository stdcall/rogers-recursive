-- | Checks of chapter 9, §§ 9.7-9.8 (printed pp. 189-202): enumeration
-- operators and recursive operators, and of exercises 9-58, 9-64
-- (pp. 208).  Scope ch08-09.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh09Operators.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh09Operators.hs
--      [--verbose]
--
-- An enumeration operator is given by a finite list W of pairs <x, D>
-- (D a finite set, the D_u of the definition of p. 191):
-- Phi(X) = {x | (exists <x, D> in W) [D subset X]}.  Single-valued sets
-- are sets of codes <a, b> = tau(a, b) (§ 5.3) with no two codes
-- <a, b>, <a, b'>, b /= b'; the models use the arguments and values
-- 0, 1, 2 (the codes 0, ..., 12).
--
-- What is checked, and where the expected values come from:
--
-- * § 9.7, exm:doubling-procedure and exm:k-enumerating-procedure
--   (p. 190): the doubling operator maps {1, 2} to {2, 4} and N to the
--   even numbers (on a bound); a constant operator.
-- * p. 191: the procedure that reads the inputs one at a time and puts
--   out x as soon as <x, D> in W has D among the inputs read gives the
--   same output for every order of the inputs (all orders of all sets of
--   at most 4 inputs from {0, ..., 4}).
-- * th:enumeration-operator-composition (p. 192): Phi_W1 Phi_W2 = Phi_W3
--   for the W3 obtained by choosing a pair of W2 for each element of D
--   (random W1, W2, all X subset {0, ..., 4}); th:enumeration-operator-
--   properties (p. 193): monotone, and the D of the pair is a finite
--   witness of continuity.
-- * ex:enumeration-operator-union-intersection (9-58, p. 208):
--   Psi(A) u Psi(B) subset Psi(A u B), Psi(A cap B) subset Psi(A) cap
--   Psi(B), both strict on examples.
-- * th:total-domain-recursive-operator (p. 195): if Phi(tau f) is
--   single-valued for all total f, then Phi(A) is single-valued for every
--   single-valued A (random W, all 27 total f, all 64 single-valued A on
--   the arguments 0, 1, 2).
-- * th:fundamental-operator-theorem (pp. 196-197), the set (*)
--   (eq:operator-extension-set) of W_sigma(z), for random W_z in their
--   standard order, in four readings: as corrected (D_s subset D_t, and
--   D_(s') u D_t not single-valued for the preceding <<x, y'>, s'>), as
--   printed (D_t subset D_s, D_(s') u D_s), and the two halves.  The
--   properties: (L) the lemma lem:operator-extension-monotone;
--   (R) Phi_sigma(z) maps single-valued sets to single-valued sets (a
--   recursive operator); (E) Phi_sigma(z)(tau f) = Phi_z(tau f) when the
--   latter is single-valued (all total f).  As corrected, (L), (R), (E)
--   hold on all models, and the D_t of the proof of (E) (p. 197) is in
--   W_sigma(z); as printed, (L) fails on W_z = (<<0, 0>, {<0, 0>}>) and
--   (R), (E) fail on the identity operator; with D_s subset D_t but
--   D_(s') u D_s, (L), (R) hold but (E) fails; with D_t subset D_s and
--   D_(s') u D_t, (L) fails.
-- * th:recursive-in-iff-characteristic-e-reducible (pp. 198-200): the
--   coding D_h(u,v) = (D_u x {1}) u (D_v x {0}) and h_1, h_2; the step of
--   p. 200: consistency of <x, y_q, u_q, v_q> with <x, y_m, u_m, v_m> and
--   D_(u_q) u D_(v_q) subset D_(u_m) u D_(v_m) give D_(u_q) subset
--   D_(u_m), D_(v_q) subset D_(v_m) (all compatible pairs on
--   {0, ..., 3}); the rule of C* gives a regular set.
-- * ex:partial-not-recursive-extension (9-64, p. 208): an enumeration
--   operator with Psi({<0, 0>}) supset {<0, 0>}, Psi({<1, 0>}) supset
--   {<0, 1>} is not single-valued on the total f with f(0) = f(1) = 0.
--
-- Not established: recursive enumerability of the sets, the effective
-- choices (sigma, Theta, g_1, g_2), anything beyond the finite models.
module Main (main) where

import Ch08Coding
import Data.List (permutations, sort)
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "9.7 examples of p. 190" exampleChecks
  group c "9.7 the procedure of p. 191 does not depend on the order" orderChecks
  group c "9.7 Th. XX, XXI: composition, monotone, continuous (pp. 192-193)" operatorChecks
  group c "9.9 ex. 9-58: union and intersection (p. 208)" unionChecks
  group c "9.8 Th. XXII (p. 195)" totalDomainChecks
  group c "9.8 Th. XXIII: the set (*) in four readings (pp. 196-197)" starChecks
  group c "9.8 Th. XXIV: the codings and the step of p. 200" codingStepChecks
  group c "9.9 ex. 9-64 (p. 208)" ex64Checks
  finish c "ch09-operators"

type Op = [(Integer, [Integer])]

phi :: Op -> [Integer] -> [Integer]
phi w xs = sortNub [x | (x, d) <- w, all (`elem` xs) d]

subset :: [Integer] -> [Integer] -> Bool
subset xs ys = all (`elem` ys) xs

union' :: [Integer] -> [Integer] -> [Integer]
union' xs ys = sortNub (xs ++ ys)

-- * Examples of p. 190

exampleChecks :: [(String, Bool)]
exampleChecks =
  [ ("doubling: Phi({1, 2}) = {2, 4}", phi doubling [1, 2] == [2, 4])
  , ("doubling: Phi(N) = E on [0, 200]", filter (<= 200) (phi doubling [0 .. 100]) == [0, 2 .. 200])
  ]
    ++ [ ("constant operator: Phi(X) = K-model for X = " ++ show xs, phi constant xs == [3, 5, 8])
       | xs <- subsetsOf [0 .. 4]
       ]
  where
    doubling = [(2 * y, [y]) | y <- [0 .. 100]]
    constant = [(3, []), (5, []), (8, [])]

-- * The procedure of p. 191

randomOp :: [Integer] -> [Integer] -> Int -> Int -> Gen -> (Op, Gen)
randomOp outs ins n p = draws n pair
  where
    pair g0 = let (x, g1) = pick outs g0; (d, g2) = subsetOf p ins g1 in ((x, d), g2)

procedure :: Op -> [Integer] -> [Integer]
procedure w inputs = go [] [] (Nothing : map Just inputs)
  where
    go _ out [] = sort out
    go seen out (i : is) =
      let seen' = maybe seen (: seen) i
          new = [x | (x, d) <- w, all (`elem` seen') d, x `notElem` out]
       in go seen' (sortNub (out ++ new)) is

orderChecks :: [(String, Bool)]
orderChecks =
  [ ("model " ++ show t ++ ", inputs " ++ show b ++ ": every order gives Phi(B)", all (\p -> procedure w p == phi w b) (permutations b))
  | t <- [1 .. 40 :: Int]
  , let (w, _) = randomOp [0 .. 4] [0 .. 4] 6 30 (mkGen (fromIntegral (51000 + t)))
  , b <- subsetsOf [0 .. 4]
  , length b <= 4
  ]

-- * Theorems XX, XXI

compose :: Op -> Op -> Op
compose w1 w2 = [(x, sortNub (concat ds)) | (x, d) <- w1, ds <- mapM (\y -> [d' | (y', d') <- w2, y' == y]) d]

operatorChecks :: [(String, Bool)]
operatorChecks = concat [run t | t <- [1 .. 100 :: Int]]
  where
    univ = [0 .. 4]
    run t =
      let g0 = mkGen (fromIntegral (53000 + t))
          (w1, g1) = randomOp univ univ 5 30 g0
          (w2, _) = randomOp univ univ 7 30 g1
          w3 = compose w1 w2
          sets = subsetsOf univ
       in [ ("model " ++ show t ++ ": Phi_W1 Phi_W2 = Phi_W3", and [phi w1 (phi w2 x) == phi w3 x | x <- sets])
          , ("model " ++ show t ++ ": monotone", and [phi w2 x `subset` phi w2 y | x <- sets, y <- sets, x `subset` y])
          , ("model " ++ show t ++ ": continuous, the finite D is a witness", and [x `elem` phi w2 d | a <- sets, (x, d) <- w2, d `subset` a])
          ]

-- * Exercise 9-58

unionChecks :: [(String, Bool)]
unionChecks =
  concat
    [ [ ("model " ++ show t ++ ": Psi(A) u Psi(B) subset Psi(A u B)", and [union' (phi w a) (phi w b) `subset` phi w (union' a b) | a <- sets, b <- sets])
      , ("model " ++ show t ++ ": Psi(A cap B) subset Psi(A) cap Psi(B)", and [phi w [n | n <- a, n `elem` b] `subset` [n | n <- phi w a, n `elem` phi w b] | a <- sets, b <- sets])
      ]
    | t <- [1 .. 60 :: Int]
    , let (w, _) = randomOp [0 .. 4] [0 .. 4] 6 35 (mkGen (fromIntegral (55000 + t)))
    ]
    ++ [ ("strict: W = {<0, {1, 2}>}: Psi({1}) u Psi({2}) = empty, Psi({1, 2}) = {0}", union' (phi [(0, [1, 2])] [1]) (phi [(0, [1, 2])] [2]) == [] && phi [(0, [1, 2])] [1, 2] == [0])
       , ("strict: W = {<0, {1}>, <0, {2}>}: Psi({1}) cap Psi({2}) = {0}, Psi(empty) = empty", phi [(0, [1]), (0, [2])] [1] == [0] && phi [(0, [1]), (0, [2])] [2] == [0] && null (phi [(0, [1]), (0, [2])] []))
       ]
    where
      sets = subsetsOf [0 .. 4]

-- * Single-valued sets of pairs

args, vals :: [Integer]
args = [0, 1, 2]
vals = [0, 1, 2]

pairCodes :: [Integer]
pairCodes = [tau a b | a <- args, b <- vals]

sv :: [Integer] -> Bool
sv xs = and [b == b' | z <- xs, z' <- xs, let (a, b) = untau z, let (a', b') = untau z', a == a']

partialFns :: [[Integer]]
partialFns = map (map (uncurry tau)) (go args)
  where
    go [] = [[]]
    go (a : as) = [p ++ rest | p <- [] : [[(a, b)] | b <- vals], rest <- go as]

totalFns :: [[Integer]]
totalFns = filter ((== length args) . length) partialFns

totalDomainChecks :: [(String, Bool)]
totalDomainChecks =
  [ ("model " ++ show t ++ ": Phi(tau f) single-valued for all total f => Phi(A) single-valued for all single-valued A", not (all (sv . phi w) totalFns) || all (sv . phi w) partialFns)
  | t <- [1 .. 400 :: Int]
  , let (w, _) = randomOp pairCodes pairCodes 4 15 (mkGen (fromIntegral (57000 + t)))
  ]
    ++ [("the hypothesis holds on some models", length [() | t <- [1 .. 400 :: Int], let (w, _) = randomOp pairCodes pairCodes 4 15 (mkGen (fromIntegral (57000 + t))), all (sv . phi w) totalFns] > 20)]

-- * The set (*) of theorem XXIII

-- | An element <<x, y>, s> of W_z, in the standard order of W_z.
type Entry = (Integer, Integer, [Integer])

data Reading = Corrected | Printed | HalfIncl | HalfUnion deriving (Eq, Show)

-- | <<x, y>, t> in W_sigma(z), by (*) in the given reading.
member :: Reading -> [Entry] -> Integer -> Integer -> [Integer] -> Bool
member r w x y t =
  sv t
    && or
      [ incl s && and [not (sv (union' s' (other s))) | (j, (x', _, s')) <- zip [0 :: Int ..] w, j < i, x' == x]
      | (i, (x0, y0, s)) <- zip [0 ..] w
      , x0 == x
      , y0 == y
      ]
  where
    incl s = if r `elem` [Corrected, HalfIncl] then s `subset` t else t `subset` s
    other s = if r `elem` [Corrected, HalfUnion] then t else s

phiZ :: [Entry] -> [Integer] -> [(Integer, Integer)]
phiZ w xs = sortNub [(x, y) | (x, y, s) <- w, s `subset` xs]

phiSigma :: Reading -> [Entry] -> [Integer] -> [(Integer, Integer)]
phiSigma r w xs = sortNub [(x, y) | (x, y, _) <- w, t <- subsetsOf xs, member r w x y t]

svPairs :: [(Integer, Integer)] -> Bool
svPairs ps = and [y == y' | (x, y) <- ps, (x', y') <- ps, x == x']

-- | (L) the lemma, (R) single-valued images, (E) agreement on total f.
propL, propR, propE :: Reading -> [Entry] -> Bool
propL r w =
  and
    [ not (member r w x y t) || member r w x y t1
    | t1 <- partialFns
    , t <- subsetsOf t1
    , (x, y, _) <- w
    ]
propR r w = all (svPairs . phiSigma r w) partialFns
propE r w = and [not (svPairs (phiZ w f)) || phiSigma r w f == phiZ w f | f <- totalFns]

-- | The D_t of the proof of (E), p. 197: D_t subset tau(f) with
-- Arg D_t = Arg D_s u Arg D_(s_1) u ... u Arg D_(s_k).
proofT :: [Entry] -> [Integer] -> Bool
proofT w f =
  not (svPairs (phiZ w f))
    || and
      [ member Corrected w x y t
      | (x, y) <- phiZ w f
      , let i = head' [j | (j, (x', y', s)) <- zip [0 :: Int ..] w, x' == x, y' == y, s `subset` f]
      , let (_, _, s) = w !! i
      , let preceding = [s' | (j, (x', _, s')) <- zip [0 ..] w, j < i, x' == x]
      , let argsT = sortNub (map (fst . untau) (concat (s : preceding)))
      , let t = sortNub [z | z <- f, fst (untau z) `elem` argsT]
      ]
  where
    head' (j : _) = j
    head' [] = error "no s"

randomW :: Int -> ([Entry], Gen)
randomW t =
  let g0 = mkGen (fromIntegral (59000 + t))
      (n, g1) = below 6 g0
      entry g = let (x, ga) = pick args g; (y, gb) = pick vals ga; (s, gc) = subsetOf 20 pairCodes gb in ((x, y, s), gc)
   in draws (n + 1) entry g1

identityW :: [Entry]
identityW = [(a, b, [tau a b]) | a <- args, b <- vals]

starChecks :: [(String, Bool)]
starChecks =
  concat
    [ [ ("model " ++ show t ++ ", corrected: (L) the lemma", propL Corrected w)
      , ("model " ++ show t ++ ", corrected: (R) a recursive operator", propR Corrected w)
      , ("model " ++ show t ++ ", corrected: (E) Phi_sigma(z)(tau f) = Phi_z(tau f)", propE Corrected w)
      , ("model " ++ show t ++ ", corrected: the D_t of p. 197 is in W_sigma(z)", all (proofT w) totalFns)
      , ("model " ++ show t ++ ", D_s subset D_t with D_(s') u D_s: (L), (R) hold", propL HalfIncl w && propR HalfIncl w)
      ]
    | t <- [1 .. 300 :: Int]
    , let (w, _) = randomW t
    ]
    ++ [ ("corrected, identity operator: (L), (R), (E)", propL Corrected identityW && propR Corrected identityW && propE Corrected identityW)
       , ("printed: (L) fails on W_z = (<<0, 0>, {<0, 0>}>), t = empty, t_1 = {<1, 0>}", member Printed w1 0 0 [] && not (member Printed w1 0 0 [tau 1 0]) && sv [tau 1 0])
       , ("printed: (R) fails on the identity operator: Phi_sigma(z)(empty) is not single-valued", not (svPairs (phiSigma Printed identityW [])))
       , ("printed: (E) fails on the identity operator and f = 0", let f = [tau a 0 | a <- args] in svPairs (phiZ identityW f) && phiSigma Printed identityW f /= phiZ identityW f)
       , ("printed: on the identity operator Phi_sigma(z) is constant, all 9 pairs", all (\a -> length (phiSigma Printed identityW a) == 9) partialFns)
       , ( "D_s subset D_t with D_(s') u D_s: (E) fails on (<<0, 1>, {<1, 1>}>, <<0, 2>, empty>) and f(1) = 0"
         , let w = [(0, 1, [tau 1 1]), (0, 2, [])]
               f = [tau 0 0, tau 1 0, tau 2 0]
            in phiZ w f == [(0, 2)] && null (phiSigma HalfIncl w f) && phiSigma Corrected w f == [(0, 2)]
         )
       , ("D_t subset D_s with D_(s') u D_t: (L) fails on W_z = (<<0, 0>, {<0, 0>}>)", member HalfUnion w1 0 0 [] && not (member HalfUnion w1 0 0 [tau 1 0]))
       , ("printed reading: some random model breaks (L)", any (\t -> not (propL Printed (fst (randomW t)))) [1 .. 300])
       , ("printed reading: some random model breaks (E)", any (\t -> not (propE Printed (fst (randomW t)))) [1 .. 300])
       ]
  where
    w1 = [(0, 0, [tau 0 0])]

-- * Theorem XXIV

-- | D_h(u,v) = (D_u x {1}) u (D_v x {0}).
hCode :: [Integer] -> [Integer] -> [Integer]
hCode u v = sortNub ([tau a 1 | a <- u] ++ [tau a 0 | a <- v])

h1, h2 :: [Integer] -> [Integer]
h1 t = sortNub [a | z <- t, let (a, b) = untau z, b == 1]
h2 t = sortNub [a | z <- t, let (a, b) = untau z, b == 0]

codingStepChecks :: [(String, Bool)]
codingStepChecks =
  [ ( "u = " ++ show u ++ ", v = " ++ show v ++ ": h_1, h_2 recover u, v; single-valued <=> D_u cap D_v = empty; D_h(u,v) subset tau(c_B) <=> D_u subset B & D_v subset B-bar"
    , h1 (hCode u v) == u && h2 (hCode u v) == v
        && sv (hCode u v) == all (`notElem` v) u
        && and [(hCode u v `subset` charGraph b) == (u `subset` b && all (`notElem` b) v) | b <- sets]
    )
  | u <- sets
  , v <- sets
  ]
    ++ [ ( "p. 200: consistency and D_(u_q) u D_(v_q) subset D_(u_m) u D_(v_m) give the inclusions"
         , and
             [ u1 `subset` u2 && v1 `subset` v2
             | (u1, v1) <- compatiblePairs
             , (u2, v2) <- compatiblePairs
             , union' u1 v1 `subset` union' u2 v2
             , all (`notElem` v2) u1
             , all (`notElem` u2) v1
             ]
         )
       , ("p. 200: the hypothesis occurs (non-vacuous)", length [() | (u1, v1) <- compatiblePairs, (u2, v2) <- compatiblePairs, union' u1 v1 `subset` union' u2 v2, all (`notElem` v2) u1, all (`notElem` u2) v1] > 100)
       ]
    ++ [ ("C* model " ++ show t ++ ": regular", regularC (cstar qs))
       | t <- [1 .. 200 :: Int]
       , let (qs, _) = draws 10 quad (mkGen (fromIntegral (61000 + t)))
       ]
  where
    sets = subsetsOf [0 .. 3]
    charGraph b = [tau a (if a `elem` b then 1 else 0) | a <- [0 .. 3]]
    compatiblePairs = [(u, v) | u <- sets, v <- sets, all (`notElem` v) u]
    quad g0 =
      let (x, g1) = below 3 g0
          (y, g2) = below 2 g1
          (lab, g3) = draws 4 (below 3) g2
          u = [a | (a, l) <- zip [0 ..] lab, l == 1]
          v = [a | (a, l) <- zip [0 ..] lab, l == 2]
       in ((toInteger x, toInteger y, u, v), g3)
    consistentQ (_, _, u1, v1) (_, _, u2, v2) = all (`notElem` v2) u1 && all (`notElem` v1) u2
    cstar = go []
      where
        go kept [] = reverse kept
        go kept (q@(x, _, _, _) : qs)
          | any (\k@(x', _, _, _) -> x' == x && consistentQ q k) kept = go kept qs
          | otherwise = go (q : kept) qs
    regularC qs =
      and [all (`notElem` v) u | (_, _, u, v) <- qs]
        && and [not (consistentQ p q) | p@(x1, _, _, _) <- qs, q@(x2, _, _, _) <- qs, x1 == x2, p /= q]

-- * Exercise 9-64

ex64Checks :: [(String, Bool)]
ex64Checks =
  [ ("Psi({<0, 0>}) = {<0, 0>}", phi w [tau 0 0] == [tau 0 0])
  , ("Psi({<1, 0>}) = {<0, 1>}", phi w [tau 1 0] == [tau 0 1])
  , ("f(0) = f(1) = 0: Phi(tau f) contains <0, 0>, <0, 1>, not single-valued", sv [tau 0 0, tau 1 0, tau 2 0] && not (sv (phi w [tau 0 0, tau 1 0, tau 2 0])))
  ]
    ++ [ ("any W extending these values (extra pairs of model " ++ show t ++ ") is not single-valued on tau f", not (sv (phi (w ++ extra) [tau 0 0, tau 1 0, tau 2 0])))
       | t <- [1 .. 50 :: Int]
       , let (extra, _) = randomOp pairCodes pairCodes 3 30 (mkGen (fromIntegral (63000 + t)))
       ]
  where
    w = [(tau 0 0, [tau 0 0]), (tau 0 1, [tau 1 0])]
