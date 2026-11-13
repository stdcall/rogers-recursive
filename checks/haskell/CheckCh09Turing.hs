-- | Checks of chapter 9, §§ 9.1-9.6 (printed pp. 167-189), and of the
-- exercises of these sections (pp. 202-207).  Scope ch08-09.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh09Turing.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh09Turing.hs [--verbose]
--
-- What is checked, and where the expected values come from (printed pages
-- and our labels):
--
-- * § 9.2, the oracle machine of p. 170 (quadruples q_0 1 B q_1, ...,
--   q_6 B R q_4; input x as x + 1 ones, the machine on the leftmost 1,
--   output the number of ones when it stops, § 1.5; "q_2 1 q_3 q_4" asks
--   whether the number n of ones on the tape is in X): for x <= 40 and
--   many X it stops with output c_X(x) after exactly one question, n = x.
-- * § 9.2, the diagram of p. 171: its only stopping branch has
--   D' = {7, 11}, D'' = empty (printed).  On random oracle computations
--   (finite trees of questions about {0, ..., 5}, repeated questions
--   answered as before): every branch of the diagram has D' cap D'' empty;
--   the computation with X follows the branch with D' subset X,
--   D'' subset X-bar; the set {<x, y, D', D''>} of the stopping branches is
--   regular (ex:w-h-regular) and phi^X of it is the computed function.
-- * th:regularization (pp. 172-173) and the definition of phi_z^X: the
--   rule of rho (drop a quadruple that is not compatible or is consistent
--   with one already put in) gives a regular set, keeps a regular set,
--   and then at most one quadruple with given x matches X; the search of
--   p. 173 (as corrected: D_(u') subset X, D_(v') subset X-bar for the
--   quadruple <x', y', u', v'> that has appeared) finds it.
-- * § 9.5, p. 181: g(0) = f_0(0) + 1, g(n + 1) = mu z [z > g(n) &
--   z > f_(n+1)(n + 1)] is not majorized by any f_n of a list of total
--   functions; the complement of Post's S (th:simple-set-exists) is
--   majorized by lambda x [2x] (random selections).
-- * th:hyperimmune-disjoint-finite-sets (p. 182): (=>) the maximum of
--   D_(f(0)) u ... u D_(f(y)) majorizes A; (<=) h(0) = g(0),
--   h(n + 1) = g(h(n) + 1) increase, at least h(n) + 2 elements of A are
--   <= h(n + 1), and D^(n+1) = {h(n) + 1, ..., h(n + 1)} meets A; the
--   numbers <= h(n + 1) outside D^(n+1) are the first h(n) + 1 (as
--   corrected), not one number (as printed), on random A and majorants.
-- * th:dekker (p. 183) on random one-one f (eventually increasing):
--   (ii) a majorant g of B-bar gives x in A <=> x in {f(0), ..., f(g(x))};
--   (iii) x in B <=> C cap A /= empty, C = {0..f(x)} - {f(0)..f(x)};
--   (iv) with n_z the largest of the first z + 1 elements of B-bar,
--   z <= f(n_z) and z in A <=> z in {f(0), ..., f(n_z)}: the procedure
--   decides A (as corrected), not B (as printed: they differ on the model).
-- * th:tt-complete-not-hypersimple (pp. 185-187): 2^(2^d) 2^d =
--   2^(2^d + d) < 2^(2^(d+1)) (d <= 10; general: Lean
--   derived_count_lt); the derived truth table of the example of p. 186;
--   without repeated numbers a set D' of k elements outside A has
--   2^(2^k) derived truth tables, with repeated numbers (allowed by the
--   definition, p. 146) more; the blocks {0..f(0)}, {f(n) + 1..f(n + 1)}
--   meeting A-bar give a majorant f of A-bar (as corrected); the printed
--   "A is majorized by f" fails on f(n) = 2n + 1, A = {4n + 3}.
-- * th:nerode (pp. 187-188): (ii) phi_(z_0)^X is the characteristic
--   function of {x | f(x) is satisfied on X}, not of X (as printed); (iii)
--   for random oracle computations that stop for every X, the
--   tt-condition built from the finite diagram (its questions x_1 < ... <
--   x_n, alpha(w) = [phi^Y(x) /= 0], Y = {x_i | w_i = 1}) is satisfied on B
--   exactly when phi^B(x) /= 0, for all B.
-- * ex:retraceable-sets (i) (p. 206), as corrected (B subset A): tracing
--   from the least b in B with b >= x decides x in A (random A, B); (iv):
--   the labels of the tree of p. 206 are n -> 2n + 1, 2n + 2; every branch
--   is retraced by n -> (n - 1) div 2 and its k-th element lies in
--   {2^k - 1, ..., 2^(k+1) - 2}, so a recursive function majorizes it.
-- * ex:function-tree (ii) (p. 205): (n_1, ..., n_k) ->
--   1^(n_1) 0 ... 1^(n_k) 0 embeds the function tree in the binary tree
--   (entries <= 2, length <= 3).
--
-- Not established: recursive enumerability, the relativized theory, the
-- general theorems; the models are finite and check the stated steps on
-- the stated ranges only.
module Main (main) where

import Ch08Coding
import Data.List (nub, sort)
import Data.Maybe (catMaybes, isJust)
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "9.2 the oracle machine of p. 170 computes c_X" oracleMachineChecks
  group c "9.2 the diagram of p. 171 and W_h(z)" diagramChecks
  group c "9.2 Th. VI: regularization and phi_z^X (pp. 172-173)" regularChecks
  group c "9.5 g not majorized; S-bar majorized by 2x (p. 181)" majorizeChecks
  group c "9.5 Th. XV (Kuznetsov, Medvedev, Uspensky) (p. 182)" kmuChecks
  group c "9.5 Th. XVI (Dekker) (p. 183)" dekkerChecks
  group c "9.6 Th. XVIII (Post) (pp. 185-187)" postChecks
  group c "9.6 Th. XIX (Nerode) (pp. 187-188)" nerodeChecks
  group c "9.9 ex. 9-44 (i), (iv): retraceable sets (p. 206)" retraceChecks
  group c "9.9 ex. 9-42 (ii): the function tree in the binary tree (p. 205)" treeEmbedChecks
  finish c "ch09-turing"

member :: [Integer] -> Integer -> Bool
member xs n = n `elem` xs

-- * The oracle machine of p. 170

data Op = Write Bool Int | MoveR Int | MoveL Int | Ask Int Int

type Machine = [((Int, Bool), Op)]

-- | q_0 1 B q_1, q_1 B R q_2, q_2 1 q_3 q_4, q_2 B q_3 q_4, q_3 B 1 q_7,
-- q_3 1 B q_5, q_5 B R q_3, q_4 1 B q_6, q_6 B R q_4 (True = 1, False = B).
printedMachine :: Machine
printedMachine =
  [ ((0, True), Write False 1)
  , ((1, False), MoveR 2)
  , ((2, True), Ask 3 4)
  , ((2, False), Ask 3 4)
  , ((3, False), Write True 7)
  , ((3, True), Write False 5)
  , ((5, False), MoveR 3)
  , ((4, True), Write False 6)
  , ((6, False), MoveR 4)
  ]

data Tape = Tape [Bool] Bool [Bool]

ones :: Tape -> Integer
ones (Tape l c r) = toInteger (length (filter id l) + fromEnum c + length (filter id r))

-- | Output and the numbers asked about, or Nothing after the step bound.
runOracle :: Machine -> (Integer -> Bool) -> Integer -> Maybe (Integer, [Integer])
runOracle m x input = go (1000 :: Int) 0 start []
  where
    start = Tape [] True (replicate (fromInteger input) True)
    go 0 _ _ _ = Nothing
    go k q t@(Tape l c r) asked = case lookup (q, c) m of
      Nothing -> Just (ones t, reverse asked)
      Just (Write s q') -> go (k - 1) q' (Tape l s r) asked
      Just (MoveR q') -> case r of
        (d : r') -> go (k - 1) q' (Tape (c : l) d r') asked
        [] -> go (k - 1) q' (Tape (c : l) False []) asked
      Just (MoveL q') -> case l of
        (d : l') -> go (k - 1) q' (Tape l' d (c : r)) asked
        [] -> go (k - 1) q' (Tape [] False (c : r)) asked
      Just (Ask qy qn) ->
        let n = ones t in go (k - 1) (if x n then qy else qn) t (n : asked)

oracleMachineChecks :: [(String, Bool)]
oracleMachineChecks =
  [ ("the quadruples are consistent", length (nub (map fst printedMachine)) == length printedMachine)
  ]
    ++ [ ( "X = " ++ name ++ ", x = " ++ show x ++ ": output c_X(x), one question, about x"
         , runOracle printedMachine xx x == Just (if xx x then 1 else 0, [x])
         )
       | (name, xx) <- oracles
       , x <- [0 .. 40]
       ]
  where
    oracles =
      [("empty", const False), ("N", const True), ("evens", even), ("primes", prime)]
        ++ [("subset " ++ show s, member s) | s <- subsetsOf [0 .. 4]]
        ++ [ ("random " ++ show t, member s)
           | t <- [1 .. 10 :: Int]
           , let (s, _) = subsetOf 50 [0 .. 40] (mkGen (fromIntegral (21000 + t)))
           ]
    prime n = n > 1 && all (\d -> n `mod` d /= 0) [2 .. n - 1]

-- * Oracle computations as trees of questions

data DTree = Q Integer DTree DTree | Out Integer | Loop deriving (Eq, Show)

-- | The diagram: a question already answered on the branch is not asked
-- again (p. 171).
diagram :: DTree -> DTree
diagram = go []
  where
    go seen (Q n yes no) = case lookup n seen of
      Just True -> go seen yes
      Just False -> go seen no
      Nothing -> Q n (go ((n, True) : seen) yes) (go ((n, False) : seen) no)
    go _ t = t

-- | The branches: D', D'' and the end (Just output, or Nothing when the
-- branch does not stop).
branches :: DTree -> [([Integer], [Integer], Maybe Integer)]
branches (Q n yes no) =
  [(n : d1, d2, e) | (d1, d2, e) <- branches yes] ++ [(d1, n : d2, e) | (d1, d2, e) <- branches no]
branches (Out y) = [([], [], Just y)]
branches Loop = [([], [], Nothing)]

runTree :: (Integer -> Bool) -> DTree -> Maybe Integer
runTree x (Q n yes no) = runTree x (if x n then yes else no)
runTree _ (Out y) = Just y
runTree _ Loop = Nothing

-- | The diagram of p. 171: 7?, then 11? on "Да" (and the end on "Да"),
-- 17? on "Нет"; the other branches go on ("...").
printedDiagram :: DTree
printedDiagram = Q 7 (Q 11 (Out 0) Loop) (Q 17 Loop Loop)

randomTree :: Int -> Bool -> [Integer] -> Gen -> (DTree, Gen)
randomTree depth total univ g0
  | depth == 0 = leaf g0
  | otherwise =
      let (r, g1) = below 10 g0
       in if r < 3
            then leaf g1
            else
              let (n, g2) = pick univ g1
                  (a, g3) = randomTree (depth - 1) total univ g2
                  (b, g4) = randomTree (depth - 1) total univ g3
               in (Q n a b, g4)
  where
    leaf g =
      let (r, g1) = below 10 g
          (y, g2) = below 2 g1
       in if not total && r < 2 then (Loop, g2) else (Out (toInteger y), g2)

type Quad = (Integer, Integer, [Integer], [Integer])

compatible :: Quad -> Bool
compatible (_, _, u, v) = all (`notElem` v) u

consistent :: Quad -> Quad -> Bool
consistent (_, _, u1, v1) (_, _, u2, v2) = all (`notElem` v2) u1 && all (`notElem` v1) u2

regular :: [Quad] -> Bool
regular qs =
  all compatible qs
    && and [not (consistent p q) | p@(x1, _, _, _) <- qs, q@(x2, _, _, _) <- qs, x1 == x2, p /= q]

matches :: (Integer -> Bool) -> Quad -> Bool
matches x (_, _, u, v) = all x u && all (not . x) v

phiOf :: [Quad] -> (Integer -> Bool) -> Integer -> [Integer]
phiOf qs x n = [y | q@(x', y, _, _) <- qs, x' == n, matches x q]

diagramChecks :: [(String, Bool)]
diagramChecks =
  [ ( "p. 171: the only stopping branch has D' = {7, 11}, D'' = empty"
    , [(sort d1, sort d2) | (d1, d2, Just _) <- branches printedDiagram] == [([7, 11], [])]
    )
  , ("p. 171: D' cap D'' = empty on every branch", and [all (`notElem` d2) d1 | (d1, d2, _) <- branches printedDiagram])
  ]
    ++ concat [run t | t <- [1 .. 150 :: Int]]
  where
    univ = [0 .. 5]
    run t =
      let (trees, _) = draws 3 (randomTree 6 False univ) (mkGen (fromIntegral (23000 + t)))
          diags = map diagram trees
          w = [(toInteger x, y, sortNub d1, sortNub d2) | (x, d) <- zip [0 :: Int ..] diags, (d1, d2, Just y) <- branches d]
       in [ ("model " ++ show t ++ ": D' cap D'' = empty on every branch", and [all (`notElem` d2) d1 | d <- diags, (d1, d2, _) <- branches d])
          , ("model " ++ show t ++ ": the set of stopping branches is regular (ex. 9-4)", regular w)
          ]
            ++ [ ( "model " ++ show t ++ ", X = " ++ show s ++ ": the computation follows the branch of X; phi^X of the set = the computation"
                 , and
                     [ runTree xx tr == runTree xx d
                         && [e | (d1, d2, e) <- branches d, all xx d1, all (not . xx) d2] == [runTree xx d]
                         && phiOf w xx (toInteger x) == maybe [] pure (runTree xx tr)
                     | (x, tr, d) <- zip3 [0 :: Int ..] trees diags
                     ]
                 )
               | s <- subsetsOf univ
               , let xx = member s
               ]

-- | The rule of rho (p. 173).
rho :: [Quad] -> [Quad]
rho = go []
  where
    go kept [] = reverse kept
    go kept (q@(x, _, _, _) : qs)
      | not (compatible q) = go kept qs
      | any (\k@(x', _, _, _) -> x' == x && consistent q k) kept = go kept qs
      | otherwise = go (q : kept) qs

randomQuads :: Int -> Gen -> ([Quad], Gen)
randomQuads n = draws n quad
  where
    quad g0 =
      let (x, g1) = below 3 g0
          (y, g2) = below 4 g1
          (u, g3) = subsetOf 25 [0 .. 3] g2
          (v, g4) = subsetOf 25 [0 .. 3] g3
       in ((toInteger x, toInteger y, u, v), g4)

-- | The search of p. 173: the first quadruple <x', y', u', v'> that
-- appears with x' = x, D_(u') subset X, D_(v') subset X-bar.
search :: [Quad] -> (Integer -> Bool) -> Integer -> Maybe Integer
search qs x n = case [y | q@(x', y, _, _) <- qs, x' == n, matches x q] of
  (y : _) -> Just y
  [] -> Nothing

regularChecks :: [(String, Bool)]
regularChecks = concat [run t | t <- [1 .. 300 :: Int]]
  where
    run t =
      let (qs, _) = randomQuads 12 (mkGen (fromIntegral (25000 + t)))
          r = rho qs
       in [ ("model " ++ show t ++ ": W_rho(z) regular", regular r)
          , ("model " ++ show t ++ ": rho keeps the regular W_rho(z)", rho r == r)
          , ("model " ++ show t ++ ": W_rho(z) subset W_z", all (`elem` qs) r)
          , ( "model " ++ show t ++ ": at most one quadruple per x matches each X; the search finds it"
            , and
                [ length (phiOf r xx n) <= 1 && search r xx n == (case phiOf r xx n of { [y] -> Just y; _ -> Nothing })
                | s <- subsetsOf [0 .. 3]
                , let xx = member s
                , n <- [0 .. 2]
                ]
            )
          ]
            ++ [ ("model " ++ show t ++ ": a regular W_z is kept by rho", regular qs <= (rho qs == nubKeep qs))
               ]
    nubKeep = nub

-- * Majorizing (p. 181)

majorizeChecks :: [(String, Bool)]
majorizeChecks =
  [ ("g strictly increases, n = " ++ show n, g (n + 1) > g n) | n <- [0 .. 18]
  ]
    ++ [ ("g(n) > f_n(n), so f_n does not majorize Val g, n = " ++ show n, g n > fs n n) | n <- [0 .. 19]
       ]
    ++ concat [postRun t | t <- [1 .. 40 :: Int]]
  where
    funcs :: [Integer -> Integer]
    funcs = cycle [const 7, \n -> n * n, \n -> 2 ^ n, \n -> n ^ (3 :: Int) + 5, \n -> product [1 .. n], \n -> 3 * n + 100]
    fs n = funcs !! fromInteger n
    g :: Integer -> Integer
    g 0 = fs 0 0 + 1
    g n = let prev = g (n - 1) in max prev (fs n n) + 1
    postRun t =
      let sSet = catMaybes (selections t)
          comp = [n | n <- [0 .. 130], n `notElem` sSet]
       in [ ("Post model " ++ show t ++ ": the k-th element of S-bar is <= 2k, k = " ++ show k, comp !! fromInteger k <= 2 * k)
          | k <- [0 .. 60]
          ]
    selections t =
      let go x gen
            | x > 65 = []
            | otherwise =
                let (r, g1) = below 3 gen
                    (d, g2) = below 30 g1
                 in (if r == 0 then Nothing else Just (2 * toInteger x + 1 + toInteger d)) : go (x + 1) g2
       in go (0 :: Int) (mkGen (fromIntegral (27000 + t)))

-- * Kuznetsov, Medvedev, Uspensky

-- | The elements of a random "infinite" set below the bound, in order.
randomA :: Int -> Integer -> Gen -> ([Integer], Gen)
randomA p bound = subsetOf p [0 .. bound]

kmuChecks :: [(String, Bool)]
kmuChecks = concat [forward t | t <- [1 .. 80 :: Int]] ++ concat [backward t | t <- [1 .. 200 :: Int]] ++ printedReading
  where
    forward t =
      let (a, g1) = randomA 30 3000 (mkGen (fromIntegral (29000 + t)))
          (ds, _) = disjointMeeting a 25 g1
          gmax y = maximum (concat (take (y + 1) ds))
       in [ ("(=>) model " ++ show t ++ ": max of D_f(0..y) >= z_y, y = " ++ show y, gmax y >= a !! y)
          | y <- [0 .. length ds - 1]
          ]
    -- disjoint finite sets, each with an element of a
    disjointMeeting a k g0 =
      let (anchors, g1) = shuffle (take 200 a) g0
          go [] _ g = ([], g)
          go (x : xs) used g =
            let (extra, g') = subsetOf 3 [n | n <- [0 .. 3000], n `notElem` used, n `notElem` anchors] g
                d = x : take 4 extra
                (rest, g'') = go xs (used ++ d) g'
             in (d : rest, g'')
       in go (take k anchors) [] g1
    backward t =
      let (a, g1) = randomA 30 20000 (mkGen (fromIntegral (31000 + t)))
          (slack, _) = draws 2000 (below 6) g1
          gfun k = a !! fromInteger k + toInteger (slack !! fromInteger k)
          hs = takeWhile (< 1900) (iterate (\hn -> gfun (hn + 1)) (gfun 0))
          countUpTo m = toInteger (length (takeWhile (<= m) a))
          dBlock n = [hs !! (n - 1) + 1 .. hs !! n]
       in [ ("(<=) model " ++ show t ++ ": h increases", and (zipWith (<) hs (drop 1 hs)))
          , ("(<=) model " ++ show t ++ ": D^(0) meets A", any (member a) [0 .. head' hs])
          ]
            ++ [ ( "(<=) model " ++ show t ++ ", n = " ++ show (n - 1) ++ ": at least h(n) + 2 elements of A <= h(n + 1); D^(n+1) meets A; the first h(n) + 1 numbers are outside D^(n+1)"
                 , countUpTo (hs !! n) >= hs !! (n - 1) + 2
                     && any (member a) (dBlock n)
                     && toInteger (length [m | m <- [0 .. hs !! n], m `notElem` dBlock n]) == hs !! (n - 1) + 1
                 )
               | n <- [1 .. length hs - 1]
               ]
    head' (x : _) = x
    head' [] = 0
    -- The printed "all except the (h(n) + 1)-th": exactly one number missing.
    printedReading =
      [ ( "printed reading of D^(n+1): one missing number; it fails once h(n) >= 1"
        , let a = [0, 2 ..]
              gfun k = a !! fromInteger k
              hs = take 6 (iterate (\hn -> gfun (hn + 1)) (gfun 0))
           in or [length [m | m <- [0 .. hs !! n], m < hs !! (n - 1) + 1] /= 1 | n <- [1 .. 5]]
        )
      ]

-- * Dekker's theorem

dekkerChecks :: [(String, Bool)]
dekkerChecks = concat [run t | t <- [1 .. 120 :: Int]] ++ [("the procedure decides A and not B on some model", or [differs t | t <- [1 .. 120 :: Int]])]
  where
    model t =
      let lf = 40
          big = 300
          (vals, _) = shuffle [0 .. big - 1] (mkGen (fromIntegral (33000 + t)))
          start = take lf vals
          f y = if y < lf then start !! y else big + toInteger y
          minimalPt x = x >= lf || all (\y -> f x < f y) [x + 1 .. lf - 1]
          bSet x = not (minimalPt x)
          aSet = sortNub (start ++ [big + toInteger y | y <- [lf .. lf + 400]])
          mins = filter minimalPt [0 ..]
       in (lf, big, f, bSet, member aSet, mins)
    run t =
      let (lf, big, f, bSet, a, mins) = model t
          (slack, _) = draws 400 (below 4) (mkGen (fromIntegral (35000 + t)))
          g x = mins !! x + slack !! x
          zs = [0 .. fromInteger big + 30]
       in [ ("model " ++ show t ++ ": f one-one", let vs = map f [0 .. lf + 50] in length (nub vs) == length vs)
          , ("model " ++ show t ++ ": B-bar = the minimal points, infinite (all x >= " ++ show lf ++ ")", all (not . bSet) [lf .. lf + 100])
          , ( "model " ++ show t ++ ": (ii) x in A <=> x in {f(0), ..., f(g(x))}"
            , and [a (toInteger x) == (toInteger x `elem` map f [0 .. g x]) | x <- zs]
            )
          , ( "model " ++ show t ++ ": (iii) x in B <=> ({0..f(x)} - {f(0)..f(x)}) meets A"
            , and [bSet x == any a [n | n <- [0 .. f x], n `notElem` map f [0 .. x]] | x <- [0 .. lf + 10]]
            )
          , ( "model " ++ show t ++ ": (iv) z <= f(n_z) and z in A <=> z in {f(0), ..., f(n_z)}"
            , and [let nz = mins !! z in toInteger z <= f nz && a (toInteger z) == (toInteger z `elem` map f [0 .. nz]) | z <- zs]
            )
          ]
    differs t =
      let (_, big, f, bSet, _, mins) = model t
       in or [(toInteger z `elem` map f [0 .. mins !! z]) /= bSet z | z <- [0 .. fromInteger big]]

-- * Post's theorem XVIII

-- | The derived truth table (p. 186), positional: 1 for the places in A,
-- the variables w_1, w_2, ... for the others, in order.
derived :: (Integer -> Bool) -> TT -> BF
derived inA (TT xs a) = fromFn n (\ws -> apply a (fill xs ws))
  where
    n = length (filter (not . inA) xs)
    fill [] _ = []
    fill (y : ys) ws
      | inA y = True : fill ys ws
      | otherwise = case ws of
          (w : ws') -> w : fill ys ws'
          [] -> False : fill ys []

postChecks :: [(String, Bool)]
postChecks =
  [ ("2^(2^d) 2^d = 2^(2^d + d) < 2^(2^(d+1)), d = " ++ show d, (2 :: Integer) ^ (2 ^ d :: Integer) * 2 ^ d == 2 ^ (2 ^ d + d) && (2 :: Integer) ^ (2 ^ d + d) < 2 ^ (2 ^ (d + 1) :: Integer))
  | d <- [0 .. 10 :: Integer]
  ]
    ++ [ ( "p. 186: the derived table of <<x1, x2, x3, x4>, alpha>, x1, x3 in A, is lambda w1 w2 [alpha(1, w1, 1, w2)], alpha = " ++ show m
         , derived (`elem` [1, 3]) (TT [1, 2, 3, 4] a) == fromFn 2 (\ws -> apply a [True, arg 1 ws, True, arg 2 ws])
         )
       | a@(BF _ m) <- allBF 4
       , m `mod` 97 == 0
       ]
    ++ [ ( "no repeated numbers: D' with " ++ show k ++ " elements outside A has 2^(2^k) derived tables"
         , length (nub [derived inA (TT xs a) | n <- [1 .. 3], xs <- distinctTuples n univ, sortNub (filter (not . inA) xs) == d', a <- allBF n]) == 2 ^ (2 ^ k :: Int)
         )
       | (k, d') <- [(1, [10]), (2, [10, 11])]
       ]
    ++ [ ( "repeated numbers: D' = {10} has more than 2^(2^1) derived tables (orders <= 3)"
         , length (nub [derived inA (TT xs a) | n <- [1 .. 3], xs <- tuples n univ, sortNub (filter (not . inA) xs) == [10], a <- allBF n]) > 4
         )
       ]
    ++ concat [blocks t | t <- [1 .. 100 :: Int]]
    ++ [ ( "printed 'A majorized by f' fails: f(n) = 2n + 1, A = {4n + 3}; A-bar meets every block, the n-th element of A exceeds f(n)"
         , let f n = 2 * n + 1
               a n = n `mod` 4 == 3
               blks = [0 .. f 0] : [[f n + 1 .. f (n + 1)] | n <- [0 .. 50]]
               aElems = filter a [0 ..]
            in all (any (not . a)) blks && and [aElems !! fromInteger n > f n | n <- [0 .. 50]]
         )
       ]
  where
    inA = (`elem` [0, 1])
    univ = [0, 1, 10, 11]
    distinctTuples 0 _ = [[]]
    distinctTuples j ys = [y : rest | y <- ys, rest <- distinctTuples (j - 1) (filter (/= y) ys)]
    tuples 0 _ = [[]]
    tuples j ys = [y : rest | y <- ys, rest <- tuples (j - 1) ys]
    blocks t =
      let g0 = mkGen (fromIntegral (37000 + t))
          (steps, g1) = draws 40 (below 6) g0
          fs = scanl1 (+) (map (toInteger . (+ 1)) steps)
          f n = fs !! fromInteger n
          blk 0 = [0 .. f 0]
          blk n = [f (n - 1) + 1 .. f n]
          (picks, g2) = draws 40 next g1
          holes = [let b = blk n in b !! fromIntegral (w `mod` fromIntegral (length b)) | (n, w) <- zip [0 .. 39] picks]
          (others, _) = subsetOf 30 [0 .. f 39] g2
          aBar = sortNub (holes ++ others)
       in [ ("model " ++ show t ++ ": every block meets A-bar", all (\n -> any (`elem` aBar) (blk n)) [0 .. 39])
          , ("model " ++ show t ++ ": f majorizes A-bar (as corrected)", and [aBar !! fromInteger n <= f n | n <- [0 .. 39]])
          ]

-- * Nerode's theorem XIX

nerodeChecks :: [(String, Bool)]
nerodeChecks = concat [run t | t <- [1 .. 200 :: Int]] ++ printedII
  where
    univ = [0 .. 5]
    run t =
      let (tr, _) = randomTree 5 True univ (mkGen (fromIntegral (39000 + t)))
          d = diagram tr
          qs = sortNub (questions d)
          alpha = fromFn (length qs) (\ws -> runTree (member [x | (x, True) <- zip qs ws]) d /= Just 0)
       in [ ("model " ++ show t ++ ", B = " ++ show b ++ ": alpha(c_B(x_1), ..., c_B(x_n)) = 1 <=> phi^B(x) /= 0", isJust (runTree (member b) tr) && sat (member b) (TT qs alpha) == (runTree (member b) tr /= Just 0))
          | b <- subsetsOf univ
          ]
    questions (Q n a b) = n : questions a ++ questions b
    questions _ = []
    printedII =
      [ ("(ii): phi_(z_0)^X is a characteristic function (values 0, 1), model " ++ show t, all (`elem` [0, 1]) (phis t))
      | t <- [1 .. 30 :: Int]
      ]
        ++ [ ( "(ii): phi_(z_0)^X is the characteristic function of {x | f(x) is satisfied on X}, not of X (printed): they differ on some model"
             , or [or [(p == 1) /= (x `elem` snd (phiModel t)) | (x, p) <- zip [0 ..] (phis t)] | t <- [1 .. 30 :: Int]]
             )
           ]
    phiModel t =
      let g0 = mkGen (fromIntegral (41000 + t))
          cond g = let (n, g') = below 3 g; (xs, g'') = draws (n + 1) (pick [0 .. 7]) g'; (w, g3) = next g'' in (TT xs (BF (n + 1) (toInteger w `mod` (2 ^ (2 ^ (n + 1) :: Integer)))), g3)
          (conds, g1) = draws 8 cond g0
          (xs0, _) = subsetOf 50 [0 .. 7] g1
       in (conds, xs0)
    phis t = let (conds, xs0) = phiModel t in [if sat (member xs0) cd then 1 else 0 :: Int | cd <- conds]

-- * Exercise 9-44

retraceChecks :: [(String, Bool)]
retraceChecks = concat [run t | t <- [1 .. 40 :: Int]] ++ treeChecks
  where
    run t =
      let g0 = mkGen (fromIntegral (43000 + t))
          (a, g1) = subsetOf 20 [0 .. 600] g0
          (b, _) = subsetOf 30 a g1
          -- psi on A: the nearest smaller element, the least element fixed;
          -- off A (needed only for the printed reading) x - 1.
          preds = zip a (take 1 a ++ a)
          psi x = case lookup x preds of
            Just p -> p
            Nothing -> max 0 (x - 1)
          chain y = y : steps y
          steps y = let z = psi y in if z == y then [] else z : steps z
          decide bs x = case filter (>= x) bs of
            (y : _) -> x `elem` chain y
            [] -> False
          top = case reverse b of
            (y : _) -> y
            [] -> 0
       in [ ("model " ++ show t ++ ": psi retraces A", and [psi x == (case filter (< x) a of { [] -> x; s -> last s }) | x <- a])
          , ("model " ++ show t ++ ": (i), B subset A: x in A <=> x on the chain from the least b >= x in B", and [decide b x == (x `elem` a) | x <- [0 .. top]])
          , ("model " ++ show t ++ ": printed B supset A (B = N): the chain from b = x answers wrongly for some x", or [decide [0 .. 700] x /= (x `elem` a) | x <- [0 .. top]])
          ]
    treeChecks =
      [ ("p. 206: the labels 0; 1, 2; 3, 4 under 1; 5, 6 under 2 are n -> 2n + 1, 2n + 2", [[2 * n + 1, 2 * n + 2] | n <- [0, 1, 2 :: Integer]] == [[1, 2], [3, 4], [5, 6]])
      ]
        ++ concat
          [ let (bits, _) = draws 25 (below 2) (mkGen (fromIntegral (45000 + t)))
                path = scanl (\n bit -> 2 * n + 1 + toInteger bit) 0 bits
                psi n = if n == 0 then 0 else (n - 1) `div` 2
             in [ ("branch " ++ show t ++ ": increasing", and (zipWith (<) path (drop 1 path)))
                , ("branch " ++ show t ++ ": psi retraces it", psi 0 == 0 && and (zipWith (\p q -> psi q == p) path (drop 1 path)))
                , ("branch " ++ show t ++ ": the k-th element is in {2^k - 1, ..., 2^(k+1) - 2}", and [2 ^ k - 1 <= n && n <= 2 ^ (k + 1) - 2 | (k, n) <- zip [0 :: Integer ..] path])
                ]
          | t <- [1 .. 100 :: Int]
          ]

-- * Exercise 9-42 (ii)

treeEmbedChecks :: [(String, Bool)]
treeEmbedChecks =
  [ ("e(" ++ show a ++ ") <= e(" ++ show b ++ ") <=> a <= b", (e a `isPrefix` e b) == (a `isPrefix` b))
  | a <- seqs
  , b <- seqs
  ]
    ++ [("e one-one", length (nub (map e seqs)) == length seqs)]
  where
    seqs = concat [sequencesOf k | k <- [0 .. 3]]
    sequencesOf 0 = [[]]
    sequencesOf k = [x : xs | x <- [0 .. 2 :: Int], xs <- sequencesOf (k - 1)]
    e = concatMap (\n -> replicate n True ++ [False])
    isPrefix xs ys = take (length xs) ys == xs
