-- | Checks of § 13.3 (printed pp. 346-350): the procedure of
-- th:complete-measure-zero and the exercises on the Cantor space.
-- Scope ch13-14.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh13Measure.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh13Measure.hs [--verbose]
--
-- * th:complete-measure-zero (p. 350): the instructions for g enumerate
--   W_(rho(z)), give each quadruple <x, y, u, v> the conditional
--   probability P[D_u subset tau(f) & D_v subset tau(f)-bar | f* subset f]
--   and output the first y whose "накопленная вероятность" exceeds 1/2.
--   W_(rho(z)) is regular (th:regularization, § 9.2): two different
--   quadruples with the same x are not consistent ("не согласованы"), so
--   their events are disjoint and the running sum of the probabilities of
--   the quadruples of y is the probability of the union of their events.
--   Checked on model sets W built from oracle computation trees (the
--   stopping branches, as in § 9.2) and on regularizations of random lists
--   by the rule of rho: the sets are regular, the events of one x are
--   disjoint, sum = union (exact rationals, all 0/1 functions on [0, 8)
--   extending f*), and the procedure outputs y whenever
--   P[phi^f(x) = y | f* subset f] > 1/2.  On a list that is not regular
--   (sub-events of a wrong branch put first) the sum exceeds 1/2 for the
--   wrong y while the union stays at 1/4: the printed procedure relies on
--   the regularity of W_(rho(z)).  The conditional probability is also
--   compared with its product formula ("это вычисление элементарно").
-- * ex:cantor-space-metric (a), (d): delta is a metric, in fact
--   delta(f, h) <= max(delta(f, g), delta(g, h)), on all 0/1 functions
--   that vanish from 6 on; the ball {g | delta(f, g) < 1/(n + 1)} is
--   {g | f restricted to [0, n] subset g} (the spherical neighbourhoods
--   of p. 346).
-- * ex:category-versus-measure (a): for blocks [x_i, x_(i+1)) the set
--   {f | every block contains a point x with f(x) = 1} has measure
--   prod (1 - 2^-(x_(i+1) - x_i)) (counted exactly for blocks of total
--   length <= 12); with x_(i+1) - x_i = i + k the partial products stay
--   >= 1 - 2^(1-k) (k = 2: positive measure; large k: close to 1, part (b)).
--
-- Not established: measurability and the limits of the proof, the
-- nonrecursiveness of K, category statements; the checks are finite.
module Main (main) where

import Ch08Coding (below, mkGen, sortNub)
import Ch13Oracle
import Data.Ratio ((%))
import Data.Word (Word64)
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "th:complete-measure-zero: regular sets, sum = union" regularChecks
  group c "th:complete-measure-zero: the procedure outputs the likely y" procedureChecks
  group c "th:complete-measure-zero: without regularity the sum can be wrong" nonRegularChecks
  group c "ex:cantor-space-metric delta" metricChecks
  group c "ex:category-versus-measure (a), (b)" categoryChecks
  finish c "ch13-measure"

-- * Quadruples with sets of points of the graph

-- | <x, y, D_u, D_v>; a point (a, b) stands for the code tau(a, b) of a pair
-- of the graph tau(f).
type Quad = (Int, Integer, [(Int, Int)], [(Int, Int)])

compatible :: Quad -> Bool
compatible (_, _, du, dv) = all (`notElem` dv) du

consistent :: Quad -> Quad -> Bool
consistent (_, _, du1, dv1) (_, _, du2, dv2) = all (`notElem` dv2) du1 && all (`notElem` dv1) du2

-- | The rule of rho (§ 9.2): drop a quadruple that is not compatible or is
-- consistent with a kept quadruple with the same x.
rho :: [Quad] -> [Quad]
rho = go []
  where
    go kept [] = reverse kept
    go kept (q@(x, _, _, _) : qs)
      | not (compatible q) = go kept qs
      | any (\k@(x', _, _, _) -> x' == x && consistent k q) kept = go kept qs
      | otherwise = go (q : kept) qs

regular :: [Quad] -> Bool
regular qs =
  all compatible qs
    && and [not (consistent a b) | (i, a@(x, _, _, _)) <- zip [0 :: Int ..] qs, (j, b@(x', _, _, _)) <- zip [0 ..] qs, i < j, x == x']

-- | The 0/1 functions on [0, 8) that extend f*.
extensions :: Seg -> [Seg]
extensions fs = [fs ++ b | b <- allBits (8 - length fs)]
  where
    allBits 0 = [[]]
    allBits k = [v : r | r <- allBits (k - 1 :: Int), v <- [0, 1]]

holds :: Seg -> Quad -> Bool
holds f (_, _, du, dv) = all (\(a, b) -> at a == b) du && all (\(a, b) -> at a /= b) dv
  where
    at a = case drop a f of (v : _) -> v; [] -> -1

prob :: Seg -> (Seg -> Bool) -> Rational
prob fs p = let es = extensions fs in toInteger (length (filter p es)) % toInteger (length es)

-- | The product formula: every point (a, b) of D_u fixes f(a) = b, every
-- point of D_v excludes one value; 0 when the conditions clash.
probFormula :: Seg -> Quad -> Rational
probFormula fs (_, _, du, dv) = product (map pointProb (sortNub (map fst (du ++ dv))))
  where
    pointProb a =
      let must = sortNub [b | (a', b) <- du, a' == a]
          mustNot = sortNub [b | (a', b) <- dv, a' == a]
          allowed v = all (== v) must && v `notElem` mustNot
          vals = case drop a fs of
            (v : _) -> [v]
            [] -> [0, 1]
       in toInteger (length (filter allowed vals)) % toInteger (length vals)

-- | The stopping branches of a computation on input x: the question
-- "f(a) = ?" is the question "<a, 0> in tau(f)?" (yes: f(a) = 0).
branches :: Int -> Comp -> [Quad]
branches x = go [] []
  where
    go du dv (Out y) = [(x, y, reverse du, reverse dv)]
    go _ _ Loop = []
    go du dv (Ask a c0 c1)
      | (a, 0) `elem` du = go du dv c0
      | (a, 0) `elem` dv = go du dv c1
      | otherwise = go ((a, 0) : du) dv c0 ++ go du ((a, 0) : dv) c1

-- | The model W: branches of a family on the inputs 0..5, questions below 8.
modelW :: Word64 -> [Quad]
modelW seed = concat [branches x (fst (randComp 4 8 (mkGen (seed * 7777 + fromIntegral x)))) | x <- [0 .. 5]]

-- | Random lists of quadruples (not regular in general).
randomQuads :: Word64 -> [Quad]
randomQuads seed = fst (go (0 :: Int) (mkGen (seed * 99991)))
  where
    go i g
      | i >= 14 = ([], g)
      | otherwise =
          let (x, g1) = below 3 g
              (y, g2) = below 2 g1
              (du, g3) = pts 2 g2
              (dv, g4) = pts 2 g3
              (rest, g5) = go (i + 1) g4
           in ((x, toInteger y, du, dv) : rest, g5)
    pts 0 g = ([], g)
    pts k g =
      let (r, g1) = below 3 g
          (a, g2) = below 6 g1
          (b, g3) = below 2 g2
          (rest, g4) = pts (k - 1 :: Int) g3
       in (if r == 0 then rest else (a, b) : rest, g4)

prefixes :: [Seg]
prefixes = [[], [0], [1], [0, 1], [1, 1, 0]]

regularChecks :: [(String, Bool)]
regularChecks =
  [("model W from trees is regular, seed " ++ show s, regular (modelW s)) | s <- [1 .. 40]]
    ++ [("rho keeps a regular set, seed " ++ show s, rho (modelW s) == modelW s) | s <- [1 .. 40]]
    ++ [("rho gives a regular set, seed " ++ show s, regular (rho (randomQuads s))) | s <- [1 .. 200]]
    ++ [ ( "sum = union, seed " ++ show s ++ ", x = " ++ show x ++ ", y = " ++ show y
         , sum [prob fs (`holds` q) | q <- qs] == prob fs (\f -> any (holds f) qs) )
       | s <- [1 .. 60]
       , w <- [modelW s, rho (randomQuads s)]
       , fs <- prefixes
       , x <- [0 .. 5]
       , y <- [0, 1]
       , let qs = [q | q@(x', y', _, _) <- w, x' == x, y' == y]
       ]
    ++ [ ("product formula, seed " ++ show s, and [probFormula fs q == prob fs (`holds` q) | q <- w])
       | s <- [1 .. 60], w <- [modelW s, rho (randomQuads s)], fs <- prefixes
       ]

-- | The printed instructions: enumerate, accumulate per y, output the first
-- y whose running sum exceeds 1/2.
procedureOut :: Seg -> [Quad] -> Int -> Maybe Integer
procedureOut fs w x = go [] [q | q@(x', _, _, _) <- w, x' == x]
  where
    go _ [] = Nothing
    go acc (q@(_, y, _, _) : qs) =
      let s = maybe 0 id (lookup y acc) + prob fs (`holds` q)
          acc' = (y, s) : filter ((/= y) . fst) acc
       in if s > 1 % 2 then Just y else go acc' qs

procedureChecks :: [(String, Bool)]
procedureChecks =
  [ ( "seed " ++ show s ++ ", f* = " ++ show fs ++ ", x = " ++ show x
    , let pY y = prob fs (\f -> evalTotal comp (\p -> case drop p f of (v : _) -> v; [] -> 0) == Just y)
          likely = [y | y <- [0, 1], pY y > 1 % 2]
       in case likely of
            [y] -> procedureOut fs w x == Just y
            _ -> procedureOut fs w x == Nothing )
  | s <- [1 .. 80]
  , let w = modelW s
  , fs <- prefixes
  , x <- [0 .. 5]
  , let comp = fst (randComp 4 8 (mkGen (s * 7777 + fromIntegral x)))
  ]
    ++ [("the likely value occurs in the models", or [procedureOut fs (modelW s) x /= Nothing | s <- [1 .. 10], fs <- prefixes, x <- [0 .. 5]])]

nonRegularChecks :: [(String, Bool)]
nonRegularChecks =
  [ ("the list is not regular", not (regular wrongFirst))
  , ("P[phi^f(0) = 0] = 3/4 on the branches", prob [] (\f -> any (holds f) right) == 3 % 4)
  , ("the union for y = 1 is 1/4", prob [] (\f -> any (holds f) wrongs) == 1 % 4)
  , ("the sum for y = 1 is 5/8 > 1/2", sum [prob [] (`holds` q) | q <- wrongs] == 5 % 8)
  , ("the summing procedure outputs the wrong y = 1", procedureOut [] wrongFirst 0 == Just 1)
  , ("after rho the set is regular", regular (rho wrongFirst))
  , ("after rho the procedure no longer outputs 1", procedureOut [] (rho wrongFirst) 0 /= Just 1)
  , ("on the branches alone it outputs 0", procedureOut [] (wrongs1 ++ right) 0 == Just 0)
  ]
  where
    -- branches of "ask f(3); if 0 output 0; else ask f(4): 0 -> output 0,
    -- 1 -> output 1": events {f(3) = 0}, {f(3) = 1, f(4) = 0},
    -- {f(3) = 1, f(4) = 1}
    right = [(0, 0, [(3, 0)], []), (0, 0, [(4, 0)], [(3, 0)])]
    wrongs1 = [(0, 1, [], [(3, 0), (4, 0)])]
    -- sub-events of the wrong branch listed before it
    wrongs =
      wrongs1
        ++ [ (0, 1, [(5, 0)], [(3, 0), (4, 0)])
           , (0, 1, [], [(3, 0), (4, 0), (5, 0)])
           , (0, 1, [(6, 0)], [(3, 0), (4, 0)]) ]
    wrongFirst = wrongs ++ right

-- * ex:cantor-space-metric

-- | f, g as 0/1 lists of length 6 (0 from 6 on).
delta :: Seg -> Seg -> Rational
delta f g = case [x | (x, a, b) <- zip3 [0 :: Integer ..] f g, a /= b] of
  (x : _) -> 1 % (x + 1)
  [] -> 0

allSix :: [Seg]
allSix = sequence (replicate 6 [0, 1])

metricChecks :: [(String, Bool)]
metricChecks =
  [ ("delta(f, g) = 0 <=> f = g", and [(delta f g == 0) == (f == g) | f <- allSix, g <- allSix])
  , ("delta symmetric", and [delta f g == delta g f | f <- allSix, g <- allSix])
  ]
    ++ [ ("ultrametric inequality, f = " ++ show f, and [delta f h <= max (delta f g) (delta g h) | g <- allSix, h <- allSix])
       | f <- allSix
       ]
    ++ [ ( "ball of radius 1/" ++ show (n + 1) ++ " about " ++ show f ++ " = {g | f|[0," ++ show n ++ "] subset g}"
         , and [(delta f g < 1 % toInteger (n + 1)) == (take (n + 1) f == take (n + 1) g) | g <- allSix] )
       | f <- take 16 allSix, n <- [0 .. 5 :: Int]
       ]

-- * ex:category-versus-measure

blockMeasure :: [Int] -> Rational
blockMeasure sizes = product [1 - 1 % (2 ^ k) | k <- sizes]

countBlocks :: [Int] -> Rational
countBlocks sizes =
  let n = sum sizes
      fs = sequence (replicate n [0, 1 :: Int])
      ok f = all (elem 1) (cut sizes f)
      cut [] _ = []
      cut (k : ks) xs = take k xs : cut ks (drop k xs)
   in toInteger (length (filter ok fs)) % (2 ^ n)

categoryChecks :: [(String, Bool)]
categoryChecks =
  [ ("measure of the block set = product, blocks " ++ show bs, countBlocks bs == blockMeasure bs)
  | bs <- [[1], [2], [1, 2], [2, 3], [1, 1, 1], [3, 4, 5], [2, 2, 2, 2], [1, 2, 3, 4]]
  ]
    ++ [ ( "gaps i + " ++ show k ++ ": partial products >= 1 - 2^(1 - k), i < " ++ show m
         , blockMeasure [i + k | i <- [0 .. m - 1]] >= 1 - 1 % (2 ^ (k - 1)) )
       | k <- [2 .. 8], m <- [1 .. 40]
       ]
