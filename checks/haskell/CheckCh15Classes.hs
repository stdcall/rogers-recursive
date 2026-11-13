-- | Checks of chapter 15, §§ 15.1-15.2 (printed pp. 429-458): the
-- arithmetical hierarchy of classes of sets and of classes of functions,
-- the topology of the Cantor and Baire spaces, and exercises 15-11 -
-- 15-15.  Scope ch15-16.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh15Classes.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh15Classes.hs
--      [--verbose]
--
-- What is checked, and where the expected values come from:
--
-- * The Tarski-Kuratowski computations of the text (module Ch15Prefix),
--   each against the level the book prints: § 15.1 examples 1-3
--   (exm:nonempty-sets Sigma_1, exm:finite-sets Sigma_2,
--   exm:recursive-sets Sigma_3, pp. 433-434); the lemma of
--   th:class-hierarchy (p. 439: Sigma_n for n >= 2, Pi_n for n >= 3, and
--   not by the same form below these bounds); th:true-arithmetic-implicit
--   (pp. 441-442: the step to f(n + 1) and {0^(omega)} are Pi_2 forms);
--   th:re-sets-class (p. 442, Sigma_3); § 15.2 examples exm:infinite-range
--   (Pi_2) and exm:general-recursive-functions (Sigma_3, p. 448); the
--   forms of th:function-classes-graphs (pp. 454-455: Sigma_n for n >= 3,
--   Pi_n for n >= 2) and of th:set-classes-characteristic-functions
--   (p. 455: Sigma_n for n >= 2, Pi_n for n >= 1).  These check the
--   bookkeeping of the algorithm, not that the classes are not lower.
-- * th:sigma-zero-clopen (pp. 435-436), (3) => (2): for every tt-condition
--   of order <= 3 on {0, 1, 2} the classes D_i and E_i of the proof
--   partition the sets X subset {0, ..., 4} as printed; (2) => (1) in the
--   form of cor:sigma-zero-finite-unions: a finite union of basic
--   neighborhoods is the class of a tt-condition (random unions).
-- * th:clopen-finite-path-trees (pp. 450-451) on the finitely branching
--   model (alphabet {0, 1}, all 677 trees of depth <= 3; a branch of a
--   finite tree is a terminal vertex): the tree T' of the proof is a tree,
--   no branch of T' begins a branch of T or conversely, every sequence of
--   length 4 begins with a branch of exactly one of T, T'; the footnote
--   cases T = {empty}, T = empty; the converse: for each of the 256 classes
--   of sequences of length 3 the shortest deciding segments form a
--   finite-path tree whose A-branches give the class.
-- * ex:finite-path-tree-subbranches (15-15, p. 473): disproved: the comb
--   {0^n 1} is a family of pairwise incomparable finite subbranches whose
--   union contains 0^n for every n (an infinite branch); the other
--   direction holds on the model trees.
-- * ex:baire-metric-complete, ex:basic-neighborhoods-base (15-11, 15-14):
--   d of p. 449 on all sequences of length 4 over {0, 1, 2} (equal
--   sequences are at distance 0): a metric, even an ultrametric; the ball
--   of radius 1/n about f is the basic neighborhood of the first n values.
-- * ex:continued-fractions (15-13, p. 473): the algorithm of the exercise
--   on all rationals a/b, 0 < a < b <= 60: it stops, every n_i >= 1, the
--   last one >= 2, the value is a/b; alpha_0, alpha_1, alpha_2 as printed
--   are the values of the first one, two, three terms, alpha_2 with n_2
--   at the bottom (corrected) and not with n_1 (printed, refuted on
--   n_0 = 1, n_1 = 2, n_2 = 3); the approximations alternate around alpha
--   and approach it; (d): for every prefix of length <= 3 with terms
--   1..4, a rational in (0, 1) with denominator <= 60 lies strictly
--   between the values of the prefix and of the prefix with the last
--   term plus 1 iff its continued fraction begins with the prefix and is
--   longer (the basic neighborhood is an open interval).
--
-- Not established: anything about recursiveness or about classes beyond
-- the finite models; irrational points of exercise 15-13 (d); that the
-- levels computed by the algorithm are exact.
module Main (main) where

import Ch08Coding
import Ch15Prefix
import Data.List (isPrefixOf, nub, sort)
import Data.Ratio ((%))
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "15.1 TK: examples 1-3, Th. XIII (pp. 433-434, 442)" tkSets
  group c "15.1 TK: lemma of Th. XI, n >= 2 and n >= 3 (p. 439)" tkLemma
  group c "15.1 TK: Th. XII, the Pi_2 forms (pp. 441-442)" tkImplicit
  group c "15.2 TK: examples 1, 2 (p. 448)" tkFunctions
  group c "15.2 TK: Th. XXV, XXVI (pp. 454-455)" tkGraphs
  group c "15.1 Th. VII, Cor. VII: tt-conditions (pp. 435-436)" ttChecks
  group c "15.2 Th. XX: finite-path trees, the tree T' (pp. 450-451)" treeChecks
  group c "15.4 ex. 15-15: the comb (p. 473)" combChecks
  group c "15.4 ex. 15-11, 15-14: the Baire metric (p. 449)" metricChecks
  group c "15.4 ex. 15-13: continued fractions (p. 473)" cfChecks
  finish c "ch15-classes"

-- * Tarski-Kuratowski computations

-- | x in W_y: an existential form.
inW :: Form
inW = Known 1 2

tkSets :: [(String, Bool)]
tkSets =
  [ ("nonempty: (exists x)[x in A] is Sigma_1", level nonempty == Cx 1 2 0 0)
  , ("finite: exists forall, Sigma_2", aS (level finite) == 2)
  , ("recursive: exists exists [forall [<=> exists] & forall [<=> exists]], Sigma_3",
     aS (level recursiveSets) == 3)
  , ("r.e.: exists forall [<=> exists], Sigma_3", aS (level reSets) == 3)
  ]
  where
    nonempty = E0 Rec
    finite = E0 (A0 (Imp Rec Rec))
    recursiveSets = E0 (E0 (And (A0 (Iff Rec inW)) (A0 (Iff (Not Rec) inW))))
    reSets = E0 (A0 (Iff Rec inW))

-- | The lemma of theorem XI: A_B = {{x} | x in B}.
tkLemma :: [(String, Bool)]
tkLemma =
  [ ("(i) n = " ++ show n, inSigma n (formI n) == (n >= 2)) | n <- [1 .. 7] ]
    ++ [ ("(ii) n = " ++ show n, inPi n (formII n) == (n >= 3)) | n <- [1 .. 7] ]
  where
    sigma n = Known n (n + 1)
    pin n = Known (n + 1) n
    single = A0 (Iff Rec Rec)   -- (forall y)[y in X <=> y = x]
    formI n = E0 (And single (sigma n))
    formII n = And (E0 single) (A0 (Imp Rec (pin n)))

tkImplicit :: [(String, Bool)]
tkImplicit =
  [ ("the condition for A = 0^(n+1) is Pi_2",
     inPi 2 (And (A0 (E0 Rec)) (A0 (Iff Rec (E0 (E0 (E0 (And inW Rec))))))))
  , ("X = 0^(omega) <=> (forall v)(forall y)(exists z) T: Pi_2",
     inPi 2 (A0 (A0 (E0 Rec))))
  ]

tkFunctions :: [(String, Bool)]
tkFunctions =
  [ ("infinite range: forall exists exists <=> forall exists",
     level (A0 (E0 (And Rec (E0 Rec)))) == Cx 3 2 0 0)
  , ("general recursive: exists forall exists, Sigma_3",
     aS (level (E0 (A0 (E0 (E0 Rec))))) == 3)
  ]

tkGraphs :: [(String, Bool)]
tkGraphs =
  [ ("XXV Sigma, n = " ++ show n, inSigma n (graphForm (Known n (n + 1))) == (n >= 3))
  | n <- [1 .. 7] ]
    ++ [ ("XXV Pi, n = " ++ show n, inPi n (graphForm (Known (n + 1) n)) == (n >= 2))
       | n <- [1 .. 7] ]
    ++ [ ("XXVI Sigma, n = " ++ show n, inSigma n (charForm (Known n (n + 1))) == (n >= 2))
       | n <- [1 .. 7] ]
    ++ [ ("XXVI Pi, n = " ++ show n, inPi n (charForm (Known (n + 1) n)) == (n >= 1))
       | n <- [1 .. 7] ]
  where
    -- X single-valued & total & the Sigma_n (Pi_n) form
    graphForm g = And (A0 (A0 (A0 (Imp Rec Rec)))) (And (A0 (E0 Rec)) g)
    -- (forall x)[f(x) <= 1] & the form for the set of f
    charForm g = And (A0 Rec) g

-- * tt-conditions and clopen classes of sets

universe :: [[Integer]]
universe = subsetsOf [0 .. 4]

ttChecks :: [(String, Bool)]
ttChecks =
  [ ("D_i, E_i partition, " ++ show (bs, a), partition bs a)
  | m <- [1 .. 3], let bs = [0 .. toInteger m - 1], a <- allBF m ]
    ++ [ ("finite union of neighborhoods is a tt-class " ++ show ns, unionIsTT ns)
       | ns <- fst (draws 300 randomNbhds (mkGen 15)) ]
  where
    holds bs a x = apply a [b `elem` x | b <- bs]
    partition bs a =
      let ds = [d | d <- subsetsOf bs, holds bs a d]
          es = [d | d <- subsetsOf bs, not (holds bs a d)]
          inNb x d = sort (filter (`elem` bs) x) == sort d
       in and [ holds bs a x == any (inNb x) ds
                  && not (holds bs a x) == any (inNb x) es
                  && length (filter (inNb x) (ds ++ es)) == 1
              | x <- universe ]
    -- a basic neighborhood: (D_u, D_v), D_u subset X, D_v subset complement
    randomNbhds g0 =
      let (k, g1) = below 4 g0
       in draws (k + 1) nbhd g1
    nbhd g0 =
      let (u, g1) = subsetOf 30 [0 .. 4] g0
          (v, g2) = subsetOf 30 [0 .. 4] g1
       in ((u, filter (`notElem` u) v), g2)
    inN x (u, v) = all (`elem` x) u && all (`notElem` x) v
    unionIsTT ns =
      let bs = nub (concat [u ++ v | (u, v) <- ns])
          m = length bs
          a = fromFn m (\ws -> any (inN [b | (b, True) <- zip bs ws]) ns)
       in and [any (inN x) ns == apply a [b `elem` x | b <- bs] | x <- universe]

-- * Finite-path trees (alphabet {0, 1}, depth <= 3)

type Seq = [Int]

alphabet :: [Int]
alphabet = [0, 1]


isTree :: [Seq] -> Bool
isTree t = and [init s `elem` t | s <- t, not (null s)]

-- | All trees inside {0, 1}^(<= d).
treesUpTo :: Int -> [[Seq]]
treesUpTo d = [] : map (map reverse) (go d [])
  where
    -- trees containing the root, vertices kept reversed under the prefix p
    go 0 p = [[p]]
    go k p = [ p : (l ++ r) | l <- [] : go (k - 1) (0 : p), r <- [] : go (k - 1) (1 : p) ]

leaves :: [Seq] -> [Seq]
leaves t = [s | s <- t, not (any (\a -> (s ++ [a]) `elem` t) alphabet)]

-- | The tree T' of the proof: subbranches f not in T whose f^- is in T
-- and is not a branch of T (and f = empty if T is empty).
complementTree :: [Seq] -> [Seq]
complementTree t = closeTree [f | f <- candidates, f `notElem` t, ok f]
  where
    candidates = [] : [s ++ [a] | s <- t, a <- alphabet]
    ok [] = True
    ok f = let g = init f in g `elem` t && g `notElem` leaves t

closeTree :: [Seq] -> [Seq]
closeTree fs = nub [take k f | f <- fs, k <- [0 .. length f]]

treeChecks :: [(String, Bool)]
treeChecks =
  ("677 trees of depth <= 3", length trees == 677)
    : [ ("T' for T = " ++ show t, prop t) | t <- trees ]
    ++ [ ("footnote: T = {empty} gives T' = empty", null (complementTree [[]]))
       , ("footnote: T = empty gives T' = {empty}", complementTree [] == [[]])
       ]
    ++ [ ("converse for the class " ++ show cls, converse cls)
       | cls <- subsetsOf (sequence (replicate 3 alphabet)) ]
  where
    trees = treesUpTo 3
    long = sequence (replicate 4 alphabet)
    begins b s = b `isPrefixOf` s
    prop t =
      let t' = complementTree t
          bt = leaves t
          bt' = if null t' then [] else leaves t'
       in isTree t'
            && and [not (begins a b) && not (begins b a) | a <- bt', b <- bt]
            && and [length (filter (`begins` s) (bt ++ bt')) == 1 | s <- long]
    -- the class is the set of sequences of length 3 in it
    converse cls =
      let decides s = all (`elem` cls) (ext s) || all (`notElem` cls) (ext s)
          ext s = [s ++ r | r <- sequence (replicate (3 - length s) alphabet)]
          shortest f = head' [take k f | k <- [0 .. 3], decides (take k f)]
          segs = nub [shortest f | f <- sequence (replicate 3 alphabet)]
          tr = closeTree segs
          inA = [s | s <- segs, all (`elem` cls) (ext s)]
       in isTree tr && sort (leaves tr) == sort segs
            && sort (nub [f | s <- inA, f <- ext s]) == sort cls
    head' (x : _) = x
    head' [] = []

-- * The comb (exercise 15-15)

combChecks :: [(String, Bool)]
combChecks =
  [ ("comb branches 0^n 1 pairwise incomparable",
     and [ not (a `isPrefixOf` b) | a <- comb, b <- comb, a /= b ])
  , ("their union contains 0^n for n <= 12", all (`elem` union) [replicate n 0 | n <- [0 .. 12]])
  , ("the union is a tree", isTree union)
  ]
    ++ [ ("finite-path tree = union of its pairwise incomparable branches " ++ show t,
          closeTree (leaves t) == t' && pairwise (leaves t))
       | t <- treesUpTo 3, not (null t), let t' = closeTree t ]
  where
    comb = [replicate n 0 ++ [1] | n <- [0 .. 12]]
    union = closeTree comb
    pairwise bs = and [not (a `isPrefixOf` b) | a <- bs, b <- bs, a /= b]

-- * The Baire metric

metricChecks :: [(String, Bool)]
metricChecks =
  [ ("d(f, g) = 0 <=> f = g", and [(dist f g == 0) == (f == g) | f <- seqs, g <- seqs])
  , ("symmetric", and [dist f g == dist g f | f <- seqs, g <- seqs])
  , ("ultrametric (hence triangle)",
     and [dist f h <= max (dist f g) (dist g h) | f <- seqs, g <- seqs, h <- seqs])
  ]
    ++ [ ("ball 1/" ++ show n ++ " about " ++ show f ++ " is the neighborhood",
          [g | g <- seqs, dist f g < 1 % toInteger n] == [g | g <- seqs, take n g == take n f])
       | f <- seqs, n <- [1 .. 4] ]
  where
    seqs = sequence (replicate 4 [0, 1, 2 :: Int])
    dist f g = case [x | (x, a, b) <- zip3 [0 :: Integer ..] f g, a /= b] of
      (x : _) -> 1 % (x + 1)
      [] -> 0

-- * Continued fractions

cf :: Rational -> [Integer]
cf r
  | r == 0 = []
  | otherwise = let n = floor (1 / r) in n : cf (1 / r - fromInteger n)

value :: [Integer] -> Rational
value [] = 0
value (n : ns) = 1 / (fromInteger n + value ns)

cfChecks :: [(String, Bool)]
cfChecks =
  [ ("cf of " ++ show (a, b), rationalCase (a % b))
  | b <- [2 .. 60], a <- [1 .. b - 1], gcd a b == 1 ]
    ++ [ ("alpha_0, alpha_1, alpha_2 " ++ show ns, printedForms ns)
       | ns <- sequence (replicate 3 [1 .. 6]) ]
    ++ [ ("printed alpha_2 refuted on 1, 2, 3",
          printedAlpha2 [1, 2, 3] /= value [1, 2, 3])
       ]
    ++ [ ("alternating approximations " ++ show (a, b), alternating (a % b))
       | b <- [2 .. 60], a <- [1 .. b - 1], gcd a b == 1 ]
    ++ [ ("(d) prefix " ++ show p, interval p)
       | k <- [1 .. 3], p <- sequence (replicate k [1 .. 4]) ]
  where
    rationalCase r =
      let ns = cf r
       in not (null ns) && all (>= 1) ns && lastIs2 ns && value ns == r
    lastIs2 ns = case reverse ns of
      (l : _) -> l >= 2
      [] -> False
    printedForms ns@[n0, n1, n2] =
      value (take 1 ns) == 1 / fromInteger n0
        && value (take 2 ns) == 1 / (fromInteger n0 + 1 / fromInteger n1)
        && value ns == 1 / (fromInteger n0 + 1 / (fromInteger n1 + 1 / fromInteger n2))
    printedForms _ = False
    printedAlpha2 [n0, n1, _] = 1 / (fromInteger n0 + 1 / (fromInteger n1 + 1 / fromInteger n1))
    printedAlpha2 _ = 0 :: Rational
    -- alpha_0 >= alpha, alpha_1 <= alpha, ..., distances decrease
    alternating r =
      let ns = cf r
          as = [value (take (k + 1) ns) | k <- [0 .. length ns - 1]]
          side k a = if even k then a >= r else a <= r
          ds = map (\a -> abs (a - r)) as
       in and (zipWith side [0 :: Int ..] as) && and (zipWith (>=) ds (drop 1 ds))
    interval p =
      let e1 = value p
          e2 = value (init p ++ [last p + 1])
          lo = min e1 e2
          hi = max e1 e2
       in and [ (lo < r && r < hi) == (p `isPrefixOf` ns && length ns > length p)
              | b <- [2 .. 60], a <- [1 .. b - 1], gcd a b == 1
              , let r = a % b, let ns = cf r ]
