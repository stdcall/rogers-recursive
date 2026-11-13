-- | Checks of chapter 16 (printed pp. 478-586): prefix rules and the
-- Tarski-Kuratowski computations of §§ 16.1-16.8, codes of tuples,
-- finite-path trees and their ordinals (§ 16.3), the second lemma of
-- § 16.8 on notations of finite ordinals.  Scope ch15-16.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh16Trees.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh16Trees.hs [--verbose]
--
-- What is checked, and where the expected values come from:
--
-- * cor:alternating-prefix (p. 481): every link of the printed chain
--   forall^0 exists^1 exists^0 forall^1 -> ... -> exists^1 forall^1
--   exists^0 is an application of the rule named there (theorem
--   th:kleene-prefix-rules (i)-(iv), dummy quantifier); the general
--   procedure (exercise 16-3), run on all 5334 prefixes of length <= 6
--   with a type-1 quantifier, is a chain of rule applications ending in
--   n alternating type-1 quantifiers and one type-0 quantifier of the
--   other kind, n = 1 + the number of changes of kind in the reduced
--   prefix, starting with its first kind; exm:prefix-sigma-one-one
--   (p. 485): th:addison-kleene-prefix-rules (i) takes exists^1 forall^1
--   (the printed chain) to exists^1 forall^0.
-- * Tarski-Kuratowski computations (module Ch15Prefix) against the
--   printed levels: exm:w-pi-one-one (Pi^1_1); th:t-pi11-complete (T in
--   Pi^1_1); th:jump-preserves-delta (Sigma^1_n and Pi^1_n forms of A',
--   n = 1..4); th:hyperarithmetical-reducibility-transitive (Sigma^(1,A)_1);
--   th:delta-n-transitive (n = 1..4); th:t2-sigma21-complete (Sigma^1_2);
--   th:t2-alpha-delta21 (a Pi^1_2 and a Sigma^1_2 form);
--   th:hyperarithmetical-quantifier (Pi^1_1); the relations C, M, P of
--   th:spector-hyperarithmetical-quantifier (Pi_1, Delta_3, Pi_3,
--   pp. 540-542); cor:singleton-sigma-one-one (f) (i), (iii);
--   th:delta11-pi02-singleton ({H(3 . 5^t)} in Pi_2, p. 570).
-- * Codes (§ 16.1, p. 482; § 16.3; § 16.7): fbar(x) = tau^*(<f(0), ...,
--   f(x - 1)>) with tau^* of p. 98, the footnote of p. 505
--   n * fbar(x) = (n * f)bar(x + 1), concatenation x * y with 0 * y = y,
--   and ex:extension-greater (16-77): a proper extension has a larger code
--   (all tuples with terms <= 3, length <= 3, extended by <= 2 terms).
-- * The examples A_1 - A_7 of § 16.3 (pp. 502-504) on a bounded part
--   (terms <= 6, length <= 4; A_5 with n <= 3): which are trees, the
--   subtree relations, branches, o(A_3) = 4, o(A_6) = 1, o(A_7) = 0,
--   o_(A_5)(<n>) = n + 1 (so o(A_5) = omega, proved in
--   checks/lean/RogersRecursive/Ch15_16Trees.lean), the sprouts of
--   A_1, A_2, A_3, A_6, A_7 as printed.
-- * Finite trees (all 677 trees of depth <= 3 over {0, 1}; the sprouts
--   n >= 2 are empty and are represented by n = 2): o(tau) is the least
--   ordinal above all o(sigma_n) (each sprout counted with +1); removing
--   a terminal vertex does not raise o (so o is monotone, p. 504);
--   lem:basic-tree-lemma in both printed forms on all pairs; the
--   formulas of the proofs of th:t-alpha-delta11 (p. 510) and of
--   th:delta11-below-h, case y = 2^s (p. 564); the tree of the end of the
--   proof of cor:boundedness-uniform has ordinal o(tau) + 1; the tree of
--   th:finite-path-tree-ordinals (b) for alpha = m < omega has ordinal m.
-- * Sum and product of trees (p. 505, ex:tree-sum-product) on random
--   finite trees: tau_1 + tau_2 (a copy of tau_1 hung by a new edge below
--   every terminal vertex of tau_2) and tau_1 . tau_2 (a copy of tau_1 at
--   every vertex of tau_2, the terminal vertices of the copy carrying the
--   copies of the vertices below) have ordinals o_1 + o_2 and o_1 . o_2;
--   the printed definition of the sum gives the empty tree when tau_2 is
--   empty, so o(tau_1 + empty) = 0 /= o(tau_1) for nonempty tau_1
--   (corrected by the added convention tau_1 + empty = tau_1).
-- * The Kleene-Brouwer ordering (p. 506): the two printed comparisons,
--   a strict linear order on all tuples with terms <= 2, length <= 3; on
--   a finite tree its order type (the number of vertices) is >= o(tau)
--   (ex:kleene-brouwer-ordering (b)); along a branch fbar(x + 1) precedes
--   fbar(x).
-- * The second lemma of § 16.8 (lem:spector-ordinals-below, p. 561) on
--   the notations of finite ordinals (1, 2, 4, 16, 65536): in the case
--   y = 2^s, s = 2^t, O_|y| = O_|s| u {2^v | v in O_|s|} holds for s =
--   2, 4, 16, 65536 and fails for y = 2 (s = 1 = 2^0: the right side is
--   empty, O_1 = {1}); with "u {1}" added (corrected) it holds for all.
--
-- Not established: the infinite trees and ordinals (only finite models
-- and bounded parts), recursiveness, the analytical levels beyond the
-- bookkeeping of the algorithm.
module Main (main) where

import Ch08Coding
import Ch15Prefix
import Data.List (isPrefixOf, sort, (\\))
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "16.1 Cor. III: the printed chain (p. 481)" chainChecks
  group c "16.1 Cor. III in general, ex. 16-3" generalChecks
  group c "16.1 example 3: Th. VII (i) (p. 485)" akChecks
  group c "16.1-16.8 TK computations" tkChecks
  group c "16.1, 16.3, 16.7 codes of tuples, ex. 16-77" codeChecks
  group c "16.3 examples A_1 - A_7 (pp. 502-504)" exampleChecks
  group c "16.3 finite trees: ordinals, monotone, sprouts (pp. 503-505)" ordinalChecks
  group c "16.3 basic tree lemma and its uses (pp. 505, 510, 564)" lemmaChecks
  group c "16.3 ex. 16-25: sum and product of trees (p. 505)" sumProductChecks
  group c "16.3 Kleene-Brouwer ordering (p. 506)" kbChecks
  group c "16.8 second lemma: finite notations, case y = 2^s (p. 561)" notationChecks
  finish c "ch16-trees"

-- * Prefixes

e0, a0, e1, a1 :: Q
e0 = Q E 0
a0 = Q A 0
e1 = Q E 1
a1 = Q A 1

chainChecks :: [(String, Bool)]
chainChecks =
  [ ("step " ++ show i ++ " by " ++ show r, isStep r p q)
  | (i, (p, r, q)) <- zip [1 :: Int ..] (zip3 printed rules (drop 1 printed)) ]
    ++ [ ("ends in exists^1 forall^1 exists^0", last' printed == [e1, a1, e0]) ]
  where
    printed =
      [ [a0, e1, e0, a1], [a0, e1, e1, a1], [a0, e1, a1], [e1, a0, a1]
      , [e1, a1, a1], [e1, a1], [e1, a1, e0] ]
    rules = [R3, R2, R4, R3, R2, Dummy]
    last' xs = case reverse xs of
      (x : _) -> x
      [] -> []

generalChecks :: [(String, Bool)]
generalChecks =
  ("5334 prefixes", length prefixes == 5334)
    : [ (show p, ok p) | p <- prefixes ]
  where
    qs = [e0, a0, e1, a1]
    prefixes = [ p | k <- [1 .. 6], p <- sequence (replicate k qs)
                   , not (null (reduced p)) ]
    ok p =
      let chain = take 200 (normalize p)
          final = case reverse chain of
            ((_, q) : _) -> q
            [] -> p
          ks = reduced p
          n = 1 + alternations ks
       in length chain < 200
            && validChain p chain
            && length final == n + 1
            && and [t == 1 | Q _ t <- take n final]
            && and [t == 0 | Q _ t <- drop n final]
            && alternations [k | Q k _ <- final] == n
            && take 1 [k | Q k _ <- final] == take 1 ks

akChecks :: [(String, Bool)]
akChecks =
  [ ("exists^1 forall^1 -> exists^1 forall^0", isStep AK1 [e1, a1] [e1, a0])
  , ("so the prefix of the example gives Sigma^1_1", reduced [e1, a0] == [E])
  ]

-- * Tarski-Kuratowski computations of chapter 16

sig1, pi1A, del1 :: Form
sig1 = KnownA 1 2
pi1A = KnownA 2 1
del1 = KnownA 1 1

tkChecks :: [(String, Bool)]
tkChecks =
  [ ("W: (forall^0 exists^0 & ... & forall^1 exists^0 exists^0) is Pi^1_1",
     level w == Cx inf inf 2 1)
  , ("T: forall exists & forall^1 exists^0 is Pi^1_1", level t == Cx inf inf 2 1)
  , ("XXXI: the form of C is Sigma^(1,A)_1", hS (level transitive) == 1)
  , ("XXXVII: T^2 = {z | (exists A)[z in T^A]} is Sigma^1_2", level (E1 pi1A) == Cx inf inf 2 3)
  , ("XXXVIII: the first form is Pi^1_2", hP (level t2First) == 2)
  , ("XXXVIII: the second form is Sigma^1_2", hS (level t2Second) == 2)
  , ("XLI: the form of A is Pi^1_1", hP (level kleene) == 1)
  , ("XLIV: C in Pi_1", level (A0 Rec) == Cx 2 1 0 0)
  , ("XLIV: M in Delta_3", level m == Cx 3 3 0 0)
  , ("XLIV: P in Pi_3", aP (level p) == 3)
  , ("cor. XLIV (f) (i): {A} in Sigma^1_1 and Pi^1_1",
     hS (level (singleton sig1 pi1A)) == 1 && hP (level (singleton pi1A sig1)) == 1)
  , ("cor. XLIV (f) (iii): Sigma^1_1 and Pi^1_1 forms for A",
     hS (level (E1 (And sig1 Rec))) == 1 && hP (level (A1 (Imp sig1 Rec))) == 1)
  , ("LII: {H(3 . 5^t)} in Pi_2", inPi 2 h35)
  ]
    ++ [ ("X: A' in Sigma^1_" ++ show n, hS (level (jump n True)) == n) | n <- [1 .. 4] ]
    ++ [ ("X: A' in Pi^1_" ++ show n, hP (level (jump n False)) == n) | n <- [1 .. 4] ]
    ++ [ ("XXXIV: A in Sigma^(1,C)_" ++ show n, hS (level (shoenS n)) == n) | n <- [1 .. 4] ]
    ++ [ ("XXXIV: A in Pi^(1,C)_" ++ show n, hP (level (shoenP n)) == n) | n <- [1 .. 4] ]
  where
    inW = Known 1 2
    w = And (A0 (E0 Rec)) (And (A0 Rec) (And (A0 (A0 (A0 Rec))) (And (A0 (A0 Rec))
          (A1 (E0 (E0 Rec))))))
    t = And (A0 (E0 Rec)) (A1 (E0 Rec))
    -- C = {x | (exists f)(forall w) not (exists y, u, v)[... & D_u in B + tau f
    --   & D_v in the complement]}, B by its Pi and Sigma forms
    transitive = E1 (A0 (Not (E0 (E0 (E0 (And Rec (And (A0 (Imp Rec pi1A))
                   (A0 (Imp Rec (Not sig1))))))))))
    t2First = A1 (Imp pi1A (E1 del1))
    t2Second = E1 (And pi1A (Not (E1 del1)))
    kleene = E0 (And (A0 (E0 pi1A)) (A0 (A0 (Imp (And Rec (A0 (A0 (Imp Rec sig1)))) Rec))))
    tree = Known 3 2
    zero = Known 3 2
    one = Known 3 2
    m = And tree (And tree (Or (And zero one)
          (And (Not zero) (And (E0 (A0 Rec)) (A0 (Or zero (E0 Rec)))))))
    p = And (A0 Rec) (And (A0 (A0 (Iff Rec (And (Known 3 3) (A0 (E0 Rec))))))
          (A0 (A0 (Imp Rec (A0 Rec)))))
    singleton first second = And (A0 (Imp Rec first)) (A0 (Imp second Rec))
    h35 = And (A0 (A0 (Imp Rec inW))) (A0 (Imp inW (A0 (E0 Rec))))
    sigN n = KnownA n (n + 1)
    piN' n = KnownA (n + 1) n
    -- A' = (exists y, u, v)[... in W & (forall x)[x in D_u => x in A]
    --   & (forall x)[x in D_v => x notin A]]
    jump n sigmaFirst =
      let (f1, f2) = if sigmaFirst then (sigN n, piN' n) else (piN' n, sigN n)
       in E0 (E0 (E0 (And (E0 Rec) (And (A0 (Imp Rec f1)) (A0 (Imp Rec (Not f2)))))))
    -- D = B by a Sigma^(1,C)_n form (first occurrence) and a Pi^(1,C)_n form
    eqB n = And (A0 (Imp Rec (sigN n))) (A0 (Imp (piN' n) Rec))
    shoenS n = E1 (And (eqB n) (sigN n))
    shoenP n = A1 (Imp (eqB n) (piN' n))

-- * Codes of tuples

tauStar :: [Integer] -> Integer
tauStar [] = 0
tauStar xs = tau (tauN xs) (toInteger (length xs) - 1) + 1

untauStar :: Integer -> [Integer]
untauStar 0 = []
untauStar z = let (a, b) = untau (z - 1) in piN (fromInteger b + 1) a

fbar :: (Integer -> Integer) -> Integer -> Integer
fbar f x = tauStar (map f [0 .. x - 1])

-- | n * y: the code of <n, y_1, ..., y_k>.
consCode :: Integer -> Integer -> Integer
consCode n y = tauStar (n : untauStar y)

-- | x * y: concatenation.
catCode :: Integer -> Integer -> Integer
catCode x y = tauStar (untauStar x ++ untauStar y)

codeChecks :: [(String, Bool)]
codeChecks =
  [ ("tau^* inverse on " ++ show s, untauStar (tauStar s) == s) | s <- tuples 3 4 ]
    ++ [ ("fbar(0) = 0", all (\f -> fbar f 0 == 0) fs) ]
    ++ [ ("footnote p. 505: n * fbar(" ++ show x ++ ")",
          consCode n (fbar f x) == fbar (cons n f) (x + 1))
       | f <- fs, n <- [0 .. 3], x <- [0 .. 4] ]
    ++ [ ("0 * y = y, y = " ++ show y, catCode 0 y == y) | y <- map tauStar (tuples 3 3) ]
    ++ [ ("x * y concatenates", catCode (tauStar s) (tauStar t) == tauStar (s ++ t))
       | s <- tuples 2 2, t <- tuples 2 2 ]
    ++ [ ("16-77: " ++ show (s, t), tauStar (s ++ t) > tauStar s)
       | s <- tuples 3 3, t <- tuples 3 2, not (null t) ]
  where
    fs = [\x -> x, \x -> 2 * x + 1, const 0, \x -> x * x `mod` 5]
    cons n f x = if x == 0 then n else f (x - 1)

-- | All tuples with terms <= e and length <= l.
tuples :: Integer -> Int -> [[Integer]]
tuples e l = concat [sequence (replicate k [0 .. e]) | k <- [0 .. l]]

-- * Trees as finite sets of tuples

type Tree = [[Int]]

isTree :: Tree -> Bool
isTree t = and [init s `elem` t | s <- t, not (null s)]

children :: Tree -> [Int] -> [[Int]]
children t a = [s | s <- t, length s == length a + 1, a `isPrefixOf` s]

-- | o_tau(a) for a finite tree: 1 at a terminal vertex, else the least
-- ordinal above all o_tau(b) with b below a.
ordAt :: Tree -> [Int] -> Integer
ordAt t a = case children t a of
  [] -> 1
  cs -> maximum (map (ordAt t) cs) + 1

ordT :: Tree -> Integer
ordT t = if [] `elem` t then ordAt t [] else 0

sprout :: Int -> Tree -> Tree
sprout n t = [y | (m : y) <- t, m == n]

leaves :: Tree -> [[Int]]
leaves t = [s | s <- t, null (children t s)]

exampleChecks :: [(String, Bool)]
exampleChecks =
  [ ("A_1, A_2, A_3, A_5, A_6, A_7 are trees", all isTree [a1T, a2T, a3T, a5T, a6T, a7T])
  , ("A_4 is not a tree", not (isTree a4T))
  , ("subtrees of A_1", all (`sub` a1T) [a2T, a3T, a5T, a6T, a7T])
  , ("subtrees of A_2", all (`sub` a2T) [a3T, a6T, a7T])
  , ("subtrees of A_5, A_6", all (`sub` a5T) [a6T, a7T] && sub a7T a6T)
  , ("A_3 has the one branch <0, 0, 0>", leaves a3T == [[0, 0, 0]])
  , ("A_5: the branches are <n, ..., 2n>, all finite",
     sort (leaves a5T) == sort [[n .. 2 * n] | n <- [0 .. 3]])
  , ("A_6 has one branch, the root", leaves a6T == [[]])
  , ("o(A_3) = 4", ordT a3T == 4)
  , ("o(A_6) = 1", ordT a6T == 1)
  , ("o(A_7) = 0", ordT a7T == 0)
  , ("o_(A_5)(<n>) = n + 1", and [ordAt a5T [n] == toInteger n + 1 | n <- [0 .. 3]])
  , ("o(A_5 bounded by n <= 3) = 5", ordT a5T == 5)
  , ("sprouts of A_1 are A_1", all (\n -> sort (sprout n a1T) == sort (shorter a1T)) [0 .. 6])
  , ("sprouts of A_2: the 0th is A_2, the others empty",
     sort (sprout 0 a2T) == sort (shorter a2T) && all (null . (`sprout` a2T)) [1 .. 6])
  , ("sprouts of A_3: the 0th is {(), <0>, <0, 0>}, the others empty",
     sort (sprout 0 a3T) == sort [[], [0], [0, 0]] && all (null . (`sprout` a3T)) [1 .. 6])
  , ("sprouts of A_6, A_7 empty", all (\n -> null (sprout n a6T) && null (sprout n a7T)) [0 .. 6])
  ]
  where
    a1T = [s | k <- [0 .. 4], s <- sequence (replicate k [0 .. 6])]
    a2T = [replicate k 0 | k <- [0 .. 4]]
    a3T = [[], [0], [0, 0], [0, 0, 0]]
    a4T = [[], [0, 0], [0, 0, 0]]
    a5T = [] : [[n .. m] | n <- [0 .. 3], m <- [n .. 2 * n]]
    a6T = [[]] :: Tree
    a7T = [] :: Tree
    sub x y = all (`elem` y) x
    shorter t = [s | s <- t, length s < 4]

-- | All trees inside {0, 1}^(<= 3).
binaryTrees :: [Tree]
binaryTrees = [] : map (map reverse) (go (3 :: Int) [])
  where
    go 0 p = [[p]]
    go k p = [ p : (l ++ r) | l <- [] : go (k - 1) (0 : p), r <- [] : go (k - 1) (1 : p) ]

-- | A tree with its ordinal and the ordinals of the sprouts 0, 1, 2.
data Info = Info {tr :: Tree, ord :: Integer, sp :: [Integer]}

infos :: [Info]
infos = [Info t (ordT t) [ordT (sprout n t) | n <- [0, 1, 2]] | t <- binaryTrees]

ordinalChecks :: [(String, Bool)]
ordinalChecks =
  ("677 trees", length binaryTrees == 677)
    : [ ("o = sup (o(sprout) + 1) for " ++ show (tr i),
          null (tr i) || ord i == maximum (map (+ 1) (sp i)))
      | i <- infos ]
    ++ [ ("removing a terminal vertex does not raise o: " ++ show t,
          and [ordT (t \\ [l]) <= ordT t | l <- leaves t])
       | t <- binaryTrees ]
    ++ [ ("the tree of h(y) (cor. XXII (b)): o = o(tau) + 1 for " ++ show t,
          ordT (succTree t) == ordT t + 1)
       | t <- binaryTrees ]
    ++ [ ("Th. XVIII (b): alpha = " ++ show m, ordT (finiteOrdTree m) == toInteger m)
       | m <- [0 .. 5] ]
  where
    succTree t = [] : [n : y | n <- [0, 1, 2], y <- t]
    finiteOrdTree m = [s | k <- [0 .. m - 1], s <- sequence (replicate k [0, 1, 2 :: Int])]

lemmaChecks :: [(String, Bool)]
lemmaChecks =
  [ ("pairs of trees", and [ok i j | i <- infos, j <- infos]) ]
    ++ [ ("form " ++ show k, and [form k i j | i <- infos, j <- infos]) | k <- [1, 2 :: Int] ]
    ++ [ ("LI, y = 2^s: o(x) <= o(s) by the sprouts",
          and [ (ord x <= ord s) == (null (tr x) || ([] `elem` tr x && all (< ord s) (sp x)))
              | x <- infos, s <- infos ]) ]
  where
    lhs i j = ord i < ord j
    first i j = (ord i == 0 && ord j == 1) || any (\b -> all (< b) (sp i)) (sp j)
    second i j = ord j /= 0 && (ord i == 0 || any (\b -> all (< b) (sp i)) (sp j))
    ok i j = lhs i j == first i j && first i j == second i j
    -- the formula of the proof of XXI: phi_y(0) = 1 & [x empty or
    -- [phi_x(0) = 1 & (exists m)(forall n) ...]]
    form :: Int -> Info -> Info -> Bool
    form 1 i j = lhs i j == ([] `elem` tr j && (null (tr i)
                   || ([] `elem` tr i && any (\b -> all (< b) (sp i)) (sp j))))
    form _ i j = lhs i j == second i j

-- * Sum and product (finite rose trees)

data Rose = Node [Rose] deriving (Eq, Show)

oR :: Maybe Rose -> Integer
oR Nothing = 0
oR (Just r) = go r
  where
    go (Node []) = 1
    go (Node cs) = maximum (map go cs) + 1

plusPrinted :: Maybe Rose -> Maybe Rose -> Maybe Rose
plusPrinted _ Nothing = Nothing
plusPrinted Nothing t2 = t2
plusPrinted (Just r1) (Just r2) = Just (attach r2)
  where
    attach (Node []) = Node [r1]
    attach (Node cs) = Node (map attach cs)

plus :: Maybe Rose -> Maybe Rose -> Maybe Rose
plus t1 Nothing = t1
plus t1 t2 = plusPrinted t1 t2

times :: Maybe Rose -> Maybe Rose -> Maybe Rose
times (Just r1) (Just r2) = Just (go r2)
  where
    go (Node cs) = graft r1 (map go cs)
    graft (Node []) ks = Node ks
    graft (Node ds) ks = Node (map (`graft` ks) ds)
times _ _ = Nothing

randomRose :: Int -> Gen -> (Maybe Rose, Gen)
randomRose depth g0 =
  let (e, g1) = below 6 g0
   in if e == 0 then (Nothing, g1) else let (r, g2) = node depth g1 in (Just r, g2)
  where
    node 0 g = (Node [], g)
    node d g =
      let (k, g1) = below 3 g
       in let (cs, g2) = draws k (node (d - 1)) g1 in (Node cs, g2)

sumProductChecks :: [(String, Bool)]
sumProductChecks =
  [ ("o(t1 + t2) = o(t1) + o(t2) " ++ show (t1, t2), oR (plus t1 t2) == oR t1 + oR t2)
  | (t1, t2) <- pairs ]
    ++ [ ("o(t1 . t2) = o(t1) . o(t2) " ++ show (t1, t2), oR (times t1 t2) == oR t1 * oR t2)
       | (t1, t2) <- pairs ]
    ++ [ ("printed sum with empty t2 refuted",
          any (\(t1, _) -> oR (plusPrinted t1 Nothing) /= oR t1) pairs) ]
  where
    pairs = fst (draws 2000 pairG (mkGen 505))
    pairG g = let (a, g1) = randomRose 4 g; (b, g2) = randomRose 4 g1 in ((a, b), g2)

-- * Kleene-Brouwer

kbLess :: [Int] -> [Int] -> Bool
kbLess a b
  | b `isPrefixOf` a = a /= b
  | a `isPrefixOf` b = False
  | otherwise = case [(x, y) | (x, y) <- zip a b, x /= y] of
      ((x, y) : _) -> x < y
      [] -> False

kbChecks :: [(String, Bool)]
kbChecks =
  [ ("<0, 4, 7, 9> before <0, 4>", kbLess [0, 4, 7, 9] [0, 4])
  , ("<0, 3> before <0, 4, 7, 9>", kbLess [0, 3] [0, 4, 7, 9])
  , ("irreflexive", not (any (\a -> kbLess a a) ts))
  , ("total", and [a == b || kbLess a b || kbLess b a | a <- ts, b <- ts])
  , ("asymmetric", not (or [kbLess a b && kbLess b a | a <- ts, b <- ts]))
  , ("transitive", and [not (kbLess a b && kbLess b c) || kbLess a c | a <- ts, b <- ts, c <- ts])
  ]
    ++ [ ("order type >= o(tau) for " ++ show t, toInteger (length t) >= ordT t)
       | t <- binaryTrees ]
    ++ [ ("along a branch, fbar(x + 1) precedes fbar(x)",
          and [kbLess (map f [0 .. x]) (map f [0 .. x - 1]) | f <- fs, x <- [0 .. 10]]) ]
  where
    ts = [s | k <- [0 .. 3], s <- sequence (replicate k [0, 1, 2 :: Int])]
    fs = [id, const 0, \x -> x `mod` 3, \x -> 7 - x `mod` 7]

-- * Notations of finite ordinals and the second lemma

-- | The notation of the finite ordinal j: 1, 2, 4, 16, 65536, ...
note :: Int -> Integer
note 0 = 1
note j = 2 ^ note (j - 1)

notationChecks :: [(String, Bool)]
notationChecks =
  [ ("printed formula, s = " ++ show (note m), printedHolds m == (m >= 1)) | m <- [0 .. 3] ]
    ++ [ ("corrected formula, s = " ++ show (note m), corrected m) | m <- [0 .. 3] ]
  where
    -- O_k = {notations of 0, ..., k - 1}
    oSet k = [note j | j <- [0 .. k - 1]]
    rhs m = sortNub (oSet m ++ [2 ^ v | v <- oSet m])
    printedHolds m = rhs m == sort (oSet (m + 1))
    corrected m = sortNub (1 : rhs m) == sort (oSet (m + 1))
