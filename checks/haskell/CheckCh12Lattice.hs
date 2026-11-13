-- | Checks of chapter 12 (printed pp. 286-325): quotient lattices of
-- finite lattices (theorem I, exercises 12-1 ... 12-10), the
-- constructions of theorems II, XI, XIV on toy enumerations, and the
-- implication diagrams of § 12.6.  Scope ch10-12.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh12Lattice.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh12Lattice.hs
--      [--verbose]
--
-- What is checked, and where the expectations come from:
--
-- * th:quotient-lattices (theorem I, pp. 288-290) on the distributive
--   lattices 2^{0,1,2}, 2^{0,1,2,3}, the divisors of 30 and of 60, the
--   chains of 3 and 4 elements, 2 x 3, with every ideal and every dual
--   ideal: (a), (b) the relation is an equivalence and a congruence, the
--   (dual) ideal is a class and the zero (unit); exercise 12-6
--   (ex:quotient-order); (c) on the Boolean algebras 2^{0,1,2},
--   2^{0,1,2,3}, divisors of 30: the complement is well defined on the
--   classes, for every subset I (all 256 of 2^{0,1,2}) I is an ideal <=>
--   D = {a | a-bar in I} is a dual ideal, and for ideals the two
--   relations coincide; the step a-bar u c_1 = (a cap c_1-bar)-bar of the
--   corrected chain of p. 290; (d) the classes meeting a sublattice M
--   (every sublattice of 2^{0,1,2}) form a sublattice of L/I.
-- * Exercises: 12-2 (the hint's family is a lattice under subset, not a
--   sublattice of 2^{1,2,3}); 12-3 (complements are unique in the
--   distributive lattices, not in the diamond M_3); 12-4 (both
--   distributive laws hold in the distributive lattices above and both
--   fail in M_3 and N_5); 12-5 (the identities, in the three Boolean
--   algebras); 12-9 (the kernel of a homomorphism onto a lattice with 0 is
--   an ideal; for the Boolean 2^{0,1,2} onto 2^{0} the quotient has the
--   size of the image; the hint of (iii): the chain of 3 onto the chain of
--   2 with kernel {0}); 12-10 ((a) maximal dual ideals are prime in the
--   distributive lattices; (b) prime dual ideals, and prime ideals, are
--   maximal in the Boolean algebras; the chain of 3 has a prime dual
--   ideal that is not maximal).
-- * th:friedberg-splitting (theorem IV, pp. 294-295) on toy enumerations
--   (800 runs): B_1, B_2 split A, and x_n takes each value at most twice.
-- * th:maximal-set-exists (theorem XI, pp. 301-303): the properties (i),
--   (ii) of z-states (all bit strings of length <= 7); the construction on
--   toy enumerations W_0, ..., W_4 (recursive sets enumerated with
--   delays), 400 stages: markers move only to larger numbers; the numbers
--   losing a marker are exactly those put into A; a moved marker [m]
--   reaches a larger m-state; [0], ..., [3] do not move in the last 200
--   stages.
-- * th:no-maximal-superset (Martin, theorem XIV, pp. 305-306) on toy
--   enumerations: at most i elements of S_i enter A, and for j < i, if
--   S_i - W_j has exactly one element, it is in A (so W_j supset A gives
--   S_i subset W_j or two elements of S_i outside W_j).
-- * The proof of theorem XVIII (p. 311): for a decreasing sequence
--   C_(n+1) = C_n cap B_(n+1) the printed differences C'_(n+1) - C'_n are
--   empty, the corrected C'_n - C'_(n+1) are not (random families).
-- * § 12.6 (pp. 308-313): the two diagrams (as drawn in
--   content/diagrams/12-06-implications.typ) have exactly the
--   implications stated in the text; every pair not implied in the closure
--   is refuted by one of the non-implications the text cites; the
--   restricted properties (1)*-(10)* of p. 313 with (2)* => (1)*,
--   (9)* => (8)*, (6)* => (5)* and the cited non-implications: the open
--   question (9)* => (4)* is neither implied nor refuted, and the
--   consequences (6)* =/=> (2)*, (3)*, (4)* follow; corollary XIX read as
--   corrected ("no set outside (2)* is in both (6)* and (9)*") gives
--   (6)* =/=> (9)* from the set of exercise 12-62 in (6)* - (2)*; read as
--   printed ("no set in (2)*") it contradicts (2)* => (6)*, (2)* => (9)*
--   and the existence of maximal sets.  Property (8) read literally
--   ("no retraceable subsets") is empty: every one-element set is
--   retraceable.
--
-- Not established: the recursion-theoretic content (recursive
-- enumerability, maximality, cohesiveness of the infinite sets); the
-- non-implications themselves (they are the book's results, taken as
-- data).
module Main (main) where

import Data.Bits (complement, shiftR, testBit, xor, (.&.), (.|.))
import Data.List (nub, sort, subsequences)
import Data.Word (Word64)

import Harness

------------------------------------------------------------------------
-- Finite lattices

data Lat = Lat { lname :: String, els :: [Int], leq :: Int -> Int -> Bool }

joinL, meetL :: Lat -> Int -> Int -> Int
joinL l a b = head [c | c <- ups, all (leq l c) ups]
  where ups = [c | c <- els l, leq l a c, leq l b c]
meetL l a b = head [c | c <- downs, all (\d -> leq l d c) downs]
  where downs = [c | c <- els l, leq l c a, leq l c b]

-- | The elements are a lattice (all joins and meets exist).
isLattice :: Lat -> Bool
isLattice l = and [ not (null (lubs a b)) && not (null (glbs a b)) | a <- els l, b <- els l ]
  where
    lubs a b = let ups = [c | c <- els l, leq l a c, leq l b c] in [c | c <- ups, all (leq l c) ups]
    glbs a b = let ds = [c | c <- els l, leq l c a, leq l c b] in [c | c <- ds, all (\d -> leq l d c) ds]

powerset :: Int -> Lat
powerset k = Lat ("2^" ++ show k) [0 .. 2 ^ k - 1] (\a b -> a .&. b == a)

divisors :: Int -> Lat
divisors n = Lat ("div " ++ show n) [d | d <- [1 .. n], n `mod` d == 0] (\a b -> b `mod` a == 0)

chain :: Int -> Lat
chain k = Lat ("chain " ++ show k) [0 .. k - 1] (<=)

prod23 :: Lat
prod23 = Lat "2 x 3" [3 * a + b | a <- [0, 1], b <- [0 .. 2]]
  (\x y -> x `div` 3 <= y `div` 3 && x `mod` 3 <= y `mod` 3)

-- | M_3 (0, three atoms, 1) and N_5 (0 < a < c < 1, 0 < b < 1).
m3, n5 :: Lat
m3 = Lat "M3" [0 .. 4] (\a b -> a == b || a == 0 || b == 4)
n5 = Lat "N5" [0 .. 4] (\a b -> a == b || a == 0 || b == 4 || (a == 1 && b == 2))

distributive :: [Lat]
distributive = [powerset 3, powerset 4, divisors 30, divisors 60, chain 3, chain 4, prod23]

boolean :: [Lat]
boolean = [powerset 3, powerset 4, divisors 30]

bottom, top :: Lat -> Int
bottom l = head [a | a <- els l, all (leq l a) (els l)]
top l = head [a | a <- els l, all (\b -> leq l b a) (els l)]

-- | The complement in a Boolean algebra.
compl :: Lat -> Int -> Int
compl l a = head [b | b <- els l, meetL l a b == bottom l, joinL l a b == top l]

isIdeal, isDual :: Lat -> [Int] -> Bool
isIdeal l i = not (null i) && and [joinL l a b `elem` i | a <- i, b <- i] && and [meetL l a c `elem` i | a <- els l, c <- i]
isDual l d = not (null d) && and [meetL l a b `elem` d | a <- d, b <- d] && and [joinL l a c `elem` d | a <- els l, c <- d]

allSubsets :: Lat -> [[Int]]
allSubsets l = subsequences (els l)

-- | All (dual) ideals: every subset tested for at most 8 elements; in a
-- larger finite lattice the principal ones (every (dual) ideal of a
-- finite lattice is principal), each tested.
ideals, duals :: Lat -> [[Int]]
ideals l
  | length (els l) <= 8 = filter (isIdeal l) (allSubsets l)
  | otherwise = filter (isIdeal l) [[a | a <- els l, leq l a c] | c <- els l]
duals l
  | length (els l) <= 8 = filter (isDual l) (allSubsets l)
  | otherwise = filter (isDual l) [[a | a <- els l, leq l c a] | c <- els l]

relI, relD :: Lat -> [Int] -> Int -> Int -> Bool
relI l i a b = or [joinL l a c1 == joinL l b c2 | c1 <- i, c2 <- i]
relD l d a b = or [meetL l a c1 == meetL l b c2 | c1 <- d, c2 <- d]

congruence :: Lat -> (Int -> Int -> Bool) -> Bool
congruence l r =
  and [r a a | a <- es]
  && and [r b a | a <- es, b <- es, r a b]
  && and [r a c | a <- es, b <- es, r a b, c <- es, r b c]
  && and [ r (joinL l a1 b1) (joinL l a2 b2) && r (meetL l a1 b1) (meetL l a2 b2)
         | a1 <- es, a2 <- es, r a1 a2, b1 <- es, b2 <- es, r b1 b2 ]
  where es = els l

classOf :: Lat -> (Int -> Int -> Bool) -> Int -> [Int]
classOf l r a = [b | b <- els l, r a b]

theoremIChecks :: [(String, Bool)]
theoremIChecks =
  concat [ [ (lname l ++ ", ideal " ++ show i ++ ": a congruence", congruence l (relI l i))
           , (lname l ++ ", ideal " ++ show i ++ ": I is a class", and [sort (classOf l (relI l i) c) == sort i | c <- i])
           , (lname l ++ ", ideal " ++ show i ++ ": I is the zero", and [relI l i (joinL l c a) a | c <- i, a <- els l])
           , (lname l ++ ", ideal " ++ show i ++ ": ex. 12-6", and [ relI l i (joinL l a b) b == any (\c -> leq l a (joinL l b c)) i
                                                                 | a <- els l, b <- els l ]) ]
         | l <- distributive, length (els l) <= 12, i <- ideals l ]
  ++ concat [ [ (lname l ++ ", dual ideal " ++ show d ++ ": a congruence", congruence l (relD l d))
              , (lname l ++ ", dual ideal " ++ show d ++ ": D is a class", and [sort (classOf l (relD l d) c) == sort d | c <- d])
              , (lname l ++ ", dual ideal " ++ show d ++ ": D is the unit", and [relD l d (meetL l c a) a | c <- d, a <- els l]) ]
            | l <- distributive, length (els l) <= 12, d <- duals l ]
  ++ concat [ [ (lname l ++ ", ideal " ++ show i ++ ": the complement respects the classes",
                 and [relI l i (compl l a) (compl l b) | a <- els l, b <- els l, relI l i a b])
              , (lname l ++ ", ideal " ++ show i ++ ": the relations of I and D = {a | a-bar in I} coincide",
                 let d = [a | a <- els l, compl l a `elem` i] in and [relI l i a b == relD l d a b | a <- els l, b <- els l]) ]
            | l <- boolean, length (els l) <= 8, i <- ideals l ]
  ++ [ ("2^3: every subset I: I ideal <=> {a | a-bar in I} dual ideal",
        let l = powerset 3 in and [isIdeal l i == isDual l [a | a <- els l, compl l a `elem` i] | i <- allSubsets l])
     , ("p. 290: a-bar u c = (a cap c-bar)-bar in the Boolean algebras",
        and [joinL l (compl l a) c == compl l (meetL l a (compl l c)) | l <- boolean, a <- els l, c <- els l])
     , ("(d): the classes meeting a sublattice M of 2^3 form a sublattice of L/I",
        let l = powerset 3
            subl = [m | m <- allSubsets l, not (null m), and [joinL l a b `elem` m && meetL l a b `elem` m | a <- m, b <- m]]
        in and [ and [ any (\c -> relI l i c (joinL l a b)) m && any (\c -> relI l i c (meetL l a b)) m | a <- m, b <- m ]
               | i <- ideals l, m <- subl ]) ]

exerciseChecks :: [(String, Bool)]
exerciseChecks =
  [ ("12-2: {A subset {1,2,3} | [1, 2 in A] => 3 in A} is a lattice under subset",
     isLattice (Lat "M" mFam (\a b -> a .&. b == a)))
  , ("12-2: its join of {1}, {2} is {1, 2, 3}, not {1} u {2}",
     joinL (Lat "M" mFam (\a b -> a .&. b == a)) (bit 1) (bit 2) == bit 1 .|. bit 2 .|. bit 3
     && (bit 1 .|. bit 2) `notElem` mFam)
  , ("12-3: complements are unique in the distributive lattices",
     and [ length [b | b <- els l, meetL l a b == bottom l, joinL l a b == top l] <= 1 | l <- distributive, a <- els l ])
  , ("12-3: an atom of M_3 has two complements", length [b | b <- els m3, meetL m3 1 b == 0, joinL m3 1 b == 4] == 2)
  , ("12-4: both distributive laws hold in the distributive lattices", all (\l -> law1 l && law2 l) distributive)
  , ("12-4: both laws fail in M_3 and N_5", not (law1 m3) && not (law2 m3) && not (law1 n5) && not (law2 n5))
  , ("M_3 and N_5 are lattices", isLattice m3 && isLattice n5)
  , ("12-5: the identities in the Boolean algebras",
     and [ compl l (compl l a) == a && joinL l a (top l) == top l && meetL l a (top l) == a
           && joinL l a (bottom l) == a && meetL l a (bottom l) == bottom l
           && compl l (joinL l a b) == meetL l (compl l a) (compl l b)
           && compl l (meetL l a b) == joinL l (compl l a) (compl l b)
           && joinL l (meetL l a b) (meetL l a (compl l b)) == a
         | l <- boolean, a <- els l, b <- els l ])
  , ("12-9 (i), (ii): 2^3 onto 2^1 by a bit: the kernel is an ideal, the quotient has 2 classes",
     let l = powerset 3 in and [ isIdeal l ker && length (nub [minimum (classOf l (relI l ker) a) | a <- els l]) == 2
                               | k <- [0 .. 2], let ker = [a | a <- els l, not (testBit a k)] ])
  , ("12-9 (iii): chain 3 onto chain 2 by 0, 1, 1: kernel {0}, the quotient has 3 classes",
     let l = chain 3; ker = [0] in isIdeal l ker && length (nub [minimum (classOf l (relI l ker) a) | a <- els l]) == 3)
  , ("12-9 (iii): 0, 1, 1 is a homomorphism of chain 3 onto chain 2",
     let h a = if a == 0 then 0 else 1 :: Int
     in and [h (max a b) == max (h a) (h b) && h (min a b) == min (h a) (h b) | a <- [0 .. 2], b <- [0 .. 2]])
  , ("12-10 (a): maximal dual ideals are prime in the distributive lattices",
     and [ prime l d | l <- distributive, length (els l) <= 12, d <- maximalDuals l ])
  , ("12-10 (b): prime dual ideals are maximal in the Boolean algebras",
     and [ d `elem` maximalDuals l | l <- boolean, length (els l) <= 8, d <- duals l, prime l d ])
  , ("12-10 (b): prime ideals are maximal in the Boolean algebras",
     and [ i `elem` maximalIdeals l | l <- boolean, length (els l) <= 8, i <- ideals l, primeIdeal l i ])
  , ("12-10: in the chain of 3 the prime dual ideal {2} is not maximal",
     let l = chain 3 in prime l [2] && [2] `notElem` maximalDuals l) ]
  where
    bit k = 2 ^ (k :: Int) :: Int
    mFam = [a | a <- [0 .. 15], even a, not (testBit a 1 && testBit a 2) || testBit a 3]
    law1 l = and [ joinL l a (meetL l b c) == meetL l (joinL l a b) (joinL l a c) | a <- els l, b <- els l, c <- els l ]
    law2 l = and [ meetL l a (joinL l b c) == joinL l (meetL l a b) (meetL l a c) | a <- els l, b <- els l, c <- els l ]
    proper l d = length d < length (els l)
    maximalDuals l = let ps = [d | d <- duals l, proper l d] in [d | d <- ps, not (any (\e -> e /= d && all (`elem` e) d) ps)]
    maximalIdeals l = let ps = [i | i <- ideals l, proper l i] in [i | i <- ps, not (any (\e -> e /= i && all (`elem` e) i) ps)]
    prime l d = proper l d && and [ a `elem` d || b `elem` d | a <- els l, b <- els l, joinL l a b `elem` d ]
    primeIdeal l i = proper l i && and [ a `elem` i || b `elem` i | a <- els l, b <- els l, meetL l a b `elem` i ]

------------------------------------------------------------------------
-- A small random generator (splitmix64)

newtype Gen = Gen Word64

next :: Gen -> (Word64, Gen)
next (Gen s) = (z3, Gen s')
  where
    s' = s + 0x9e3779b97f4a7c15
    z1 = (s' `xor` (s' `shiftR` 30)) * 0xbf58476d1ce4e5b9
    z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94d049bb133111eb
    z3 = z2 `xor` (z2 `shiftR` 31)

below :: Int -> Gen -> (Int, Gen)
below k g = let (w, g') = next g in (fromIntegral (w `mod` fromIntegral k), g')

draws :: Int -> (Gen -> (a, Gen)) -> Gen -> ([a], Gen)
draws 0 _ g = ([], g)
draws k f g = let (a, g1) = f g; (as, g2) = draws (k - 1) f g1 in (a : as, g2)

shuffleL :: [a] -> Gen -> ([a], Gen)
shuffleL [] g = ([], g)
shuffleL xs g = let (i, g1) = below (length xs) g
                    (rest, g2) = shuffleL (take i xs ++ drop (i + 1) xs) g1
                in (xs !! i : rest, g2)

-- | A toy enumeration: (element, step at which it appears).
type Enum' = [(Int, Int)]

upTo :: Enum' -> Int -> [Int]
upTo w n = [x | (x, t) <- w, t <= n]

------------------------------------------------------------------------
-- Theorem IV (Friedberg's splitting)

splittingChecks :: [(String, Bool)]
splittingChecks = concatMap one [1 .. 800]
  where
    one s =
      let g0 = Gen (fromIntegral (120000 + 31 * s))
          (perm, g1) = shuffleL [0 .. 39] g0
          f = take 30 perm                       -- f(0), f(1), ...: A
          (ws, _) = draws 30 randomEnum g1       -- W_0, ..., W_29
          step (b1, b2, xs) n =                  -- stage n + 1, n <= 28
            let y = f !! (n + 1)
                cands = [ x | x <- [0 .. n], let w = upTo (ws !! x) n
                            , y `elem` w, null [z | z <- b1, z `elem` w] || null [z | z <- b2, z `elem` w] ]
            in case cands of
                 (x : _) -> if null [z | z <- b1, z `elem` upTo (ws !! x) n]
                              then (y : b1, b2, x : xs) else (b1, y : b2, x : xs)
                 [] -> (y : b1, b2, xs)
          (bb1, bb2, chosen) = foldl step ([head f], [], []) [0 .. 28]
      in [ ("run " ++ show s ++ ": B_1 u B_2 = A, B_1 cap B_2 = 0",
            sort (bb1 ++ bb2) == sort f)
         , ("run " ++ show s ++ ": x_n takes each value at most twice",
            all (\x -> length (filter (== x) chosen) <= 2) (nub chosen)) ]
    randomEnum g = let (k, g1) = below 12 g
                       (xs, g2) = draws k (below 40) g1
                       (ts, g3) = draws k (below 30) g2
                   in (zip xs ts, g3)

------------------------------------------------------------------------
-- Theorem XI: z-states and the maximal set construction

-- | The lexicographic order of bit strings of equal length (b_0 first).
lexGT :: [Bool] -> [Bool] -> Bool
lexGT a b = dropWhile (uncurry (==)) (zip a b) `startsWith` (True, False)
  where startsWith ((p, q) : _) (x, y) = p == x && q == y
        startsWith [] _ = False

zStateChecks :: [(String, Bool)]
zStateChecks =
  [ ("property (ii) for strings of length " ++ show k, and [ not (lexGT (take (z + 1) y) (take (z + 1) x)) || lexGT (take (z' + 1) y) (take (z' + 1) x)
                                                            | x <- strings k, y <- strings k, z <- [0 .. k - 1], z' <- [z + 1 .. k - 1] ])
  | k <- [1 .. 7] ]
  ++ [ ("property (i): states only grow when bits turn on (length " ++ show k ++ ")",
        and [ not (lexGT x y) | x <- strings k, y <- strings k, and (zipWith (\p q -> not p || q) x y) ]) | k <- [1 .. 7] ]
  where strings k = sequence (replicate k [False, True])

-- | The toy W_z: multiples of z + 2 (z < 4) and a finite set, element x
-- appearing at step x + 3z.
toyW :: Int -> Int -> Int -> Bool
toyW z n x
  | z < 4 = x `mod` (z + 2) == 0 && x + 3 * z <= n
  | z == 4 = x `elem` [5, 11, 17, 23, 30, 31] && x + 3 * z <= n
  | otherwise = False

-- | The z-state of x at stage n + 1 (the bits of W_i, i > 4, are 0).
zState :: Int -> Int -> Int -> [Bool]
zState n z x = [i <= 4 && toyW i (n + 1) x && i <= n | i <- [0 .. z]]

-- | The 4-state: the m-states for m >= 4 compare as the 4-states.
state4 :: Int -> Int -> [Bool]
state4 n = zState n 4

-- | Marker positions x_0 < x_1 < ...: the first `width` and an offset for
-- the rest (x_p = p + off for p >= width).
data Markers = Markers { firstPos :: [Int], off :: Int }

width :: Int
width = 120

posM :: Markers -> Int -> Int
posM mk p = if p < width then firstPos mk !! p else p + off mk

data MS = MS { mks :: Markers, aSet :: [Int], movesLog :: [(Int, Int, Int, Int)] }   -- (stage, m, old, new)

-- | Stage n + 1 of the construction.  Only markers at numbers <= n + 1
-- can be in a nonzero state (nothing larger is enumerated yet); for
-- m >= 4 the least m is found with the suffix maxima of the 4-states.
stageMax :: MS -> Int -> MS
stageMax st n =
  let mk = mks st
      relevant = takeWhile (\p -> posM mk p <= n + 1) [0 ..]
      states = [state4 n (posM mk p) | p <- relevant]
      pre m p = take (m + 1) (states !! p)
      firstBigger m = [q' | q' <- drop (m + 1) relevant, lexGT (pre m q') (pre m m)]
      small = [ (m, q) | m <- takeWhile (< 4) relevant, (q : _) <- [firstBigger m] ]
      sufs = drop 1 (scanr max [] states)          -- sufs !! m = max of the states of p > m
      large = [ m | (m, s, sup) <- zip3 [4 ..] (drop 4 states) (drop 4 sufs), sup > s ]
      cands = small ++ [ (m, q) | m <- take 1 large, (q : _) <- [firstBigger m] ]
  in case cands of
       [] -> st
       ((m, q) : _) ->
         let s = q - m
             newPos p
               | p < m = posM mk p
               | otherwise = posM mk (p + s)
             mk' = Markers (map newPos [0 .. width - 1]) (off mk + s)
             lost = [y | y <- [posM mk m .. posM mk q - 1], y `notElem` aSet st]
         in MS mk' (aSet st ++ lost) (movesLog st ++ [(n, m, posM mk m, posM mk q)])

maximalChecks :: [(String, Bool)]
maximalChecks =
  [ ("markers move only to larger numbers", and [new > old | (_, _, old, new) <- movesLog final])
  , ("x_0 < x_1 < ... at the end", and (zipWith (<) ps (drop 1 ps)))
  , ("the numbers without a marker are exactly A (numbers <= 100)",
     sort (aSet final) == [y | y <- [0 .. 100], y `notElem` ps] ++ filter (> 100) (sort (aSet final)))
  , ("A and the marker positions are disjoint", all (`notElem` ps) (aSet final))
  , ("a moved marker [m] reaches a larger m-state",
     and [ lexGT (zState n m new) (zState n m old) | (n, m, old, new) <- movesLog final ])
  , ("markers [0]..[3] do not move in stages 200..400", null [() | (n, m, _, _) <- movesLog final, n >= 200, m <= 3])
  , ("some markers moved", length (movesLog final) >= 5)
  , ("[0] stays at 0 (in W_0 from the start)", posM (mks final) 0 == 0) ]
  where
    final = foldl stageMax (MS (Markers [0 .. width - 1] 0) [] []) [0 .. 399]
    ps = map (posM (mks final)) [0 .. 80]

------------------------------------------------------------------------
-- Theorem XIV (Martin)

-- | S_i = the i + 1 numbers after 0, 1, ..., i(i + 1)/2 - 1.
blockS :: Int -> [Int]
blockS i = [i * (i + 1) `div` 2 .. i * (i + 1) `div` 2 + i]

martinChecks :: [(String, Bool)]
martinChecks = concatMap one [1 .. 300] ++ [("the rule puts elements into A in some run", any nonEmpty [1 .. 300])]
  where
    nonEmpty s = let g0 = Gen (fromIntegral (530000 + 17 * s))
                     (ws, _) = draws 8 randomW g0
                 in or [ length [y | y <- blockS i, y `elem` upTo (ws !! j) 40] == i
                       | i <- [1 .. 10], j <- [0 .. min 7 (i - 1)] ]
    one s =
      let g0 = Gen (fromIntegral (530000 + 17 * s))
          (ws, _) = draws 8 randomW g0           -- W_0, ..., W_7 on 0..65 (blocks S_0..S_10)
          blocks = [0 .. 10]
          stage a n = nub (a ++ [ x | i <- blocks, j <- [0 .. min 7 (i - 1)]
                                    , let w = upTo (ws !! j) n
                                    , length [y | y <- blockS i, y `elem` w] == i
                                    , x <- blockS i, x `notElem` w ])
          a = foldl stage [] [0 .. 40]
      in [ ("run " ++ show s ++ ", S_" ++ show i ++ ": at most i elements in A",
            length [x | x <- blockS i, x `elem` a] <= i) | i <- blocks ]
         ++ [ ("run " ++ show s ++ ", W_" ++ show j ++ ", S_" ++ show i ++ ": one element outside W_j => it is in A",
               let w = upTo (ws !! j) 40; out = [x | x <- blockS i, x `notElem` w]
               in length out /= 1 || all (`elem` a) out)
            | j <- [0 .. 7], i <- blocks, i > j ]
    randomW g = let (dense, g1) = below 3 g
                    (xs, g2) = draws 70 (below (if dense == 0 then 66 else 30)) g1
                    (ts, g3) = draws 70 (below 40) g2
                in (zip xs ts, g3)

------------------------------------------------------------------------
-- Theorem XVIII: the differences of a decreasing sequence

decreasingChecks :: [(String, Bool)]
decreasingChecks = concatMap one [1 .. 500]
  where
    one s =
      let g0 = Gen (fromIntegral (610000 + 13 * s))
          (bs, _) = draws 8 (\g -> let (m, g') = next g in (fromIntegral (m .&. 0xffffffff) :: Word64, g')) g0
          cs = scanl1 (.&.) (map (.|. 1) bs)     -- C_(n+1) = C_n cap B_(n+1), all contain 0
          pairs = zip cs (drop 1 cs)
      in [ ("family " ++ show s ++ ": C'_(n+1) - C'_n = 0 (printed)", all (\(c, c') -> c' .&. complement c == 0) pairs)
         , ("family " ++ show s ++ ": C'_n - C'_(n+1) is what can be nonempty", any (\(c, c') -> c .&. complement c' /= 0) pairs) ]

------------------------------------------------------------------------
-- § 12.6: the implications

type Imp = (Int, Int)

closure :: [Int] -> [Imp] -> [Imp]
closure ps arrows = fix (nub (arrows ++ [(p, p) | p <- ps]))
  where
    fix r = let r' = nub (r ++ [(a, c) | (a, b) <- r, (b', c) <- r, b == b']) in if length r' == length r then r else fix r'

-- | The arrows of the drawings (chains of content/diagrams/12-06-implications.typ).
chainsToArrows :: [[Int]] -> [Imp]
chainsToArrows = concatMap (\c -> zip c (drop 1 c))

diagram1, diagram2 :: [Imp]
diagram1 = chainsToArrows [[1, 2, 3, 4, 7], [2, 5, 6, 7]]
diagram2 = chainsToArrows [[1, 2, 3, 4, 8, 9, 10, 7], [2, 5, 6, 7], [6, 10]]

-- | The implications stated in the text (pp. 308, 312).
stated1, stated2 :: [Imp]
stated1 = [(1, 2), (2, 3), (3, 4), (4, 7), (2, 5), (5, 6), (6, 7)]
stated2 = stated1 ++ [(9, 10), (10, 7), (4, 8), (8, 9), (6, 10)]

-- | The non-implications cited (a set with the first property and without
-- the second): pp. 308-309 and 312.
refuted1, refuted2 :: [Imp]
refuted1 = [(3, 2), (4, 3), (7, 4), (7, 6), (2, 1), (5, 2), (6, 5), (3, 6), (5, 4)]
refuted2 = refuted1 ++ [(7, 10), (10, 9), (9, 8), (8, 4), (5, 9)]

-- | Every pair not in the closure is refuted: a counterexample to (i, j)
-- has every property implied by i and none implying j.
complete :: [Int] -> [Imp] -> [Imp] -> Bool
complete ps arrows refs = null (undecided ps arrows refs)

-- | The pairs neither implied nor refuted.
undecided :: [Int] -> [Imp] -> [Imp] -> [Imp]
undecided ps arrows refs =
  [ (a, b) | a <- ps, b <- ps, (a, b) `notElem` cl
  , not (any (\(i, j) -> (i, a) `elem` cl && (b, j) `elem` cl) refs) ]
  where cl = closure ps arrows

-- | No counterexample contradicts the closure (and the pair is decided).
consistent :: [Int] -> [Imp] -> [Imp] -> Bool
consistent ps arrows refs = all (`notElem` closure ps arrows) refs

implicationChecks :: [(String, Bool)]
implicationChecks =
  [ ("diagram 1 draws exactly the implications stated on p. 308", sort (nub diagram1) == sort stated1)
  , ("diagram 2: its closure is that of the implications stated on p. 312",
     sort (closure ps2 diagram2) == sort (closure ps2 stated2))
  , ("diagram 1: the cited non-implications do not contradict it", consistent ps1 stated1 refuted1)
  , ("diagram 1: no other implications (every other pair refuted)", complete ps1 stated1 refuted1)
  , ("diagram 2: the cited non-implications do not contradict it", consistent ps2 stated2 refuted2)
  , ("diagram 2: no other implications (every other pair refuted)", complete ps2 stated2 refuted2)
  , ("p. 313: (2)* => (1)*, (9)* => (8)*, (6)* => (5)* added; the cited non-implications are consistent",
     consistent ps2 starred starredRefuted)
  , ("p. 313: the only undecided pairs are (9)* => (4)* (open) and the equivalent (8)* => (4)*",
     undecided ps2 starred starredRefuted == [(8, 4), (9, 4)])
  , ("p. 313: (6)* =/=> (2)*, (3)*, (4)* follow from (6)* =/=> (9)*",
     all (refutedBy starred [(6, 9)]) [(6, 2), (6, 3), (6, 4)])
  , ("p. 313, corrected corollary XIX [(6)* & (9)* => (2)*] holds for every type a set in (2)* can have",
     -- the properties of a set of (2)* are those implied by (2)* (or more):
     -- it is in (6)* and (9)* and in (2)*
     and [ not (6 `elem` t && 9 `elem` t) || 2 `elem` t | t <- [upClosed 2, upClosed 1] ])
  , ("p. 313, printed: [(2)* => not ((6)* & (9)*)] contradicts (2)* => (6)*, (2)* => (9)* (maximal sets exist)",
     (2, 6) `elem` closure ps2 starred && (2, 9) `elem` closure ps2 starred)
  , ("property (8) read literally is empty: {x} is retraceable (psi(x) = x)",
     and [retraceable [x] (\_ -> Just x) | x <- [0 .. 20 :: Int]])
  , ("finite sets are retraceable", and [retraceable d (prevIn d) | d <- subsequences [0 .. 6 :: Int], not (null d)]) ]
  where
    ps1 = [1 .. 7]
    ps2 = [1 .. 10]
    starred = stated2 ++ [(2, 1), (9, 8), (6, 5)]
    starredRefuted = [(7, 10), (7, 6), (10, 9), (3, 2), (3, 6), (6, 9), (4, 3)]
    refutedBy arrows refs (a, b) = let cl = closure ps2 arrows in
      any (\(i, j) -> (i, a) `elem` cl && (b, j) `elem` cl) refs
    upClosed p = [q | (p', q) <- closure ps2 starred, p' == p]
    retraceable d psi = and [ psi x == Just (if x == minimum d then x else maximum [y | y <- d, y < x]) | x <- d ]
    prevIn d x = Just (if x == minimum d then x else maximum [y | y <- d, y < x])

main :: IO ()
main = do
  c <- newCounter
  group c "12.1 Th. I: quotient lattices of finite lattices" theoremIChecks
  group c "12.7 ex. 12-2 ... 12-10 on finite lattices" exerciseChecks
  group c "12.2 Th. IV (Friedberg splitting) on toy enumerations" splittingChecks
  group c "12.4 Th. XI: z-states" zStateChecks
  group c "12.4 Th. XI: the maximal set construction on toy enumerations" maximalChecks
  group c "12.5 Th. XIV (Martin) on toy enumerations" martinChecks
  group c "12.6 Th. XVIII: the differences of a decreasing sequence" decreasingChecks
  group c "12.6 the implications and the diagrams" implicationChecks
  finish c "ch12-lattice"
