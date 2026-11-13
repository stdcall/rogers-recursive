-- | Checks of chapter 6 and of chapter 7, sections 7.1-7.6 (pp. 106-122):
-- m- and 1-reductions, the join, the padding function t of theorem III,
-- the back-and-forth construction of Myhill's theorem VI with its lemma,
-- the construction of f' in the proof of theorem VII, the cylinder
-- reductions of theorem VIII, and exercises 7-4, 7-15 (b), 7-16, 7-29 on
-- models.
--
-- Run: runghc -ichecks/haskell checks/haskell/CheckCh05Reductions.hs
--
-- What is checked and where the expectations come from:
-- * Theorem 7-I (p. 110, th:reducibility-properties), (a)-(d), corollary
--   7-II (p. 112, cor:reducibility-not-complement) and theorem 7-II (b)
--   (p. 112, th:incomparable-semilattice, the join A (+) B = {2x | x in A}
--   union {2x + 1 | x in B} and the function h of the proof): on finite
--   universes, exhaustively over all subsets and all maps.  This covers
--   only the set-theoretic content (on a finite universe every map is
--   "recursive"); (e), (f) and the incomparability of K, K-bar are not
--   modelled.
-- * Theorem 7-III (pp. 113-114, th:k-one-complete): the inductive
--   definition of t from a padding function t' (t(x, y) = t'(x, z), z =
--   mu w [t'(x, w) /= t(x', y') for all <x', y'> < <x, y>]) on a model
--   numbering in which the code <k, p> computes the k-th function (p a
--   padding): t keeps the function, is one-one, and f^* = lambda x [t(f(x),
--   x)] is one-one for non-injective f; the model t' is not one-one in
--   both arguments, so the construction is needed.
-- * Theorem 7-VI (pp. 116-118, th:myhill-isomorphism): the lemma (the chain
--   f(x'), f(x_(i_1)), ...) and stages 0, 1, ..., 2k, 2k + 1 as printed, on
--   four pairs of model sets with 1-reductions g, h; after every stage the
--   pairs form a finite correspondence, after stage 2k + 1 the number k is
--   a first and a second component, the chains are at most n + 1 long, and
--   the limit map restricted to [0, 150] is one-one, onto [0, 150] (by the
--   inverse) and maps A to B, A-bar to B-bar.  The printed definition of a
--   finite correspondence with "1 <= i <= n, i <= j <= n" is the same
--   condition as with 1 <= j <= n (06-01 question).
-- * Theorem 7-VII (pp. 118-120, th:m-complete-iff-one-complete): the
--   construction of f' from f and the function g of the lemma, run with a
--   decidable stand-in S for K and a model cylinder A = B_0 x N with a g
--   satisfying both conditions of the lemma (checked on all nonempty finite
--   sets of codes below 13): f' is one-one, n in S iff f'(n) in A, and the
--   search for f'(n + 1) takes at most n + 1 values of g.
-- * Theorem 7-VIII (p. 121, th:cylinder-properties) and its corollary: the
--   reductions lambda x [<x, 0>], pi_1, lambda x [<f(x), x>] and the
--   composites of the proof of (d), on model sets.
-- * Exercise 7-4 (p. 133, ex:finite-difference-m-equivalent): the printed
--   statement fails for A = N, B = N - {0}: no map at all reduces B to N
--   (checked exhaustively on the finite universes of sizes 1-4; proved for
--   N in checks/lean/RogersRecursive/Ch05_07Numbering.lean); for infinite
--   A, B different from N with finite (A - B) union (B - A) the map that
--   sends A - B to a fixed element of B and B - A to a fixed element of
--   B-bar is a reduction (checked on [0, 2000] for four model pairs).
-- * Exercise 7-15 (b) (p. 134, ex:images-recursive, corrected "phi(N) =
--   N & A recursive"): phi(2x) = e(x), phi(2x + 1) = x with A the even
--   numbers gives phi(N) = N and phi(A) = Val e (here e enumerates a model
--   set; in the book e enumerates K, which makes phi(A) not recursive).
-- * Exercise 7-16 (p. 134, ex:partial-reducibilities), the partial answer
--   on finite universes: (i) and (ii) give two degrees ({empty} and the
--   nonempty sets), (iii) the degrees of finite sets are their
--   cardinalities (so there are infinitely many of them on N).
-- * Exercise 7-29 (p. 135, ex:join-complement-isomorphic) and the hint of
--   7-2: the permutation 2x <-> 2x + 1 maps A (+) A-bar onto its complement.
--
-- Not established: recursiveness of any of the maps (Church's thesis in
-- the book), the statements about K and r.e. sets, and anything beyond the
-- finite universes and ranges stated.
module Main (main) where

import Data.List (nub, sort, sortOn)

import Harness

------------------------------------------------------------------------
-- Pairs (section 5.3)

tau :: Integer -> Integer -> Integer
tau x y = (x * x + 2 * x * y + y * y + 3 * x + y) `div` 2

tri :: Integer -> Integer
tri n = n * (n + 1) `div` 2

untau :: Integer -> (Integer, Integer)
untau z = head [(x, s - x) | s <- [0 ..], tri (s + 1) > z, let x = z - tri s]

pi1, pi2 :: Integer -> Integer
pi1 = fst . untau
pi2 = snd . untau

isSquare :: Integer -> Bool
isSquare x = let r = floor (sqrt (fromInteger x :: Double)) :: Integer
             in any (\q -> q * q == x) [r - 1, r, r + 1]

isPrime :: Integer -> Bool
isPrime n = n >= 2 && all (\d -> n `mod` d /= 0) (takeWhile (\d -> d * d <= n) [2 ..])

------------------------------------------------------------------------
-- Finite universes

subsetsOf :: [a] -> [[a]]
subsetsOf [] = [[]]
subsetsOf (x : xs) = let r = subsetsOf xs in r ++ map (x :) r

-- | All maps from [0, n - 1] to [0, m - 1], as lists of values.
maps :: Int -> Int -> [[Int]]
maps n m = mapM (const [0 .. m - 1]) [1 .. n]

-- | All partial maps (Nothing: undefined).
partialMaps :: Int -> Int -> [[Maybe Int]]
partialMaps n m = mapM (const (Nothing : map Just [0 .. m - 1])) [1 .. n]

reduces :: Int -> [Int] -> [Int] -> [Int] -> Bool
reduces n a b f = and [(x `elem` a) == ((f !! x) `elem` b) | x <- [0 .. n - 1]]

injective :: Eq b => [b] -> Bool
injective vs = length (nub vs) == length vs

mRed, oneRed :: Int -> Int -> [Int] -> [Int] -> Bool
mRed n m a b = any (reduces n a b) (maps n m)
oneRed n m a b = any (\f -> injective f && reduces n a b f) (maps n m)

compl :: Int -> [Int] -> [Int]
compl n a = [x | x <- [0 .. n - 1], x `notElem` a]

join :: [Int] -> [Int] -> [Int]
join a b = sort ([2 * x | x <- a] ++ [2 * x + 1 | x <- b])

------------------------------------------------------------------------
-- Theorem VI: finite correspondences, the lemma, the stages

type Corr = [(Integer, Integer)]

-- | The printed definition: i /= j => x_i /= x_j & y_i /= y_j for
-- 1 <= i <= n, i <= j <= n; and (ii) x_i in A <=> y_i in B.
isCorrPrinted, isCorrFull :: (Integer -> Bool) -> (Integer -> Bool) -> Corr -> Bool
isCorrPrinted pa pb ps = distinct [(i, j) | i <- [0 .. n - 1], j <- [i .. n - 1]] && agree pa pb ps
  where
    n = length ps
    distinct ijs = and [fst (ps !! i) /= fst (ps !! j) && snd (ps !! i) /= snd (ps !! j) | (i, j) <- ijs, i /= j]
isCorrFull pa pb ps = injective (map fst ps) && injective (map snd ps) && agree pa pb ps

agree :: (Integer -> Bool) -> (Integer -> Bool) -> Corr -> Bool
agree pa pb ps = and [pa x == pb y | (x, y) <- ps]

-- | The lemma: from f (C <=_1 D via f), a finite correspondence and x' not
-- a first component, the chain f(x'), f(x_(i_1)), ...; returns y' and the
-- number of values of f computed.
lemmaExt :: (Integer -> Integer) -> Corr -> Integer -> (Integer, Int)
lemmaExt f ps x' = go x' 1
  where
    go u k = let y = f u
             in case [x | (x, y0) <- ps, y0 == y] of
                  (x : _) -> go x (k + 1)
                  [] -> (y, k)

-- | One stage of the construction (stage 0, 1, 2, ...), as printed:
-- stage 2k adds a pair with first component k (lemma with g), stage 2k + 1
-- one with second component k (lemma with h, the roles of A and B
-- exchanged), unless k already occurs there.  Returns the new list and the
-- length of the chain (0 if the stage adds nothing).
stageStep :: (Integer -> Integer) -> (Integer -> Integer) -> Corr -> Integer -> (Corr, Int)
stageStep g h ps s
  | even s = if k `elem` map fst ps then (ps, 0)
             else let (y, l) = lemmaExt g ps k in (ps ++ [(k, y)], l)
  | otherwise = if k `elem` map snd ps then (ps, 0)
                else let (x, l) = lemmaExt h [(y0, x0) | (x0, y0) <- ps] k in (ps ++ [(x, k)], l)
  where k = s `div` 2

stages :: (Integer -> Integer) -> (Integer -> Integer) -> [(Corr, Int)]
stages g h = scanl (\(ps, _) s -> stageStep g h ps s) ([], 0) [0 ..]

nextPrimeLike :: (Integer -> Bool) -> Integer -> Integer
nextPrimeLike p x = head [y | y <- [x + 1 ..], p y == p x]

myhillModels :: [(String, Integer -> Bool, Integer -> Bool, Integer -> Integer, Integer -> Integer)]
myhillModels =
  [ ( "A = 3N, B = 2N, g(x) = 2x (+1), h(y) = 3y (+1)"
    , \x -> x `mod` 3 == 0, even
    , \x -> if x `mod` 3 == 0 then 2 * x else 2 * x + 1
    , \y -> if even y then 3 * y else 3 * y + 1 )
  , ("A = B = 2N, g = lambda x [x + 2], h = lambda x [x]", even, even, (+ 2), id)
  , ( "A = B = primes, g = h = the next number of the same kind"
    , isPrime, isPrime, nextPrimeLike isPrime, nextPrimeLike isPrime )
  , ( "A = B = 2N, g, h: parity kept, x div 2 permuted in blocks of 16"
    , even, even, parityPerm 1, parityPerm 12 ) ]

-- | A pseudo-random sequence (a linear congruential generator).
lcg :: Integer -> [Integer]
lcg seed = drop 1 (iterate (\v -> (v * 1103515245 + 12345) `mod` 2147483648) seed)

-- | 2 p(x div 2) + x mod 2, p a pseudo-random permutation of each block
-- [16m, 16m + 15]: one-one, onto, and keeps the parity.
parityPerm :: Integer -> Integer -> Integer
parityPerm seed x = 2 * (16 * m + perm !! fromInteger r) + x `mod` 2
  where
    (m, r) = (x `div` 2) `divMod` 16
    perm = map snd (sortOn fst (zip (take 16 (lcg (seed + 7919 * m))) [0 :: Integer ..]))

------------------------------------------------------------------------
-- Theorem VII: the model cylinder and the construction of f'

-- | A = B_0 x N, B_0 = {u | u mod 3 = 1}.
inA :: Integer -> Bool
inA z = pi1 z `mod` 3 == 1

-- | g of the lemma on a nonempty finite set D (its canonical index is
-- sum 2^d): <pi_1(min D), 1 + max pi_2(D)>, on the side of min D.
gCyl :: [Integer] -> Integer
gCyl ds = tau (pi1 (minimum ds)) (1 + maximum (map pi2 ds))

-- | The stand-in S for K and a non-injective f with n in S iff f(n) in A.
inS :: Integer -> Bool
inS n = n `mod` 5 `elem` [0, 2]

fS :: Integer -> Integer
fS n = if inS n then tau 1 (n `mod` 2) else tau 0 (n `mod` 3)

-- | f'(0), f'(1), ... with the number of values of g used for each.
fPrime :: [(Integer, Int)]
fPrime = go 0 []
  where
    go n prev
      | fS n `notElem` prev = (fS n, 0) : go (n + 1) (prev ++ [fS n])
      | otherwise = let (y, k) = search [fS n] 1 in (y, k) : go (n + 1) (prev ++ [y])
      where
        search ds k = let y = gCyl ds
                      in if y `notElem` prev then (y, k) else search (ds ++ [y]) (k + 1)

------------------------------------------------------------------------

main :: IO ()
main = do
  c <- newCounter

  let n3 = 3
      sets3 = subsetsOf [0 .. n3 - 1]
  group c "theorem 7-I (a)-(d) on the universe {0, 1, 2}, all subsets and maps"
    ( [ ("reflexive " ++ show a, reduces n3 a a [0 .. n3 - 1] && injective [0 .. n3 - 1 :: Int]) | a <- sets3 ]
      ++ [ ("transitive via the composite " ++ show (a, b, d),
            and [ reduces n3 a d [g !! (f !! x) | x <- [0 .. n3 - 1]]
                  && (not (injective f && injective g) || injective [g !! (f !! x) | x <- [0 .. n3 - 1]])
                | f <- maps n3 n3, reduces n3 a b f, g <- maps n3 n3, reduces n3 b d g ])
         | a <- sets3, b <- sets3, d <- sets3 ]
      ++ [ ("(b), (c), (d) " ++ show (a, b),
            (not (oneRed n3 n3 a b) || mRed n3 n3 a b)
            && (not (oneRed n3 n3 a b) || oneRed n3 n3 (compl n3 a) (compl n3 b))
            && (not (mRed n3 n3 a b) || mRed n3 n3 (compl n3 a) (compl n3 b)))
         | a <- sets3, b <- sets3 ]
      ++ [ ("corollary 7-II: A <=m B and not A <=m B-bar for A = B = {0, 1, 2}",
            mRed n3 n3 [0, 1, 2] [0, 1, 2] && not (mRed n3 n3 [0, 1, 2] []))
         , ("(a) of theorem 7-II: N and the empty set are incomparable",
            not (mRed n3 n3 [0, 1, 2] []) && not (mRed n3 n3 [] [0, 1, 2])) ] )

  group c "theorem 7-II (b): the join is the least upper bound ({0, 1, 2} and C in {0, ..., 3})"
    ( [ ("A <=m A (+) B via 2x, B via 2x + 1 " ++ show (a, b),
         reduces 3 a (join a b) [2 * x | x <- [0 .. 2]] && reduces 3 b (join a b) [2 * x + 1 | x <- [0 .. 2]])
      | a <- sets3, b <- sets3 ]
      ++ [ ("h(2x) = f(x), h(2x + 1) = g(x) reduces A (+) B to C " ++ show (a, b, d),
            and [ reduces 6 (join a b) d [if even z then f !! (z `div` 2) else g !! (z `div` 2) | z <- [0 .. 5]]
                | f <- maps 3 4, reduces 3 a d f, g <- maps 3 4, reduces 3 b d g ]
            && (mRed 6 4 (join a b) d == (mRed 3 4 a d && mRed 3 4 b d)))
         | a <- sets3, b <- sets3, d <- subsetsOf [0 .. 3] ] )

  -- the padding of theorem III on the model numbering: code <k, p> computes the k-th function
  let cls = pi1
      t' x y = tau (pi1 x) (pi2 x + y + 1)
      bound = 600 :: Integer
      -- (code of <x, y>, t(x, y), z) in the order of the codes
      tTable = foldl step [] [0 .. bound - 1]
        where
          step acc code =
            let (x, _) = untau code
                used = [v | (_, v, _) <- acc]
                z = head [w | w <- [0 ..], t' x w `notElem` used]
            in acc ++ [(code, t' x z, z)]
      t x y = head [v | (code, v, _) <- tTable, code == tau x y]
  group c "theorem 7-III: the padding t of Davis on a model numbering"
    ( [ ("t' is not one-one in both arguments: t'(<0,0>, 1) = t'(<0,1>, 0)", t' (tau 0 0) 1 == t' (tau 0 1) 0)
      , ("t one-one on the first 600 pairs", injective [v | (_, v, _) <- tTable])
      , ("mu w terminates: z <= number of earlier pairs", and [z <= i | (i, (_, _, z)) <- zip [0 ..] tTable])
      , ("the search is used (some z > 0)", any (\(_, _, z) -> z > 0) tTable)
      , ("t(0, 0) = t'(0, 0)", t 0 0 == t' 0 0) ]
      ++ [ ("phi_t(x, y) = phi_x: " ++ show (untau code), cls v == cls (pi1 code)) | (code, v, _) <- tTable ]
      ++ [ ("f^* = lambda x [t(f(x), x)] one-one, f = " ++ name,
            let vs = [t (f x) x | x <- [0 .. 15]] in injective vs && all (\x -> cls (t (f x) x) == cls (f x)) [0 .. 15])
         | (name, f) <- [("lambda x [x div 3]", (`div` 3)), ("lambda x [0]", const 0), ("lambda x [x mod 4]", (`mod` 4))] ] )

  group c "06-01 question: 'i <= j <= n' and '1 <= j <= n' define the same finite correspondences"
    [ ("random lists of pairs " ++ show k, isCorrPrinted even even ps == isCorrFull even even ps)
    | (k, ps) <- zip [0 :: Int ..] samples ]

  group c "theorem 7-VI: the lemma and the stages (finite correspondences, chains <= n + 1)"
    ( concat
      [ [ (name ++ ": after stage " ++ show s ++ " a finite correspondence", isCorrFull pa pb ps)
        , (name ++ ": chain of stage " ++ show s ++ " at most n + 1", l <= length ps)
        , (name ++ ": after stage " ++ show s ++ " the stage's number is placed",
           let k = (s - 1) `div` 2 in if even (s - 1) then k `elem` map fst ps else k `elem` map snd ps) ]
      | (name, pa, pb, g, h) <- myhillModels
      , (s, (ps, l)) <- zip [1 :: Integer ..] (take 400 (tail (stages g h))) ]
      ++ [ (name ++ ": stage 0 gives <0, g(0)>; stage 1 adds nothing iff g(0) = 0",
            let sts = stages g h
            in fst (sts !! 1) == [(0, g 0)] && ((length (fst (sts !! 2)) == 1) == (g 0 == 0)))
         | (name, _, _, g, h) <- myhillModels ]
      ++ [ ("chains longer than 2 occur; the longest in the models: " ++ show longest, maximum longest > 2)
         | let longest = [maximum (map snd (take 400 (stages g h))) | (_, _, _, g, h) <- myhillModels] ] )

  group c "theorem 7-VI: the limit map on [0, 150] is a recursive isomorphism of A and B"
    [ (name, let ps = fst (stages g h !! 302)
                 sigma x = head [y | (x0, y) <- ps, x0 == x]
                 sigmaInv y = head [x | (x, y0) <- ps, y0 == y]
             in injective (map sigma [0 .. 150])
                && all (\y -> sigma (sigmaInv y) == y) [0 .. 150]
                && all (\x -> pa x == pb (sigma x)) [0 .. 150])
    | (name, pa, pb, g, h) <- myhillModels ]

  let finiteSetsOfCodes = filter (not . null) (subsetsOf [0 .. 12])
  group c "theorem 7-VII: the model g has both properties of the lemma"
    ( [ ("D = " ++ show ds,
         (not (all inA ds) || (inA (gCyl ds) && gCyl ds `notElem` ds))
         && (not (all (not . inA) ds) || (not (inA (gCyl ds)) && gCyl ds `notElem` ds)))
      | ds <- finiteSetsOfCodes ]
      ++ [("the stand-in f is not one-one", not (injective (map fS [0 .. 20])))]
      ++ [("n in S iff f(n) in A, n = " ++ show n, inS n == inA (fS n)) | n <- [0 .. 300]] )

  let fps = take 301 fPrime
  group c "theorem 7-VII: the construction of f' (pp. 119)"
    ( [ ("f' one-one on [0, 300]", injective (map fst fps))
      , ("the search is used (f(n + 1) repeats)", any ((> 0) . snd) fps)
      , ("some searches take more than one value of g", any ((> 1) . snd) fps) ]
      ++ [("n in S iff f'(n) in A, n = " ++ show n, inS n == inA y) | (n, (y, _)) <- zip [0 ..] fps]
      ++ [("at most n + 1 values of g for f'(n + 1), n + 1 = " ++ show n, k <= fromInteger n) | (n, (_, k)) <- zip [0 ..] fps]
      ++ [("f'(n) = f(n) when f(n) is new, n = " ++ show n, k > 0 || y == fS n) | (n, (y, k)) <- zip [0 ..] fps] )

  let cylModels = [("even", even), ("prime", isPrime), ("x mod 5 = 1", \x -> x `mod` 5 == 1)]
      inTimesN p z = p (pi1 z)
  group c "theorem 7-VIII and corollary: the cylinder reductions"
    ( [ (na ++ ": (a) A <=_1 A x N via lambda x [<x, 0>]",
         injective (map (`tau` 0) [0 .. 500]) && all (\x -> pa x == inTimesN pa (tau x 0)) [0 .. 500])
      | (na, pa) <- cylModels ]
      ++ [ (na ++ ": (b) A x N <=m A via pi_1", all (\z -> inTimesN pa z == pa (pi1 z)) [0 .. 3000])
         | (na, pa) <- cylModels ]
      ++ [ (na ++ " to " ++ nb ++ ": (c) f' = lambda x [<f(x), x>] one-one, B <=_1 C x N",
            let f x = if pa x then head (filter pb [0 ..]) else head (filter (not . pb) [0 ..])
                f' x = tau (f x) x
            in injective (map f' [0 .. 300]) && all (\x -> pa x == inTimesN pb (f' x)) [0 .. 300])
         | (na, pa) <- cylModels, (nb, pb) <- cylModels ]
      ++ [ (na ++ " to " ++ nb ++ ": (d) A x N <=_1 B x N via lambda z [<f(pi_1 z), z>], back to A <=m B",
            let f x = if pa x then head (filter pb [0 ..]) else head (filter (not . pb) [0 ..])
                big z = tau (f (pi1 z)) z
                back x = pi1 (big (tau x 0))
            in injective (map big [0 .. 300])
               && all (\z -> inTimesN pa z == inTimesN pb (big z)) [0 .. 300]
               && all (\x -> pa x == pb (back x)) [0 .. 300])
         | (na, pa) <- cylModels, (nb, pb) <- cylModels ] )

  group c "exercise 7-4: the degenerate case A = N, B = N - {0} (finite universes)"
    [ ("universe of size " ++ show n ++ ": no map reduces N - {0} to N",
       not (mRed n n [1 .. n - 1] [0 .. n - 1])) | n <- [1 .. 4] ]

  let pairs74 =
        [ ("2N and 2N - {0, 4} + {1, 7}", even, \x -> (even x && x `notElem` [0, 4]) || x `elem` [1, 7])
        , ("primes + {0} and primes - {2}", \x -> isPrime x || x == 0, \x -> isPrime x && x /= 2)
        , ("N - {3} and N - {5}", (/= 3), (/= 5))
        , ("N - {0} and N - {1, 2}", (/= 0), (`notElem` [1, 2])) ]
      red74 pa pb x
        | pa x && not (pb x) = head (filter pb [0 ..])
        | pb x && not (pa x) = head (filter (not . pb) [0 ..])
        | otherwise = x
  group c "exercise 7-4 as corrected: A, B infinite, different from N, finite difference"
    ( [ (name ++ ": A <=m B and B <=m A by the finite modification of the identity",
         all (\x -> pa x == pb (red74 pa pb x)) [0 .. 2000] && all (\x -> pb x == pa (red74 pb pa x)) [0 .. 2000])
      | (name, pa, pb) <- pairs74 ]
      ++ [ (name ++ ": the maps differ from the identity only on (A - B) union (B - A)",
            all (\x -> red74 pa pb x == x || pa x /= pb x) [0 .. 2000])
         | (name, pa, pb) <- pairs74 ] )

  group c "exercise 7-15 (b): phi(2x) = e(x), phi(2x + 1) = x, A = 2N"
    [ (name ++ ": phi(N) = N and phi(A) = Val e below 400",
       let e = filter p [0 ..]
           phi z = if even z then e !! fromInteger (z `div` 2) else z `div` 2
           img = map phi [0 .. 1200]
           imgA = [phi z | z <- [0, 2 .. 1200]]
       in all (`elem` img) [0 .. 400] && sort (nub (filter (<= 400) imgA)) == [x | x <- [0 .. 400], p x])
    | (name, p) <- [("e enumerates the primes", isPrime), ("e enumerates the squares", isSquare)] ]

  let n4 = 4
      sets4 = subsetsOf [0 .. n4 - 1]
      redI a b = any (\f -> and [maybe False (`elem` b) (f !! x) | x <- a]) (partialMaps n4 n4)
      redII a b = any (\f -> and [(x `elem` a) == maybe False (`elem` b) (f !! x) | x <- [0 .. n4 - 1]]) (partialMaps n4 n4)
      redIII a b = any (\f -> injective [v | Just v <- f]
                              && and [(x `elem` a) == maybe False (`elem` b) (f !! x) | x <- [0 .. n4 - 1]])
                       (partialMaps n4 n4)
  group c "exercise 7-16, the partial answer on the universe {0, ..., 3}"
    ( [ ("(i) A <= B iff A empty or B nonempty " ++ show (a, b), redI a b == (null a || not (null b)))
      | a <- sets4, b <- sets4 ]
      ++ [ ("(ii) A <= B iff A empty or B nonempty " ++ show (a, b), redII a b == (null a || not (null b)))
         | a <- sets4, b <- sets4 ]
      ++ [ ("(iii) A <= B iff |A| <= |B| " ++ show (a, b), redIII a b == (length a <= length b))
         | a <- sets4, b <- sets4 ] )

  group c "exercise 7-29 and the hint of 7-2: 2x <-> 2x + 1 maps A (+) A-bar onto its complement"
    [ (name, let s z = if even z then z + 1 else z - 1
                 inJ z = if even z then p (z `div` 2) else not (p (z `div` 2))
             in all (\z -> s (s z) == z) [0 .. 2000] && all (\z -> inJ z == not (inJ (s z))) [0 .. 2000])
    | (name, p) <- [("even", even), ("prime", isPrime), ("x mod 7 in {2, 3}", \x -> x `mod` 7 `elem` [2, 3])] ]

  finish c "ch05-07-reductions"
  where
    samples = take 400 (go 17)
    go seed = let rs = take 9 (tail (iterate (\s -> (s * 1103515245 + 12345) `mod` 2147483648) seed))
                  len = fromInteger (head rs `mod` 5)
                  ps = [(a `mod` 6, b `mod` 6) | (a, b) <- take len (zip (drop 1 rs) (drop 5 rs))]
              in ps : go (last rs)
