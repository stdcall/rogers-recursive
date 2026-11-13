-- | Checks of chapter 4 (pp. 73-80): the transformations of relations
-- by permutations and theorem II (p. 76) on finite sets, the examples
-- (i)-(iii) of pp. 75-76, theorem III (p. 78) on finite models, and the
-- hint of exercise 4-6 (p. 79).
--
-- Run: runghc -ichecks/haskell checks/haskell/CheckCh01Invariance.hs
--
-- Expected values: theorem II, psi = f(phi) as relations iff
-- phi = f^(-1) psi f (on the set {0, ..., n - 1}: all permutations f and
-- all partial functions phi, psi for n <= 3; for n = 4 all f, phi and
-- psi = f(phi)); property (i)
-- "contains 7" is not invariant, (ii) "has at least two elements" is,
-- and (iii) through c_(f(A)) = c_A f^(-1); theorem III: with
-- phi_x = lambda y [psi f(x, y)] and phi_(k(x)) = g phi_x, the function
-- eta = g^(-1) psi h satisfies phi_x = lambda y [eta f^(x, y)],
-- f^ = lambda x y [h^(-1) f(k(x), y)] (a finite family phi_x of partial
-- functions on {0, ..., n - 1} stands for the numbering); the hint of
-- exercise 4-6: h^(-1) g h (2m) = 2 f(m) + 1, so f is computable from
-- h^(-1) g h.
--
-- Not established: recursiveness (of f^(-1) in theorem I, of eta and f^
-- in theorem III, the non-recursiveness in exercise 4-6) - the checks
-- concern the set-theoretic identities only, on finite sets; theorems
-- II and III are proved in general in
-- checks/lean/RogersRecursive/Ch01_04Invariance.lean.
module Main (main) where

import Data.List (nub, permutations, sort)
import Data.Maybe (fromJust)

import Harness

type Perm = [Int]          -- f !! x = f(x) on {0, ..., n - 1}

type PFun = [Maybe Int]    -- psi !! x, Nothing = diverges

inv :: Perm -> Perm
inv f = [fromJust (lookup y (zip f [0 ..])) | y <- [0 .. length f - 1]]

-- | The image f(R) of a binary relation (p. 76).
imageRel :: Perm -> [(Int, Int)] -> [(Int, Int)]
imageRel f r = sort [(f !! x, f !! y) | (x, y) <- r]

graph :: PFun -> [(Int, Int)]
graph psi = [(x, y) | (x, Just y) <- zip [0 ..] psi]

-- | f^(-1) psi f.
conj :: Perm -> PFun -> PFun
conj f psi = [fmap (inv f !!) (psi !! (f !! x)) | x <- [0 .. length f - 1]]

allPFun :: Int -> [PFun]
allPFun n = mapM (const (Nothing : map Just [0 .. n - 1])) [1 .. n]

-- | Is the relation single-valued?
singleValued :: [(Int, Int)] -> Bool
singleValued r = length (nub (map fst r)) == length (nub r)

fromGraph :: Int -> [(Int, Int)] -> PFun
fromGraph n r = [lookup x r | x <- [0 .. n - 1]]

-- Theorem III on a finite model ----------------------------------------

-- | psi on codes 0 .. n*n - 1, f(x, y) = x n + y a coding of pairs: a
-- family phi_x = lambda y [psi f(x, y)], x < n, closed under g phi_x
-- when the family is closed (we close it by listing g^j phi_x).
theorem3 :: Int -> Perm -> Perm -> PFun -> Bool
theorem3 n g h base =
  and [ [eta (fhat x y) | y <- [0 .. n - 1]] == phi x | x <- [0 .. length family - 1] ]
  where
    -- the family: base and its images under powers of g
    family = take (orderOf g) (iterate (map (fmap (g !!))) base)
    phi x = family !! x
    m = length family
    -- psi on codes c = x n + y (x < m), with a permutation h of the codes
    psi c = phi (c `div` n) !! (c `mod` n)
    f x y = x * n + y
    k x = (x + 1) `mod` m                      -- phi_(k(x)) = g phi_x
    gInv = inv g
    hInv = inv h
    eta c = fmap (gInv !!) (psi (h !! c))      -- eta = g^(-1) psi h
    fhat x y = hInv !! f (k x) y               -- f^ = h^(-1) f(k(x), y)

orderOf :: Perm -> Int
orderOf g = 1 + length (takeWhile (/= [0 .. length g - 1]) (iterate (map (g !!)) g))

-- | A permutation of {0, ..., size - 1} from a seed (Fisher-Yates with
-- a linear congruential generator).
randomPerm :: Int -> Integer -> Perm
randomPerm size seed = go [0 .. size - 1] seed []
  where
    go [] _ acc = acc
    go xs s acc =
      let s' = (6364136223846793005 * s + 1442695040888963407) `mod` (2 ^ (64 :: Int))
          i = fromInteger ((s' `div` 65536) `mod` toInteger (length xs))
      in go (take i xs ++ drop (i + 1) xs) s' (xs !! i : acc)

-- Exercise 4-6 ------------------------------------------------------------

-- | f a permutation of N moving only numbers below m (given on [0 .. m-1]).
ext :: Perm -> Int -> Int
ext f x = if x < length f then f !! x else x

extInv :: Perm -> Int -> Int
extInv f = ext (inv f)

hOf :: Perm -> Int -> Int
hOf f x = if odd x then x else 2 * ext f (x `div` 2)

hInvOf :: Perm -> Int -> Int
hInvOf f x = if odd x then x else 2 * extInv f (x `div` 2)

gEx :: Int -> Int
gEx x = if even x then x + 1 else x - 1

conjEx :: Perm -> Int -> Int
conjEx f = hInvOf f . gEx . hOf f

main :: IO ()
main = do
  c <- newCounter
  group c "theorem II (p. 76): psi = f(phi) iff phi = f^(-1) psi f, n <= 3"
    [ ("n = " ++ show n ++ ", f = " ++ show f ++ ", phi = " ++ show phi,
       let psi' = imageRel f (graph phi)
       in singleValued psi'
            && conj f (fromGraph n psi') == phi
            && and [ (sort (graph psi) == psi') == (conj f psi == phi) | psi <- allPFun n ])
    | n <- [1 .. 3], f <- permutations [0 .. n - 1], phi <- allPFun n ]
  group c "theorem II, n = 4 (only psi = f(phi) and its conjugate)"
    [ ("f = " ++ show f ++ ", phi = " ++ show phi,
       let psi' = imageRel f (graph phi)
       in singleValued psi' && conj f (fromGraph 4 psi') == phi)
    | f <- permutations [0 .. 3], phi <- allPFun 4 ]
  group c "p. 75, (i)-(iii): invariance of the examples"
    ( [ ("(i) the permutation (0 7) maps {7} to {0}",
         let f = [7, 1, 2, 3, 4, 5, 6, 0] in sort [f !! x | x <- [7]] == [0]) ]
      ++ [ ("(ii) " ++ show a ++ " under " ++ show f,
            (length a >= 2) == (length (nub [f !! x | x <- a]) >= 2))
         | f <- permutations [0 .. 4], a <- subsets [0 .. 4] ]
      ++ [ ("(iii) c_(f(A)) = c_A f^(-1) for " ++ show a,
            and [ (y `elem` [f !! x | x <- a]) == ((inv f !! y) `elem` a) | y <- [0 .. 4] ])
         | f <- permutations [0 .. 4], a <- subsets [0 .. 4] ] )
  group c "theorem III (p. 78) on finite models: phi_x = lambda y [eta f^(x, y)]"
    [ ("n = " ++ show n ++ ", seed " ++ show sd,
       theorem3 n g h base)
    | n <- [3, 4, 5], sd <- [1 .. 40]
    , let g = randomPerm n sd
    , let base = [if (fromInteger sd * 7 + y) `mod` 3 == 0 then Nothing else Just ((y * 5 + fromInteger sd) `mod` n) | y <- [0 .. n - 1]]
    , let m = orderOf g
    , let h = randomPerm (m * n) (sd + 1000) ]
  group c "exercise 4-6: h^(-1) g h (2m) = 2 f(m) + 1"
    ( [ ("seed " ++ show sd ++ ", m = " ++ show m,
         conjEx f (2 * m) == 2 * ext f m + 1
           && conjEx f (2 * m + 1) == 2 * extInv f m
           && (conjEx f (2 * m) - 1) `div` 2 == ext f m)
      | sd <- [1 .. 30], let f = randomPerm 25 sd, m <- [0 .. 40] ]
      ++ [ ("seed " ++ show sd ++ ": h, h^(-1) g h permutations of [0 .. 59]",
            sort (map (hOf f) [0 .. 59]) == [0 .. 59] && sort (map (conjEx f) [0 .. 59]) == [0 .. 59])
         | sd <- [1 .. 30], let f = randomPerm 25 sd ] )
  finish c "ch01-04-invariance"
  where
    subsets [] = [[]]
    subsets (x : xs) = let r = subsets xs in r ++ map (x :) r

