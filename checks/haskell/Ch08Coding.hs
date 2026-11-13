-- | Shared definitions of the checks of chapters 8-9 (CheckCh08*.hs,
-- CheckCh09*.hs), base only.
--
-- * The pairing function of § 5.3 (p. 89):
--   tau(x, y) = ((x + y)^2 + 3x + y) / 2, its inverses pi_1, pi_2, and the
--   n-tuples <x_1, ..., x_n> = tau^n(x_1, ..., x_n), nested to the left:
--   tau^(n+1)(x_1, ..., x_(n+1)) = tau(tau^n(x_1, ..., x_n), x_(n+1))
--   (p. 90).  A x B = tau(A cross B) (p. 90).
-- * Canonical indices (p. 98): D_u = {x | bit x of u is 1}, D_0 = empty.
-- * A (+) B = {2x | x in A} u {2x + 1 | x in B} (§ 7.6).
-- * Boolean functions and tt-conditions of § 8.3 (pp. 145-146): an n-ary
--   boolean function is kept as its truth table (bit sum_i w_i 2^(i-1) of
--   a mask); the tt-condition <<x_1, ..., x_n>, alpha> is satisfied on X
--   if alpha(c_X(x_1), ..., c_X(x_n)) = 1.
-- * A small deterministic pseudo-random generator (splitmix64) for the
--   random models; every run draws the same cases.
module Ch08Coding
  ( tau, untau, pi1, pi2, tauN, piN, isqrt
  , canon, dset
  , join, timesSet
  , BF (..), apply, assignments, allBF, fromFn, arity
  , TT (..), sat, order, assoc
  , Gen, mkGen, next, below, pick, shuffle, subsetOf, draws
  , subsetsOf, sortNub, arg
  ) where

import Data.Bits (shiftL, shiftR, testBit, xor)
import Data.List (nub, sort)
import Data.Word (Word64)

-- * Pairing (§ 5.3)

tau :: Integer -> Integer -> Integer
tau x y = (x + y) * (x + y + 1) `div` 2 + x

isqrt :: Integer -> Integer
isqrt n
  | n < 0 = error "isqrt"
  | n < 2 = n
  | otherwise = go n
  where
    go x = let y = (x + n `div` x) `div` 2 in if y >= x then x else go y

untau :: Integer -> (Integer, Integer)
untau z = (x, w - x)
  where
    w = (isqrt (8 * z + 1) - 1) `div` 2
    x = z - w * (w + 1) `div` 2

pi1, pi2 :: Integer -> Integer
pi1 = fst . untau
pi2 = snd . untau

tauN :: [Integer] -> Integer
tauN [] = error "tauN: n > 0"
tauN [x] = x
tauN xs = tau (tauN (init xs)) (last xs)

piN :: Int -> Integer -> [Integer]
piN n z
  | n <= 1 = [z]
  | otherwise = let (a, b) = untau z in piN (n - 1) a ++ [b]

-- * Canonical indices (p. 98)

canon :: [Integer] -> Integer
canon = sum . map (2 ^) . nub

dset :: Integer -> [Integer]
dset u = [toInteger i | i <- [0 .. bits u], testBit u i]
  where
    bits v = length (takeWhile (> 0) (iterate (`div` 2) v))

-- * Operations on sets given as predicates

join :: (Integer -> Bool) -> (Integer -> Bool) -> Integer -> Bool
join a b n = if even n then a (n `div` 2) else b (n `div` 2)

timesSet :: (Integer -> Bool) -> (Integer -> Bool) -> Integer -> Bool
timesSet a b z = let (x, y) = untau z in a x && b y

-- * Boolean functions and tt-conditions (§ 8.3)

-- | Arity and truth table.
data BF = BF Int Integer deriving (Eq, Show)

arity :: BF -> Int
arity (BF n _) = n

index :: [Bool] -> Int
index ws = sum [if w then 1 `shiftL` i else 0 | (i, w) <- zip [0 ..] ws]

apply :: BF -> [Bool] -> Bool
apply (BF n m) ws
  | length ws /= n = error "apply: arity"
  | otherwise = testBit m (index ws)

assignments :: Int -> [[Bool]]
assignments 0 = [[]]
assignments n = [w : ws | ws <- assignments (n - 1), w <- [False, True]]

allBF :: Int -> [BF]
allBF n = [BF n m | m <- [0 .. 2 ^ (2 ^ n :: Integer) - 1]]

fromFn :: Int -> ([Bool] -> Bool) -> BF
fromFn n f = BF n (sum [2 ^ index ws | ws <- assignments n, f ws])

data TT = TT [Integer] BF deriving (Eq, Show)

sat :: (Integer -> Bool) -> TT -> Bool
sat x (TT xs a) = apply a (map x xs)

order :: TT -> Int
order (TT xs _) = length xs

assoc :: TT -> [Integer]
assoc (TT xs _) = sortNub xs

-- * Pseudo-random models (splitmix64)

newtype Gen = Gen Word64

mkGen :: Word64 -> Gen
mkGen = Gen

next :: Gen -> (Word64, Gen)
next (Gen s) = (z3, Gen s')
  where
    s' = s + 0x9E3779B97F4A7C15
    z1 = (s' `xor` (s' `shiftR` 30)) * 0xBF58476D1CE4E5B9
    z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94D049BB133111EB
    z3 = z2 `xor` (z2 `shiftR` 31)

-- | A number in [0, n).
below :: Int -> Gen -> (Int, Gen)
below n g = let (w, g') = next g in (fromIntegral (w `mod` fromIntegral n), g')

pick :: [a] -> Gen -> (a, Gen)
pick xs g = let (i, g') = below (length xs) g in (xs !! i, g')

shuffle :: [a] -> Gen -> ([a], Gen)
shuffle [] g = ([], g)
shuffle xs g =
  let (i, g1) = below (length xs) g
      (front, back) = splitAt i xs
      (rest, g2) = shuffle (front ++ drop 1 back) g1
   in (case back ++ front of { (y : _) -> y : rest; [] -> rest }, g2)

-- | Each element kept with probability p / 100.
subsetOf :: Int -> [a] -> Gen -> ([a], Gen)
subsetOf _ [] g = ([], g)
subsetOf p (x : xs) g =
  let (r, g1) = below 100 g
      (rest, g2) = subsetOf p xs g1
   in (if r < p then x : rest else rest, g2)

-- | n independent draws.
draws :: Int -> (Gen -> (a, Gen)) -> Gen -> ([a], Gen)
draws 0 _ g = ([], g)
draws n f g = let (a, g1) = f g; (as, g2) = draws (n - 1) f g1 in (a : as, g2)

subsetsOf :: [a] -> [[a]]
subsetsOf [] = [[]]
subsetsOf (x : xs) = [ys | s <- subsetsOf xs, ys <- [s, x : s]]

sortNub :: Ord a => [a] -> [a]
sortNub = map head' . groupSorted . sort
  where
    head' (y : _) = y
    head' [] = error "sortNub"
    groupSorted [] = []
    groupSorted (y : ys) = let (s, r) = span (== y) ys in (y : s) : groupSorted r

-- | The i-th argument (from 1) of a boolean function; False if absent.
arg :: Int -> [Bool] -> Bool
arg i ws = case drop (i - 1) ws of
  (w : _) -> w
  [] -> False
