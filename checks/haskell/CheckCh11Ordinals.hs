-- | Checks of chapter 11, §§ 11.7-11.9 (printed pp. 263-285): ordinal
-- notations on finite parts, the corrections of theorems XV, XXI and of
-- corollary XVIII (b), +_O, and the ordinal arithmetic of exercises 11-50,
-- 11-53.  Scope ch10-12.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh11Ordinals.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh11Ordinals.hs
--      [--verbose]
--
-- Ordinals below epsilon_0 are written in Cantor normal form
-- omega^(b_1) c_1 + ... + omega^(b_k) c_k (exercise 11-52 (b)), with +, x
-- and exponentiation computed by the usual normal-form rules.  An "index
-- of a function" of a notation system is modelled by the function itself.
--
-- What is checked, and where the expectations come from:
--
-- * Exercise 11-50 (p. 283): (a) the four rules on 4000 random triples
--   below omega^(omega^2) (with alpha^(n + 1) = alpha^n alpha as a check
--   of the exponentiation); (b) 1 + omega /= omega + 1, 2 omega /= omega 2,
--   (1 + 1) omega /= omega + omega; (c) alpha = omega alpha for alpha =
--   omega^omega (and for 0), not for omega^k c, k finite.  Exercise 11-53
--   (b): omega + omega^2 = omega^2 and omega + beta /= beta below omega^2;
--   omega omega^omega = omega^omega, and 0 is also a fixed point of lambda
--   beta [omega beta]; (c): omega^beta > beta for beta < epsilon_0
--   (samples).
-- * th:related-system-extension (theorem XV, pp. 265-266) on the
--   recursively related system S of the ordinals below alpha = omega 3
--   (code 3b + a for omega a + b): S' with nu, k, p, q as printed and q of
--   2y the sequence 2 phi_(q_S(y)) (corrected): k, p, q give the type,
--   the predecessor and increasing sequences cofinal in the limit
--   (bounded tests) for all notations <= 300; psi of the proof is total,
--   increasing and cofinal in omega 3; R_S' as printed (with "&" for the
--   comma of [x = 1, y = 1]) is the order of S' on notations <= 80.  The
--   printed 2 phi_(q_(S')(y)) gives for x = 2 (nu = omega) a sequence
--   reaching omega 2.
-- * corollary XVIII (b) (ii) (p. 271): for a univalent S with nu(0) = 1,
--   nu(1) = 0 and phi into O, nu_S(x) < nu_S(y) <=> phi(x) <_O phi(y)
--   (corrected) holds, the printed x < y <=> phi(x) <_O phi(y) fails.
-- * theorem XVII (+_O, pp. 269-270) on notations of O below omega^2 + 2
--   (two notations of omega, omega + k, omega 2, omega^2): x +_O y is a
--   notation (sequences increasing in <_O, values increasing and cofinal
--   in |x| + |y|), and y /= 1 => x <_O x +_O y; the remarks of p. 269:
--   |x| < |y| does not give x <_O y, and the notations above two
--   notations of omega are incomparable.
-- * theorem XXI (Parikh, pp. 273-274), the successor case, on the finite
--   notations 1, 2, 2^2, 2^(2^2), ... of O, with psi(D) = the canonical
--   index of the finite set D (one-one, in place of a productive
--   function) and S_(n + 1) = S_n u {psi(D) | D subset S_n} (exercise
--   7-46): with phi'(2^x) = psi(phi'(W_f(2^x))) (corrected) phi'(z) is in
--   S_(|z| + 1) - S_|z| for |z| <= 5; the printed phi'(W_f(x)) gives
--   phi'(2) = phi'(1), in S_1.
--
-- Not established: the theorems for systems in general, limit cases of
-- theorem XXI, universality (theorems XVI, XVIII), constructivity; tests of
-- cofinality are bounded.
module Main (main) where

import Data.Bits (shiftR, testBit, xor)
import Data.List (nub)
import Data.Word (Word64)

import Harness

------------------------------------------------------------------------
-- Ordinals below epsilon_0 in Cantor normal form

newtype Ord0 = O [(Ord0, Integer)] deriving Eq

instance Ord Ord0 where
  compare (O xs) (O ys) = go xs ys
    where
      go [] [] = EQ
      go [] _ = LT
      go _ [] = GT
      go ((a, c) : r) ((b, d) : s) = case compare a b of
        EQ -> case compare c d of
          EQ -> go r s
          o -> o
        o -> o

instance Show Ord0 where
  show (O []) = "0"
  show (O ts) = foldr1 (\a b -> a ++ " + " ++ b) (map term ts)
    where
      term (e, c)
        | e == zero = show c
        | otherwise = "w^(" ++ show e ++ ")" ++ (if c == 1 then "" else " " ++ show c)

zero, one, omega :: Ord0
zero = O []
one = fin 1
omega = O [(one, 1)]

fin :: Integer -> Ord0
fin 0 = zero
fin n = O [(zero, n)]

wPow :: Ord0 -> Ord0
wPow e = O [(e, 1)]

add :: Ord0 -> Ord0 -> Ord0
add a (O []) = a
add (O as) (O ((e, c) : bs)) =
  let higher = [t | t@(e', _) <- as, e' > e]
      same = sum [c' | (e', c') <- as, e' == e]
  in O (higher ++ [(e, same + c)] ++ bs)

mul :: Ord0 -> Ord0 -> Ord0
mul (O []) _ = zero
mul _ (O []) = zero
mul (O ((a1, c1) : rest)) (O bs) = foldl add zero (map term bs)
  where
    term (b, d)
      | b == zero = O ((a1, c1 * d) : rest)
      | otherwise = O [(add a1 b, d)]

-- | The unique b' with 1 + b' = b (b > 0).
minusOneLeft :: Ord0 -> Ord0
minusOneLeft b@(O ts) = case ts of
  [(e, c)] | e == zero -> fin (c - 1)
  _ -> b

isFinite :: Ord0 -> Bool
isFinite (O ts) = all ((== zero) . fst) ts

finValue :: Ord0 -> Integer
finValue (O []) = 0
finValue (O ts) = sum (map snd ts)

power :: Ord0 -> Ord0 -> Ord0
power _ (O []) = one
power (O []) _ = zero
power a _ | a == one = one
power a (O bs) = foldl mul one [ powN (powW b) d | (b, d) <- bs ]
  where
    powN x d = foldl mul one (replicate (fromIntegral d) x)
    -- a^(omega^b)
    powW b
      | b == zero = a
      | isFinite a = wPow (wPow (minusOneLeft b))
      | otherwise = let O ((a1, _) : _) = a in wPow (mul a1 (wPow b))

-- | 0, successor or limit.
kind :: Ord0 -> Int
kind (O []) = 0
kind (O ts) = if fst (last ts) == zero then 1 else 2

------------------------------------------------------------------------
-- Random ordinals

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

-- | Ordinals below omega^(omega^2): exponents omega a + b, a, b <= 2.
randomOrd :: Gen -> (Ord0, Gen)
randomOrd g0 =
  let (k, g1) = below 4 g0
      (ts, g2) = terms k g1
  in (foldl add zero (map (\(e, c) -> O [(e, c)]) (descending ts)), g2)
  where
    terms 0 g = ([], g)
    terms k g = let (a, h1) = below 3 g; (b, h2) = below 3 h1; (c, h3) = below 3 h2
                    (r, h4) = terms (k - 1 :: Int) h3
                in ((add (mul omega (fin (fromIntegral a))) (fin (fromIntegral b)), fromIntegral c + 1) : r, h4)
    descending = foldr insert []
    insert t [] = [t]
    insert t@(e, _) (u@(f, _) : r) = if e >= f then t : u : r else u : insert t r

arithmeticChecks :: [(String, Bool)]
arithmeticChecks =
  concat [ let (a, g1) = randomOrd (Gen (fromIntegral (5100 + i)))
               (b, g2) = randomOrd g1
               (c, _) = randomOrd g2
               small x = O (take 2 (let O ts = x in ts))
               (a', b', c') = (small a, small b, small c)
           in [ ("(a + b) + c = a + (b + c) " ++ show (a, b, c), add (add a b) c == add a (add b c))
              , ("a (b + c) = a b + a c", mul a (add b c) == add (mul a b) (mul a c))
              , ("(a b) c = a (b c)", mul (mul a b) c == mul a (mul b c))
              , ("a^(b + c) = a^b a^c " ++ show (a', b', c'), power a' (add b' c') == mul (power a' b') (power a' c'))
              , ("(a^b)^c = a^(b c)", power (power a' b') c' == power a' (mul b' c'))
              , ("a^(n + 1) = a^n a, n <= 3", and [power a (fin (n + 1)) == mul (power a (fin n)) a | n <- [0 .. 3]]) ]
         | i <- [1 .. 4000 :: Int] ]
  ++ [ ("2^(omega + 1) = omega 2, 2^omega = omega", power (fin 2) (add omega one) == mul omega (fin 2) && power (fin 2) omega == omega)
     , ("(omega + 1)^2 = omega^2 + omega + 1", power (add omega one) (fin 2) == add (add (wPow (fin 2)) omega) one)
     , ("(b) 1 + omega = omega /= omega + 1", add one omega == omega && add omega one /= omega)
     , ("(b) 2 omega = omega /= omega 2", mul (fin 2) omega == omega && mul omega (fin 2) /= omega)
     , ("(b) (1 + 1) omega = omega /= 1 omega + 1 omega", mul (add one one) omega == omega && add omega omega /= omega)
     , ("(c) omega omega^omega = omega^omega", mul omega (wPow omega) == wPow omega)
     , ("(c) omega 0 = 0", mul omega zero == zero)
     , ("(c) omega alpha /= alpha for alpha = omega^k c, k <= 6, c <= 4",
        and [mul omega x /= x | k <- [0 .. 6], c <- [1 .. 4], let x = O [(fin k, c)]])
     , ("11-53 (b) (i): omega + omega^2 = omega^2", add omega (wPow (fin 2)) == wPow (fin 2))
     , ("11-53 (b) (i): omega + beta /= beta for beta = omega a + b < omega^2, a, b <= 20",
        and [add omega x /= x | a <- [0 .. 20], b <- [0 .. 20], let x = add (mul omega (fin a)) (fin b)])
     , ("11-53 (b) (ii): omega^omega and 0 are fixed points of lambda beta [omega beta]",
        mul omega (wPow omega) == wPow omega && mul omega zero == zero)
     , ("11-53 (b) (ii): omega beta /= beta for 0 < beta < omega^omega (omega^k c + ..., samples)",
        and [mul omega x /= x | k <- [0 .. 5], c <- [1 .. 3], r <- [0 .. 3], let x = add (O [(fin k, c)]) (fin r), k > 0 || c > 0])
     , ("11-53 (c): omega^beta > beta for 400 random beta", and [wPow b > b | i <- [1 .. 400 :: Int], let (b, _) = randomOrd (Gen (fromIntegral (7300 + i)))]) ]

------------------------------------------------------------------------
-- Theorem XV: S below omega 3 and its extension S'

-- | S: the code 3b + a denotes omega a + b, a < 3.
nuS :: Integer -> Ord0
nuS x = add (mul omega (fin (x `mod` 3))) (fin (x `div` 3))

kS :: Integer -> Integer
kS x = if x == 0 then 0 else if x `div` 3 > 0 then 1 else 2

pS :: Integer -> Integer
pS x = x - 3

qS :: Integer -> (Integer -> Integer)
qS x n = 3 * n + (x `mod` 3 - 1)

alpha :: Ord0
alpha = mul omega (fin 3)

inDS' :: Integer -> Bool
inDS' x = x == 1 || (x >= 0 && even x)

nuS' :: Integer -> Ord0
nuS' 1 = alpha
nuS' x = nuS (x `div` 2)

kS' :: Integer -> Integer
kS' 1 = 2
kS' x = kS (x `div` 2)

pS' :: Integer -> Integer
pS' x = 2 * pS (x `div` 2)

-- | psi of the proof: psi(0) = the notation of 0, psi(j + 1) = the least u
-- with nu_S(u) > nu_S(psi(j)).
psiSeq :: [Integer]
psiSeq = iterate (\p -> head [u | u <- [0 ..], nuS u > nuS p]) 0

-- | q_S'; the corrected and the printed first line.
qS' :: Bool -> Integer -> Maybe (Integer -> Integer)
qS' _ 1 = Just (\n -> 2 * (psiSeq !! fromIntegral n))
qS' corrected x
  | even x && kS (x `div` 2) == 2 =
      if corrected then Just (\n -> 2 * qS (x `div` 2) n)
      else fmap (\s n -> 2 * s n) (qS' False (x `div` 2))
  | otherwise = Nothing

-- | Increasing, below the limit and cofinal (each test ordinal below the
-- limit is reached within 300 terms).
fundamental :: (Integer -> Ord0) -> Ord0 -> [Ord0] -> Bool
fundamental vals lim tests =
  and (zipWith (<) vs (drop 1 vs)) && all (< lim) vs
  && and [any (>= t) (map vals [0 .. 300]) | t <- tests, t < lim]
  where vs = map vals [0 .. 40]

testOrdinals :: [Ord0]
testOrdinals = [add (mul omega (fin a)) (fin b) | a <- [0 .. 2], b <- [0, 1, 7, 25]]

theoremXVChecks :: [(String, Bool)]
theoremXVChecks =
  [ ("S': k, p, q at x = " ++ show x,
     case kS' x of
       0 -> nuS' x == zero
       1 -> kind (nuS' x) == 1 && inDS' (pS' x) && add (nuS' (pS' x)) one == nuS' x
       _ -> kind (nuS' x) == 2 && maybe False (\s -> all (inDS' . s) [0 .. 40]
                                   && fundamental (nuS' . s) (nuS' x) testOrdinals) (qS' True x))
  | x <- [0 .. 300], inDS' x ]
  ++ [ ("psi is increasing and cofinal in omega 3", fundamental (\n -> nuS (psiSeq !! fromIntegral n)) alpha testOrdinals)
     , ("psi begins 0, 1, 2, 5, 8 (omega, omega 2, omega 2 + 1, ...)", take 5 psiSeq == [0, 1, 2, 5, 8])
     , ("R_S' as printed is the order of S' on notations <= 80",
        and [ rS' x y == (nuS' x <= nuS' y) | x <- [1 .. 80], inDS' x, y <- [1 .. 80], inDS' y ])
     , ("printed q_S'(2) = 2 phi_(q_S'(1)): the sequence reaches omega 2 > nu_S'(2) = omega",
        nuS' 2 == omega && maybe False (\s -> any (\n -> nuS' (s n) >= nuS' 2) [0 .. 5]) (qS' False 2))
     , ("printed q_S'(4) = 2 phi_(q_S'(2)) is not a fundamental sequence of omega 2",
        maybe True (\s -> not (fundamental (nuS' . s) (nuS' 4) testOrdinals)) (qS' False 4)) ]
  where
    rS' x y
      | even x && even y = nuS (x `div` 2) <= nuS (y `div` 2)
      | even x && y == 1 = True
      | x == 1 && y == 1 = True
      | otherwise = False

------------------------------------------------------------------------
-- O on a finite part, +_O

-- | A notation of O: 1, 2^x, or 3 5^y with phi_y given (its name and its
-- intended limit).
data N = One | Two N | Lim String Ord0 (Integer -> N)

nameN :: N -> String
nameN One = "1"
nameN (Two x) = "2^" ++ nameN x
nameN (Lim s _ _) = s

sameN :: N -> N -> Bool
sameN a b = nameN a == nameN b

absN :: N -> Ord0
absN One = zero
absN (Two x) = add (absN x) one
absN (Lim _ o _) = o

-- | z <_O y (the search in a sequence goes to 25 terms).
lessO :: N -> N -> Bool
lessO _ One = False
lessO z (Two x) = sameN z x || lessO z x
lessO z (Lim _ _ s) = any (\n -> sameN z (s n) || lessO z (s n)) [0 .. 25]

plusO :: N -> N -> N
plusO x One = x
plusO x (Two u) = Two (plusO x u)
plusO x (Lim s o f) = Lim (nameN x ++ "+(" ++ s ++ ")") (add (absN x) o) (\n -> plusO x (f n))

finN :: Integer -> N
finN 0 = One
finN k = Two (finN (k - 1))

omegaA, omegaB, omega2, omegaSq :: N
omegaA = Lim "wA" omega finN
omegaB = Lim "wB" omega (\n -> finN (2 * n + 1))
omega2 = plusO omegaA omegaA
omegaSq = Lim "wSq" (wPow (fin 2)) (\n -> timesW (n + 1))

-- | omega k as omega (k - 1) +_O omega.
timesW :: Integer -> N
timesW 1 = omegaA
timesW k = plusO (timesW (k - 1)) omegaA

-- | A notation of O, tested to the given depth: sequences increasing in
-- <_O and in value, cofinal in the limit (bounded).
validO :: Int -> N -> Bool
validO _ One = True
validO d (Two x) = d <= 0 || validO (d - 1) x
validO d (Lim _ o f) =
  and [lessO (f i) (f j) | i <- [0 .. 3], j <- [i + 1 .. 4]]
  && fundamental (absN . f) o tests
  && (d <= 0 || all (validO (d - 1) . f) [0 .. 3])
  where tests = [t | t <- [add (mul omega (fin a)) (fin b) | a <- [0 .. 3], b <- [0, 3, 9]] ++ [add (wPow (fin 2)) (fin 2)], t < o]

notations :: [N]
notations = [One, finN 1, finN 3, omegaA, omegaB, Two omegaA, omega2, Two omega2, omegaSq, Two (Two omegaSq)]

plusOChecks :: [(String, Bool)]
plusOChecks =
  concat [ [ (nameN x ++ " +_O " ++ nameN y ++ ": a notation of O", validO 2 s)
           , (nameN x ++ " +_O " ++ nameN y ++ ": |x +_O y| = |x| + |y|", absN s == add (absN x) (absN y))
           , (nameN x ++ " +_O " ++ nameN y ++ ": y /= 1 => x <_O x +_O y", sameN y One || lessO x s) ]
         | x <- take 8 notations, y <- notations, let s = plusO x y ]
  ++ [ ("the test notations are notations of O", all (validO 2) notations)
     , ("|wB| < |2^wA| but not wB <_O 2^wA", absN omegaB < absN (Two omegaA) && not (lessO omegaB (Two omegaA)))
     , ("wA <_O 2^wA; 2^wA and wB are incomparable",
        lessO omegaA (Two omegaA) && not (lessO (Two omegaA) omegaB) && not (lessO omegaB (Two omegaA)))
     , ("1 <_O 2 <_O 2^2 <_O ... <_O wA", and [lessO (finN i) (finN (i + 1)) && lessO (finN i) omegaA | i <- [0 .. 10]]) ]

------------------------------------------------------------------------
-- Corollary XVIII (b) (ii)

corollaryChecks :: [(String, Bool)]
corollaryChecks =
  [ ("corrected (ii): nu_S(x) < nu_S(y) <=> phi(x) <_O phi(y), x, y in {0, 1}",
     and [ (nu x < nu y) == lessO (ph x) (ph y) | x <- [0, 1], y <- [0, 1] ])
  , ("(i): nu_S(x) = |phi(x)|_O", and [nu x == absN (ph x) | x <- [0, 1]])
  , ("printed (ii) fails: 0 < 1 but not phi(0) <_O phi(1)", 0 < (1 :: Integer) && not (lessO (ph 0) (ph 1))) ]
  where
    nu :: Integer -> Ord0
    nu x = if x == 0 then one else zero
    ph x = if x == 0 then finN 1 else One

------------------------------------------------------------------------
-- Theorem XXI (Parikh), the successor case on finite notations

-- | psi(D) = the canonical index of D; D_x is the set with index x.
setOf :: Integer -> [Integer]
setOf x = [i | i <- [0 .. bits x - 1], testBit x (fromIntegral i)]
  where bits k = fromIntegral (length (takeWhile (> 0) (iterate (`shiftR` 1) k)))

psiD :: [Integer] -> Integer
psiD = sum . map (2 ^) . nub

-- | x in S_j: S_0 = 0, S_(j + 1) = S_j u {psi(D) | D subset S_j}.
inS :: Int -> Integer -> Bool
inS 0 _ = False
inS j x = all (inS (j - 1)) (setOf x)

-- | phi' on the notation 1, 2, 2^2, ... of k (|.| = k); the predecessors
-- of the notation of k are those of 0, ..., k - 1.
phiCorrected, phiPrinted :: Int -> Integer
phiCorrected k = psiD [phiCorrected i | i <- [0 .. k - 1]]
phiPrinted 0 = psiD []
phiPrinted k = psiD [phiPrinted i | i <- [0 .. k - 2]]    -- phi'(W_f(x)) for 2^x

parikhChecks :: [(String, Bool)]
parikhChecks =
  [ ("corrected: phi'(z) in S_(|z| + 1) - S_|z|, |z| = " ++ show k,
     inS (k + 1) (phiCorrected k) && not (inS k (phiCorrected k)))
  | k <- [0 .. 5] ]
  ++ [ ("corrected phi' is one-one on |z| <= 5", length (nub (map phiCorrected [0 .. 5])) == 6)
     , ("phi'(1), phi'(2), phi'(2^2), phi'(2^(2^2)) = 0, 1, 3, 11", map phiCorrected [0 .. 3] == [0, 1, 3, 11])
     , ("printed: phi'(2) = phi'(1) = psi(0), in S_1, not in S_2 - S_1",
        phiPrinted 1 == phiPrinted 0 && inS 1 (phiPrinted 1)) ]

main :: IO ()
main = do
  c <- newCounter
  group c "11.9 ex. 11-50, 11-53: ordinal arithmetic" arithmeticChecks
  group c "11.7 Th. XV: S' on a system below omega 3" theoremXVChecks
  group c "11.7 Th. XVII: +_O on notations below omega^2 + 2" plusOChecks
  group c "11.7 Cor. XVIII (b) (ii)" corollaryChecks
  group c "11.8 Th. XXI (Parikh), successor case" parikhChecks
  finish c "ch11-ordinals"
