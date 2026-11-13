-- | Checks of chapter 11, §§ 11.1-11.6 (printed pp. 232-263): the
-- constructions of the recursion theorem run on a toy numbering, the
-- weak recursion theorem on finite universes, the recursion equations (E)
-- and the sequences of the footnotes.  Scope ch10-12.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh11Recursion.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh11Recursion.hs
--      [--verbose]
--
-- The toy numbering.  A program is an expression in one input (Var) with
-- constants, +, -, x, the pairing <x, y> of § 5.3 with its inverses,
-- IfZ, App (a b) = phi_a(b) (the universal function), Undef (nowhere
-- defined), Pad y x (the program x with y as padding: phi_t(x, y) =
-- phi_x), Smn a b = s(a, b) = the code of lambda x [phi_a(<b, x>)] (the
-- s-m-n function), Mk (a code built from the codes of its parts).  The
-- code of a program is its prefix token string written in base 16 (one
-- token a digit, a leading 1 as end mark); every number is the code of a
-- program (unreadable numbers code Undef).  phi_c(x) is the evaluation
-- with a fuel bound on App and Pad; the checks require a result within
-- the bound (no check passes on exhausted fuel).
--
-- What is checked, and where the expectations come from:
--
-- * th:fixed-point (p. 233): g~(u) = s(G, u) with phi_G(<u, x>) =
--   phi_(phi_u(u))(x), v a code of f g~, n = g~(v); phi_n = phi_f(n) on
--   inputs 0..8 for five total f, among them f(x) = code of lambda y [x]
--   (phi_n(y) = n: a program printing its own code) and the example of
--   p. 234, W_f(x) = {x} (W_n = {n}: phi_n(n) = 0, divergent at 0..12,
--   n - 1, n + 1); th:fixed-point-uniform (p. 234): n(z) = g~ v~(z) is
--   computed by a program, phi_n(z) = phi_(phi_z(n(z))).
-- * th:fixed-point-parameters (p. 235): g~(u, x) = s(G_2, <u, x>),
--   n_f(x) = g~(v, x) for three f of two variables, x <= 4.
-- * th:recursion-theorem (Kleene, pp. 235-236): with the padding t, g~~,
--   v~~ and n = lambda z x y [g~~(t(v~~(z), y), x)] as printed, the fixed
--   point property for three z, x, y <= 2; n is one-one on z (three
--   codes), x, y <= 3 because the v~~ here (the code of a fixed program
--   with z as a constant) is one-one; with v~~'(z) = v~~(z with its
--   padding removed), also a code of the required function, n is not
--   one-one: n(t(z, 0), x, y) = n(z, x, y) (the gap of the printed proof;
--   one-one v~~ is required, see the correction of p. 236).
-- * th:double-recursion (Smullyan, p. 246): m, n built as in the proof;
--   two programs printing each other's codes, and exercise
--   ex:mutual-membership: m /= n, W_m = {n}, W_n = {m}.
-- * th:descending-chain (theorem VII, pp. 240-241), with t(f(x, y), y) for f'(x, y)
--   (a code > y of the same program): g = phi_n total on 0..3, g(y) > y,
--   W_g(y) = {g g(y)}; m_0, m_1, m_2 distinct, W_(m_i) = {m_(i + 1)}.
-- * th:fixed-point-not-minimal (pp. 253-254): f = phi_m is the identity
--   off n(m), f(n(m)) = t (an index of lambda y [0]), phi_n(m) =
--   lambda y [0].
-- * th:enumeration-operator-fixed-point (pp. 249-250): for 3000 random
--   enumeration operators on {0, ..., 5} (finite axiom sets), A_0 = 0,
--   A_(n+1) = Phi(A_n) increases to A with Phi(A) = A and A subset B for
--   every fixed point B (all 64 subsets); Phi is monotone.
-- * § 11.5, the example (E), (E*) (p. 255): the least fixed point of the
--   operator of (E*), computed by iteration on 0..2048, is psi^ (2x on
--   powers of 2, divergent elsewhere); psi^ and lambda x [2x] satisfy
--   (E); the footnote of p. 256: the least fixed point of its operator is
--   lambda x [x] on 2, 4, 8, ..., lambda x [x] satisfies the equations but
--   is not a fixed point.
-- * The footnote of p. 259: x_(2n) = n^2, x_(2n+1) = x_n begins 0, 0, 1,
--   0, 4, 1, 9, 0, 16, 4, 25, 1, with the printed rows of
--   subsequences.
--
-- Not established: that the toy numbering is acceptable (it has no
-- unbounded search), the theorems for the numbering of the book; only the
-- printed constructions on the listed instances and inputs.
module Main (main) where

import Data.Bits (shiftL, shiftR, xor, (.&.))
import Data.List (foldl', nub, subsequences)
import Data.Word (Word64)

import Harness

------------------------------------------------------------------------
-- Pairing (§ 5.3): <x, y> = ((x + y)^2 + 3x + y) / 2

pairN :: Integer -> Integer -> Integer
pairN x y = ((x + y) * (x + y) + 3 * x + y) `div` 2

isqrt :: Integer -> Integer
isqrt n
  | n < 2 = n
  | otherwise = go (1 `shiftL` ((bitLength n + 1) `div` 2))   -- >= sqrt n
  where
    go x = let y = (x + n `div` x) `div` 2 in if y >= x then x else go y

unpairN :: Integer -> (Integer, Integer)
unpairN z =
  let w = (isqrt (8 * z + 1) - 1) `div` 2
      t = w * (w + 1) `div` 2
      x0 = z - t
  in (x0, w - x0)

------------------------------------------------------------------------
-- The toy programs and their codes

data E
  = Var | Const Integer | Suc E | Prd E | Add E E | Sub E E | Mul E E
  | Pr E E | P1 E | P2 E | IfZ E E E | App E E | Undef | Pad Integer Integer
  | Smn E E | Mk Int [E] | Hole E

-- | The number of bits of k > 0.
bitLength :: Integer -> Int
bitLength k = search 1
  where
    search e = if k `shiftR` e == 0 then bisect (e `div` 2) e else search (2 * e)
    -- k >= 2^lo / 2, k < 2^hi
    bisect lo hi
      | hi - lo <= 1 = hi
      | otherwise = let mid = (lo + hi) `div` 2 in
          if k `shiftR` mid == 0 then bisect lo mid else bisect mid hi

-- | Digits in base 2^b, least significant first, no leading zeros
-- (split in halves: the codes reach some 10^5 digits).
digitsPow2 :: Int -> Integer -> [Int]
digitsPow2 _ 0 = []
digitsPow2 b k0 = go k0 ((bitLength k0 + b - 1) `div` b)
  where
    mask = (1 `shiftL` b) - 1
    go k n
      | n <= 32 = [fromIntegral ((k `shiftR` (b * i)) .&. mask) | i <- [0 .. n - 1]]
      | otherwise =
          let h = n `div` 2
          in go (k .&. ((1 `shiftL` (b * h)) - 1)) h ++ go (k `shiftR` (b * h)) (n - h)

fromDigitsPow2 :: Int -> [Int] -> Integer
fromDigitsPow2 b ds0 = go ds0 (length ds0)
  where
    go ds n
      | n <= 32 = foldr (\d acc -> fromIntegral d + (acc `shiftL` b)) 0 ds
      | otherwise =
          let h = n `div` 2
              (l, r) = splitAt h ds
          in go l h + (go r (n - h) `shiftL` (b * h))

natToks :: Integer -> [Int]
natToks n = map (+ 1) (digitsPow2 3 n) ++ [0]

toks :: E -> [Int]
toks e = case e of
  Var -> [0]
  Const n -> 1 : natToks n
  Suc a -> 2 : toks a
  Prd a -> 3 : toks a
  Add a b -> 4 : toks a ++ toks b
  Sub a b -> 5 : toks a ++ toks b
  Mul a b -> 6 : toks a ++ toks b
  Pr a b -> 7 : toks a ++ toks b
  P1 a -> 8 : toks a
  P2 a -> 9 : toks a
  IfZ a b c -> 10 : toks a ++ toks b ++ toks c
  App a b -> 11 : toks a ++ toks b
  Undef -> [12]
  Pad y x -> 13 : natToks y ++ natToks x
  Smn a b -> 14 : toks a ++ toks b
  Mk k es -> 15 : natToks (fromIntegral k) ++ concatMap toks es
  Hole _ -> error "a hole has no code"

fromToks :: [Int] -> Integer
fromToks ts = fromDigitsPow2 4 (ts ++ [1])

code :: E -> Integer
code = fromToks . toks

-- | The tokens of a code (without the end mark), if it has one.
toToks :: Integer -> Maybe [Int]
toToks c
  | c <= 0 = Nothing
  | otherwise = case reverse (digitsPow2 4 c) of
      (1 : rest) -> Just (reverse rest)
      _ -> Nothing

arity :: Int -> Maybe Int
arity k
  | k `elem` [0, 12] = Just 0
  | k `elem` [1, 2, 3, 8, 9] = Just 1
  | k `elem` [4, 5, 6, 7, 11, 13, 14] = Just 2
  | k == 10 = Just 3
  | otherwise = Nothing

parseE :: [Int] -> Maybe (E, [Int])
parseE [] = Nothing
parseE (t : ts) = case t of
  0 -> Just (Var, ts)
  1 -> do (n, r) <- nat ts; Just (Const n, r)
  2 -> one Suc
  3 -> one Prd
  4 -> two Add
  5 -> two Sub
  6 -> two Mul
  7 -> two Pr
  8 -> one P1
  9 -> one P2
  10 -> do (a, r1) <- parseE ts; (b, r2) <- parseE r1; (c, r3) <- parseE r2; Just (IfZ a b c, r3)
  11 -> two App
  12 -> Just (Undef, ts)
  13 -> do (y, r1) <- nat ts; (x, r2) <- nat r1; Just (Pad y x, r2)
  14 -> two Smn
  15 -> do (k, r1) <- nat ts
           a <- arity (fromIntegral k)
           (es, r2) <- many a r1
           Just (Mk (fromIntegral k) es, r2)
  _ -> Nothing
  where
    one f = do (a, r) <- parseE ts; Just (f a, r)
    two f = do (a, r1) <- parseE ts; (b, r2) <- parseE r1; Just (f a b, r2)
    many 0 r = Just ([], r)
    many k r = do (e, r1) <- parseE r; (es, r2) <- many (k - 1 :: Int) r1; Just (e : es, r2)

nat :: [Int] -> Maybe (Integer, [Int])
nat ts = case break (== 0) ts of
  (ds, 0 : r) | all (\d -> d >= 1 && d <= 8) ds -> Just (fromDigitsPow2 3 (map (subtract 1) ds), r)
  _ -> Nothing

decode :: Integer -> E
decode c = case toToks c >>= parseE of
  Just (e, []) -> e
  _ -> Undef

-- | s(e, u): the code of lambda x [phi_e(<u, x>)].
smn :: Integer -> Integer -> Integer
smn e u = code (App (Const e) (Pr (Const u) Var))

-- | t(x, y): a code of the program x padded with y.
tPad :: Integer -> Integer -> Integer
tPad x y = code (Pad y x)

data R = V Integer | Div | Out deriving (Eq, Show)

eval :: Int -> E -> Integer -> R
eval fuel e x = case e of
  Var -> V x
  Const n -> V n
  Suc a -> un (+ 1) a
  Prd a -> un (\v -> max 0 (v - 1)) a
  Add a b -> bin (+) a b
  Sub a b -> bin (\p q -> max 0 (p - q)) a b
  Mul a b -> bin (*) a b
  Pr a b -> bin pairN a b
  P1 a -> un (fst . unpairN) a
  P2 a -> un (snd . unpairN) a
  IfZ a b c -> case ev a of
    V 0 -> ev b
    V _ -> ev c
    r -> r
  App a b -> case (ev a, ev b) of
    (V c, V v) -> call c v
    (V _, r) -> r
    (r, _) -> r
  Undef -> Div
  Pad _ c -> call c x
  Smn a b -> bin smn a b
  Mk k es -> case mapM ev' es of
    Right vs -> V (build k vs)
    Left r -> r
  Hole _ -> Div
  where
    ev a = eval fuel a x
    ev' a = case ev a of V v -> Right v; r -> Left r
    un f a = case ev a of V v -> V (f v); r -> r
    bin f a b = case (ev a, ev b) of
      (V p, V q) -> V (f p q)
      (V _, r) -> r
      (r, _) -> r
    call c v = if fuel <= 0 then Out else eval (fuel - 1) (decode c) v
    build 1 [v] = code (Const v)
    build 13 [y, c] = code (Pad y c)
    build k vs = fromToks (k : concatMap (\v -> maybe [12] id (toToks v)) vs)

phi :: Integer -> Integer -> R
phi c = eval 60 (decode c)

-- | phi_a and phi_b agree (with results within the fuel) on the inputs.
sameOn :: [Integer] -> Integer -> Integer -> Bool
sameOn xs a b = all (\x -> let r = phi a x in r /= Out && r == phi b x) xs

value :: R -> Integer
value (V v) = v
value r = error ("no value: " ++ show r)

-- | The code of a template (an expression with holes) as an expression:
-- a hole is filled with Const (its value).
quote :: E -> E
quote e = case e of
  Hole a -> Mk 1 [a]
  Var -> Mk 0 []
  Undef -> Mk 12 []
  Const n -> Mk 1 [Const n]
  Pad y c -> Mk 13 [Const y, Const c]
  Suc a -> Mk 2 [quote a]
  Prd a -> Mk 3 [quote a]
  Add a b -> Mk 4 [quote a, quote b]
  Sub a b -> Mk 5 [quote a, quote b]
  Mul a b -> Mk 6 [quote a, quote b]
  Pr a b -> Mk 7 [quote a, quote b]
  P1 a -> Mk 8 [quote a]
  P2 a -> Mk 9 [quote a]
  IfZ a b c -> Mk 10 [quote a, quote b, quote c]
  App a b -> Mk 11 [quote a, quote b]
  Smn a b -> Mk 14 [quote a, quote b]
  Mk _ _ -> error "no quoting of Mk"

-- | 0 iff a = b.
eqE :: E -> E -> E
eqE a b = Add (Sub a b) (Sub b a)

------------------------------------------------------------------------
-- The constructions of §§ 11.2, 11.4

-- | G: phi_G(<u, x>) = phi_(phi_u(u))(x); g~(u) = s(G, u).
bigG :: Integer
bigG = code (App (App (P1 Var) (P1 Var)) (P2 Var))

gTilde :: Integer -> Integer
gTilde = smn bigG

-- | A code of f g~ for the program f; the fixed point g~(v) (theorem I)
-- and n(z) = g~ v~(z) (theorem II) are the same formula.
vOf :: Integer -> Integer
vOf f = code (App (Const f) (Smn (Const bigG) Var))

fixedPoint :: Integer -> Integer
fixedPoint f = gTilde (vOf f)

-- | The program computing n(z) of theorem II.
nExpr :: E
nExpr = Smn (Const bigG) (quote (App (Hole Var) (Smn (Const bigG) Var)))

nProgram :: Integer
nProgram = code nExpr

fQuine, fSingleton, fSucc, fAddConst, fTwice :: Integer
fQuine = code (Mk 1 [Var])                                      -- code of lambda y [x]
fSingleton = code (quote (IfZ (eqE Var (Hole Var)) (Const 0) Undef))  -- W_f(x) = {x}
fSucc = code (Suc Var)                                          -- f(x) = x + 1
fAddConst = code (quote (Add Var (Hole Var)))                   -- code of lambda y [y + x]
fTwice = code (quote (Mul (Const 2) (Hole Var)))                -- code of lambda y [2x]

theoremIChecks :: [(String, Bool)]
theoremIChecks =
  concat [ [ (name ++ ": phi_v is total, phi_v(v) = f(g~(v))",
              phi (vOf f) (vOf f) == phi f (gTilde (vOf f)))
           , (name ++ ": phi_n = phi_f(n) on 0..8",
              let n = fixedPoint f in sameOn [0 .. 8] n (value (phi f n)))
           , (name ++ ": theorem II, the program for n(z) computes n(f)",
              phi nProgram f == V (fixedPoint f)) ]
         | (name, f) <- [ ("quine", fQuine), ("singleton", fSingleton), ("x + 1", fSucc)
                        , ("y + x", fAddConst), ("2x", fTwice) ] ]
  ++ [ ("a program printing its own code: phi_n(y) = n",
        let n = fixedPoint fQuine in all (\y -> phi n y == V n) [0 .. 6])
     , ("example of p. 234: W_n = {n}",
        let n = fixedPoint fSingleton
        in phi n n == V 0 && all (\y -> phi n y == Div) ([0 .. 12] ++ [n - 1, n + 1]))
     , ("phi_n(y) = y + n for f(x) = code of lambda y [y + x]",
        let n = fixedPoint fAddConst in all (\y -> phi n y == V (y + n)) [0 .. 6])
     , ("phi_n = phi_(n + 1) for f(x) = x + 1 (both nowhere defined here)",
        let n = fixedPoint fSucc in all (\y -> phi n y == Div && phi (n + 1) y == Div) [0 .. 4]) ]

------------------------------------------------------------------------
-- Theorem III: one parameter

bigG2 :: Integer
bigG2 = code (App (App (P1 (P1 Var)) (P1 Var)) (P2 Var))   -- phi(<<u, x>, y>) = phi_(phi_u(<u, x>))(y)

gTilde2 :: Integer -> Integer -> Integer
gTilde2 u x = smn bigG2 (pairN u x)

v3 :: Integer -> Integer
v3 f2 = code (App (Const f2) (Pr (Smn (Const bigG2) Var) (P2 Var)))

nF :: Integer -> Integer -> Integer
nF f2 x = gTilde2 (v3 f2) x

f2Shift, f2Const, f2Point :: Integer
f2Shift = code (quote (Add Var (Hole (P2 Var))))               -- f(a, x) = code of lambda y [y + x]
f2Const = code (Mk 1 [Add (P1 Var) (P2 Var)])                  -- f(a, x) = code of lambda y [a + x]
f2Point = code (quote (IfZ (eqE Var (Hole (P2 Var))) (Hole (P1 Var)) Undef))  -- y = x -> a

theoremIIIChecks :: [(String, Bool)]
theoremIIIChecks =
  [ (name ++ ", x = " ++ show x ++ ": phi_(n_f(x)) = phi_(f(n_f(x), x))",
     let n = nF f2 x in sameOn [0 .. 6] n (value (phi f2 (pairN n x))))
  | (name, f2) <- [("shift", f2Shift), ("const", f2Const), ("point", f2Point)], x <- [0 .. 4] ]
  ++ [ ("const: phi_(n_f(x))(y) = n_f(x) + x",
        all (\x -> let n = nF f2Const x in all (\y -> phi n y == V (n + x)) [0 .. 3]) [0 .. 4])
     , ("point: phi_(n_f(x)) is defined exactly at x, with the value n_f(x)",
        all (\x -> let n = nF f2Point x in all (\y -> phi n y == (if y == x then V n else Div)) [0 .. 6]) [0 .. 4]) ]

------------------------------------------------------------------------
-- Theorem IV (Kleene)

-- | g~~(u, x) = t(g~(u, x), <u, x>), as an expression of <u, x>.
ggtExpr :: E
ggtExpr = Mk 13 [Var, Smn (Const bigG2) Var]

ggt :: Integer -> Integer -> Integer
ggt u x = tPad (gTilde2 u x) (pairN u x)

-- | v~~(z): a code of lambda u x [phi_z(g~~(u, x), x)] (z a constant of
-- a fixed program: one-one in z).
vv :: Integer -> Integer
vv z = code (App (Const z) (Pr ggtExpr (P2 Var)))

kleeneN :: (Integer -> Integer) -> Integer -> Integer -> Integer -> Integer
kleeneN vvF z x y = ggt (tPad (vvF z) y) x

-- | Total functions of two variables (as programs of <a, x>).
zs :: [Integer]
zs = [f2Const, code (quote (Mul Var (Hole (Suc (P2 Var))))), f2Shift]

-- | The code with its padding removed.
canon :: Integer -> Integer
canon c = case decode c of
  Pad _ c' -> canon c'
  _ -> c

theoremIVChecks :: [(String, Bool)]
theoremIVChecks =
  [ ("z = " ++ show i ++ ", x = " ++ show x ++ ", y = " ++ show y ++ ": phi_n = phi_(phi_z(n, x))",
     let n = kleeneN vv z x y in sameOn [0 .. 4] n (value (phi z (pairN n x))))
  | (i, z) <- zip [0 :: Int ..] zs, x <- [0 .. 2], y <- [0 .. 2] ]
  ++ [ ("g~~ is one-one on u, x <= 5", let vs = [ggt u x | u <- [0 .. 5], x <- [0 .. 5]] in length (nub vs) == length vs)
     , ("t is one-one on x, y <= 5 and phi_t(x, y) = phi_x",
        let vs = [tPad c y | c <- zs, y <- [0 .. 5]] in length (nub vs) == length vs
          && and [sameOn [0 .. 4] (tPad c y) c | c <- zs, y <- [0 .. 2]])
     , ("v~~ (a constant in a fixed program) is one-one on the codes used",
        let vs = map vv (zs ++ map (`tPad` 0) zs) in length (nub vs) == length vs)
     , ("n is one-one on z (three codes), x, y <= 3",
        let vs = [kleeneN vv z x y | z <- zs, x <- [0 .. 3], y <- [0 .. 3]] in length (nub vs) == length vs)
     , ("v~~'(z) = v~~(z without padding) is a code of the same function as v~~(z)",
        and [ sameOn [pairN u x | u <- [0 .. 2], x <- [0 .. 2]] (vv (canon z')) (vv z')
            | z <- zs, let z' = tPad z 0 ])
     , ("with v~~' the function n is not one-one: n(t(z, 0), x, y) = n(z, x, y)",
        and [ kleeneN (vv . canon) (tPad z 0) x y == kleeneN (vv . canon) z x y && tPad z 0 /= z
            | z <- zs, x <- [0 .. 1], y <- [0 .. 1] ])
     , ("with v~~' the fixed point property still holds",
        and [ let n = kleeneN (vv . canon) (tPad z 0) x 0 in sameOn [0 .. 3] n (value (phi (tPad z 0) (pairN n x)))
            | z <- zs, x <- [0 .. 1] ]) ]

------------------------------------------------------------------------
-- Theorem X (a) (Smullyan), exercise ex:mutual-membership

doubleRec :: Integer -> Integer -> (Integer, Integer)
doubleRec gP hP =
  let v = v3 gP
      mHat y = gTilde2 v y
      kProg = code (App (Const hP) (Pr (Smn (Const bigG2) (Pr (Const v) Var)) Var))
      nHat = fixedPoint kProg
  in (mHat nHat, nHat)

doubleChecks :: [(String, Bool)]
doubleChecks =
  [ ("phi_m = phi_g(<m, n>) and phi_n = phi_h(<m, n>), " ++ name,
     sameOn [0 .. 5] m (value (phi gP (pairN m n))) && sameOn [0 .. 5] n (value (phi hP (pairN m n))))
  | (name, gP, hP) <- cases, let (m, n) = doubleRec gP hP ]
  ++ [ ("two programs printing each other's codes",
        let (m, n) = doubleRec (code (Mk 1 [P2 Var])) (code (Mk 1 [P1 Var]))
        in m /= n && all (\y -> phi m y == V n && phi n y == V m) [0 .. 4])
     , ("exercise: m /= n, W_m = {n}, W_n = {m}",
        let (m, n) = doubleRec pointG pointH
        in m /= n && phi m n == V 0 && phi n m == V 0
           && all (\y -> phi m y == Div) ([0 .. 10] ++ [m, n - 1, n + 1])
           && all (\y -> phi n y == Div) ([0 .. 10] ++ [n, m - 1, m + 1])) ]
  where
    pointG = code (quote (IfZ (eqE Var (Hole (P2 Var))) (Const 0) Undef))
    pointH = code (quote (IfZ (eqE Var (Hole (P1 Var))) (Const 0) Undef))
    cases = [ ("constants", code (Mk 1 [P2 Var]), code (Mk 1 [P1 Var]))
            , ("points", pointG, pointH)
            , ("shifts", code (quote (Add Var (Hole (P2 Var)))), code (quote (Add Var (Hole (P1 Var))))) ]

------------------------------------------------------------------------
-- Theorem VII: a descending chain W_(m_i) = {m_(i + 1)}

-- | f'(x, y) = t(f(x, y), y), f(x, y) a code of lambda w [0 if w =
-- phi_x phi_x(y), divergent otherwise].
fPrime :: Integer
fPrime = code (Mk 13 [P2 Var, quote template])
  where
    d = App (Hole (P1 Var)) (App (Hole (P1 Var)) (Hole (P2 Var)))
    template = IfZ (eqE Var d) (Const 0) Undef

chainChecks :: [(String, Bool)]
chainChecks =
  [ ("g(y) is defined and g(y) > y, y <= 3", all (\y -> case g y of V v -> v > y; _ -> False) [0 .. 3])
  , ("W_g(y) = {g g(y)}, y <= 2",
     all (\y -> let gy = value (g y); ggy = value (g gy)
                in phi gy ggy == V 0 && all (\w -> phi gy w == Div) ([0 .. 6] ++ [ggy - 1, ggy + 1])) [0 .. 2])
  , ("m_0, m_1, m_2 distinct, W_(m_0) = {m_1}, W_(m_1) = {m_2}",
     let m0 = value (g 0); m1 = value (g m0); m2 = value (g m1)
     in length (nub [m0, m1, m2]) == 3 && phi m0 m1 == V 0 && phi m1 m2 == V 0
        && phi m0 m2 == Div && phi m1 m0 == Div) ]
  where
    hP = code (Smn (Const fPrime) Var)       -- phi_h(x)(y) = f'(x, y)
    n = fixedPoint hP
    g = phi n

------------------------------------------------------------------------
-- Theorem XIII: the fixed point of theorem II need not be minimal

notMinimalChecks :: [(String, Bool)]
notMinimalChecks =
  [ ("f(x) = x for x /= n(m), x <= 10", all (\x -> x == nm || phi m x == V x) [0 .. 10])
  , ("f(n(m)) = t", phi m nm == V t0)
  , ("phi_t = lambda y [0] and phi_n(m) = lambda y [0]", all (\y -> phi t0 y == V 0 && phi nm y == V 0) [0 .. 4])
  , ("phi_f(x) = phi_x for x = n(m) and x <= 4", sameOn [0 .. 3] (value (phi m nm)) nm
       && and [sameOn [0 .. 3] (value (phi m x)) x | x <- [0 .. 4], x /= nm]) ]
  where
    t0 = code (Const 0)
    psiT = IfZ (eqE Var (Hole nExpr)) (Const t0) Var
    hP = code (quote psiT)
    m = fixedPoint hP
    nm = fixedPoint m

------------------------------------------------------------------------
-- Theorem XI on finite universes

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

type Op = [(Int, [Int])]

applyOp :: Op -> [Int] -> [Int]
applyOp w b = nub [x | (x, d) <- w, all (`elem` b) d]

subsetL :: [Int] -> [Int] -> Bool
subsetL a b = all (`elem` b) a

sameSet :: [Int] -> [Int] -> Bool
sameSet a b = subsetL a b && subsetL b a

randomOpW :: Int -> Op
randomOpW s =
  let g0 = Gen (fromIntegral (64000 + s))
      (k, g1) = below 8 g0
      (w, _) = draws (k + 1) ax g1
  in w
  where
    ax g = let (x, h1) = below 6 g; (dk, h2) = below 3 h1; (d, h3) = draws dk (below 6) h2
           in ((x, nub d), h3)

weakChecks :: [(String, Bool)]
weakChecks = concatMap one [1 .. 3000]
  where
    one s =
      let w = randomOpW s
          as = take 8 (iterate (applyOp w) [])
          a = last as
          fixed = [b | b <- subsequences [0 .. 5], sameSet (applyOp w b) b]
      in [ ("op " ++ show s ++ ": A_0 subset A_1 subset ...", and (zipWith subsetL as (drop 1 as)))
         , ("op " ++ show s ++ ": Phi(A) = A", sameSet (applyOp w a) a)
         , ("op " ++ show s ++ ": A is contained in every fixed point", all (subsetL a) fixed)
         , ("op " ++ show s ++ ": monotone", and [ subsetL (applyOp w b) (applyOp w c)
                                                 | b <- subsequences [0 .. 3], c <- subsequences [0 .. 3], subsetL b c ]) ]

------------------------------------------------------------------------
-- Example (E), (E*) and the footnotes of pp. 256, 259

type PF = [(Integer, Integer)]   -- a finite function: (argument, value)

-- | The least fixed point on 0..bound by iteration from the empty function.
lfp :: (PF -> Integer -> Maybe Integer) -> Integer -> PF
lfp op bound = go []
  where
    go f = let f' = [(y, v) | y <- [0 .. bound], Just v <- [op f y]] in if f' == f then f else go f'

-- | (E*): psi(1) = 2, psi(2x) = 2 phi(x).
opE :: PF -> Integer -> Maybe Integer
opE f y
  | y == 1 = Just 2
  | even y = fmap (2 *) (lookup (y `div` 2) f)
  | otherwise = Nothing

-- | The operator of the footnote of p. 256: 2 at 2, 2 phi(z) at 2z for z
-- even, divergent otherwise.
opF :: PF -> Integer -> Maybe Integer
opF f y
  | y == 2 = Just 2
  | even y && even (y `div` 2) = fmap (2 *) (lookup (y `div` 2) f)
  | otherwise = Nothing

isPow2 :: Integer -> Bool
isPow2 y = y >= 1 && y .&. (y - 1) == 0

-- | (E) holds for a partial function on 0..bound (Kleene equality).
satisfiesE :: (Integer -> Maybe Integer) -> Integer -> Bool
satisfiesE p bound = p 1 == Just 2 && and [ p (2 * x) == fmap (2 *) (p x) | x <- [0 .. bound `div` 2] ]

equationChecks :: [(String, Bool)]
equationChecks =
  [ ("the least fixed point of (E*) is psi^ on 0..2048", lfpE == [(y, 2 * y) | y <- [0 .. 2048], isPow2 y])
  , ("psi^ satisfies (E)", satisfiesE (`lookup` lfpE) 2048)
  , ("lambda x [2x] satisfies (E)", satisfiesE (\x -> Just (2 * x)) 2048)
  , ("lambda x [2x] is not a fixed point of (E*) (divergent at odd y /= 1)", opE [(y, 2 * y) | y <- [0 .. 2048]] 3 == Nothing)
  , ("footnote of p. 256: the least fixed point is lambda x [x] on 2, 4, 8, ...", lfpF == [(y, y) | y <- [2 .. 2048], isPow2 y])
  , ("footnote: lambda x [x] satisfies psi(4x) = 2 psi(2x), psi(2) = 2",
     and [4 * x == 2 * (2 * x) | x <- [0 .. 500 :: Integer]])
  , ("footnote: lambda x [x] is not a fixed point (divergent at 1, 6, ...)",
     let ident = [(y, y) | y <- [0 .. 2048]] in opF ident 1 == Nothing && opF ident 6 == Nothing)
  , ("footnote: the least fixed point satisfies the equations",
     lookup 2 lfpF == Just 2 && and [lookup (4 * x) lfpF == fmap (2 *) (lookup (2 * x) lfpF) | x <- [0 .. 511]]) ]
  where
    lfpE = lfp opE 2048
    lfpF = lfp opF 2048

sequenceChecks :: [(String, Bool)]
sequenceChecks =
  [ ("x_0, ..., x_11 = 0, 0, 1, 0, 4, 1, 9, 0, 16, 4, 25, 1", take 12 xsq == [0, 0, 1, 0, 4, 1, 9, 0, 16, 4, 25, 1])
  , ("row 2 (odd places): 0, 0, 1, 0, 4, 1", [xsq !! i | i <- [1, 3 .. 11]] == [0, 0, 1, 0, 4, 1])
  , ("row 3 (places 3, 7, 11): 0, 0, 1", [xsq !! i | i <- [3, 7, 11]] == [0, 0, 1])
  , ("row 4 (place 7): 0", xsq !! 7 == 0)
  , ("the odd places repeat the sequence (n <= 1000)", and [xsq !! (2 * n + 1) == xsq !! n | n <- [0 .. 1000]]) ]
  where
    xsq = map x [0 :: Int ..]
    x i = if even i then fromIntegral (i `div` 2) ^ (2 :: Int) else x (i `div` 2) :: Integer

-- | The toy numbering itself: pairing, codes, s-m-n, padding.
numberingChecks :: [(String, Bool)]
numberingChecks =
  [ ("<x, y> is a bijection on x, y <= 40 with its inverse",
     and [unpairN (pairN x y) == (x, y) | x <- [0 .. 40], y <- [0 .. 40]]
     && and [pairN (fst (unpairN z)) (snd (unpairN z)) == z | z <- [0 .. 2000]])
  , ("<x, y> on big numbers", and [unpairN (pairN x y) == (x, y) | x <- bigs, y <- bigs])
  , ("decode (code e) has the code of e",
     and [code (decode (code e)) == code e | e <- samples])
  , ("phi_s(e, u)(x) = phi_e(<u, x>)",
     and [phi (smn e u) x == phi e (pairN u x) | e <- [f2Const, f2Shift, bigG2], u <- [0 .. 3], x <- [0 .. 3]])
  , ("unreadable numbers are codes of the nowhere defined function",
     all (\c -> phi c 0 == Div) [0, 2, 17, 255]) ]
  where
    bigs = [0, 1, 7, 10 ^ (40 :: Int) + 3, 2 ^ (300 :: Int) - 1]
    samples = [Var, Const 12345, Add Var (Const 7), IfZ Var Undef (Pad 3 99), Mk 13 [Var, Const 2], Smn (Const 5) Var]

main :: IO ()
main = do
  c <- newCounter
  group c "11.2 the toy numbering" numberingChecks
  group c "11.2 Th. I, II: fixed points in the toy numbering" theoremIChecks
  group c "11.2 Th. III: one parameter" theoremIIIChecks
  group c "11.2 Th. IV (Kleene): fixed points and one-one n" theoremIVChecks
  group c "11.4 Th. X (a) (Smullyan), ex. mutual membership" doubleChecks
  group c "11.4 Th. VII: descending chain" chainChecks
  group c "11.5 Th. XIII: a fixed point that is not minimal" notMinimalChecks
  group c "11.5 Th. XI on finite universes" weakChecks
  group c "11.5 the equations (E), (E*) and the footnote of p. 256" equationChecks
  group c "11.6 the sequence of the footnote of p. 259" sequenceChecks
  finish c "ch11-recursion"
