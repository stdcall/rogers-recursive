-- | Checks of the finite-extension constructions of chapter 13, §§ 13.1-13.4
-- (printed pp. 326-354).  Scope ch13-14.
--
-- Run: ghc -O1 -ichecks/haskell checks/haskell/CheckCh13Constructions.hs, or
--      runghc -ichecks/haskell checks/haskell/CheckCh13Constructions.hs [--verbose]
--
-- The oracle computations phi_z^[f] are model families of finite question
-- trees (Ch13Oracle): every "check whether an extension exists" of the
-- book is decided by walking the tree, so each construction can be run
-- for a bounded number of stages.  Expected values come from the printed
-- statements (pages and our labels):
--
-- * p. 332-333 (pg:segment-notation): phi_z^[f](x) = y implies
--   phi_z^[g](x) = y for every g extending f; a computation defined on f
--   gives the same value on every total extension of f.
-- * th:mutually-not-re-relative (pp. 333-334): after stage 2n + 1,
--   x_m in A <=> x_m not in W_n^g for every total g extending the
--   segments built; after stage 2n + 2 the same with f, g exchanged.
-- * lem:incomparable-with-sequence (pp. 334-335), with model sets A_y and
--   n = <y, z>: stage 2n + 1 gives f(x_m) /= phi_z^(A_y)(x_m); stage
--   2n + 2 either gives x with phi_z^f(x) defined and /= c_(A_y)(x) for
--   every total f extending f_(m+1), or (no such extension) every value
--   phi_z^[f~](u) on an extension of f_m agrees with c_(A_y)(u) (the set
--   E of p. 335 is inside c_(A_y)), on the inputs of the model.  The step
--   "E = c_(A_y), so c_(A_y) is recursive" is not modelled.  The stages
--   of th:incomparable-below-jump (p. 337) are the same with one set A.
-- * th:double-jump-sets (pp. 339-340), the function psi (exercise
--   ex:k-jump-partial-function): on model enumerations of K and of
--   W_(rho(z_0)), with "the quadruples that have appeared in W_(rho(z_0))
--   by the w-th step" (cumulative reading), x in K' <=> psi(w) is
--   undefined for some w.  With "the quadruples that appear exactly at
--   the w-th step" the equivalence fails: a model where the only
--   quadruple of x appears before the element of its D_u enters K.
-- * th:jump-inversion (pp. 341-342): the stages n + 1 give
--   {n | an extension was found at stage n + 1} = {x | phi_x^f(x) is
--   defined} (= (tau(f))'), and g(n) is the last value of f_(n+1); from
--   f and the searches one rebuilds the segments and g (part (ii)).
-- * th:spector-jump-join (pp. 343-344), with f_0 = g_0 = empty (as
--   corrected; printed "f_0 = g_0 /= empty"): f_m and g_m have the same
--   length; every stage adds exactly one point x with f(x) /= g(x); with
--   x_0 < x_1 < ... these points, {x | phi_x^f(x) converges} =
--   {n | f(x_(2n)) = 1} (p. 344) and {x | phi_x^g(x) converges} =
--   {n | g(x_(2n+1)) = 1}.  The same holds when the run starts from any
--   common nonempty f_0 = g_0 (the printed condition does not refute the
--   proof; it does not define the segments).
-- * th:non-re-below-zero-jump (pp. 345-346), with model characteristic
--   functions c_x and n = <x, y, z> = tau^3(x, y, z): substage (c) finds
--   g^0, g^1 that differ at a point w, and f_(n+1) gives
--   phi_y^[f_(n+1)](w) /= c_x(w); after (a) or (b), f_(n+1) is not inside
--   phi_z^(c_x), or no extension F of f_(n+1) has phi_y^F = c_x on the
--   points used.  So c_x /= phi_y^f or f /= phi_z^(c_x) for every
--   triple processed.
-- * th:rational-chain-degrees (pp. 351-352), parts 2-3: s_x is an
--   increasing map of N onto N - {x}, f^((x)) is f with the x-th section
--   cut out; for the first 400 rationals r_0, r_1, ... (all rationals in
--   lowest terms), r <= s <=> {n | r_n < r} subset {n | r_n < s} on these
--   codes; {n | r_n < r} keeps growing with the list (so g_r one-one is
--   possible).
--
-- Not established: recursiveness or relative recursiveness of the
-- constructions, the halting-problem oracles, the theorems themselves;
-- the models are finite and check the stated stage steps on the stated
-- ranges only.
module Main (main) where

import Ch08Coding (below, mkGen, piN, sortNub, tau, untau)
import Ch13Oracle
import Data.Maybe (isJust, isNothing)
import Data.Ratio ((%))
import Data.Word (Word64)
import Harness

main :: IO ()
main = do
  c <- newCounter
  group c "pp. 332-333 phi^[f] and its extensions" monotoneChecks
  group c "th:mutually-not-re-relative stages 2n + 1, 2n + 2" thIVChecks
  group c "lem:incomparable-with-sequence stages" lemmaVChecks
  group c "th:double-jump-sets psi (cumulative reading)" psiChecks
  group c "th:jump-inversion stages and decoding" thIXChecks
  group c "th:spector-jump-join (f_0 = g_0 = empty)" thXChecks
  group c "th:non-re-below-zero-jump substages (a)-(c)" thXIChecks
  group c "th:rational-chain-degrees parts 2-3" rationalChecks
  finish c "ch13-constructions"

-- * Model sets

-- | A model 0/1 function on [0, 600) (the sets A_y, the functions c_x, g).
bits :: Word64 -> Int -> Int -> Int
bits seed i p = fst (below 2 (mkGen (seed * 2654435761 + fromIntegral i * 104729 + fromIntegral p)))

-- * pp. 332-333

monotoneChecks :: [(String, Bool)]
monotoneChecks =
  [ ( "phi^[f](x) = " ++ show y ++ " stays on every extension, z = " ++ show z ++ ", x = " ++ show x
    , all (\e -> evalSeg comp (f ++ e) == Just y) exts && definedOnAll comp f == Just y )
  | z <- [0 .. 30 :: Int], x <- [0 .. 12 :: Int]
  , let comp = family 11 z x
  , f <- [take k (map (bits 5 (z + x)) [0 ..]) | k <- [0, 3, 6, 9, 12, 18]]
  , Just y <- [evalSeg comp f]
  , let exts = [replicate k v | k <- [1, 5, 20], v <- [0, 1]]
  ]
    ++ [ ( "no extension defined => undefined on all total extensions, z = " ++ show z ++ ", x = " ++ show x
         , undefinedOnAll comp f )
       | z <- [0 .. 30 :: Int], x <- [0 .. 12 :: Int]
       , let comp = family 11 z x
       , f <- [take k (map (bits 6 (z + x)) [0 ..]) | k <- [0, 4, 8, 16]]
       , isNothing (firstExt comp f)
       ]
    ++ [ ( "the first extension extends f and gives a defined value, z = " ++ show z
         , isPrefixOf' f e && isJust (evalSeg comp e) )
       | z <- [0 .. 30 :: Int], x <- [0 .. 12 :: Int]
       , let comp = family 11 z x
       , f <- [take k (map (bits 7 (z + x)) [0 ..]) | k <- [0, 4, 8]]
       , Just e <- [firstExt comp f]
       ]

-- * th:mutually-not-re-relative

-- | (stage is odd (2n + 1), n, x_m, an extension was found)
type Rec = (Bool, Int, Int, Bool)

thIV :: Word64 -> Int -> (Seg, Seg, [Rec])
thIV seed s = go 0 [] [] []
  where
    go st f g recs
      | st == s = (f, g, reverse recs)
      | even st =
          let n = st `div` 2
              xm = length f
           in case firstExt (family seed n xm) g of
                Just g' -> go (st + 1) (f ++ [0]) g' ((True, n, xm, True) : recs)
                Nothing -> go (st + 1) (f ++ [1]) g ((True, n, xm, False) : recs)
      | otherwise =
          let n = st `div` 2
              xm = length g
           in case firstExt (family seed n xm) f of
                Just f' -> go (st + 1) f' (g ++ [0]) ((False, n, xm, True) : recs)
                Nothing -> go (st + 1) f (g ++ [1]) ((False, n, xm, False) : recs)

thIVChecks :: [(String, Bool)]
thIVChecks =
  concat
    [ [ ( "seed " ++ show seed ++ ", stage for n = " ++ show n ++ (if odd' then " (A)" else " (B)")
        , let (own, other) = if odd' then (fN, gN) else (gN, fN)
              comp = family seed n xm
              inSet = drop xm own `startsWith` 1
              inW = isJust (definedOnAll comp other)
              outW = undefinedOnAll comp other
           in (inSet == not yes) && (if yes then inW else outW) )
      | (odd', n, xm, yes) <- recs
      ]
      ++ [ ("seed " ++ show seed ++ ": both answers occur", any yesOf recs && any (not . yesOf) recs) ]
    | seed <- [1 .. 12]
    , let (fN, gN, recs) = thIV seed 40
    ]
  where
    yesOf (_, _, _, y) = y

startsWith :: [Int] -> Int -> Bool
startsWith (v : _) w = v == w
startsWith [] _ = False

-- * lem:incomparable-with-sequence

-- | The model inputs of the lemma: x < 40.
inputsV :: [Int]
inputsV = [0 .. 39]

data RecV = Diag Int Int Int | Found Int Int Int Integer | NoExt Int Int Seg

-- | The computations phi_z^[.](x) of the lemma's model: for z = 3 mod 4 a
-- computation that asks nothing and outputs c_(A_y)(x) or loops (so that
-- the answer "no" of stage 2n + 2 occurs), otherwise the family.
compV :: Word64 -> Int -> Int -> Int -> Comp
compV seed y z x
  | z `mod` 4 == 3 = if bits (seed + 150) z x == 0 then Loop else Out (toInteger (bits (seed + 100) y x))
  | otherwise = family seed z x

lemmaV :: Word64 -> Int -> (Seg, [RecV])
lemmaV seed s = go 0 [] []
  where
    aSet y = bits (seed + 100) y
    go st f recs
      | st == s = (f, reverse recs)
      | even st =
          let (y, z) = untau (toInteger (st `div` 2))
              yi = fromInteger y
              zi = fromInteger z
              xm = length f
              v = evalTotal (compV seed yi zi xm) (aSet yi)
           in go (st + 1) (f ++ [if v == Just 0 then 1 else 0]) (Diag yi zi xm : recs)
      | otherwise =
          let (y, z) = untau (toInteger (st `div` 2))
              yi = fromInteger y
              zi = fromInteger z
              found =
                [ (x, e)
                | x <- inputsV
                , Just e <- [firstExtWhere (/= toInteger (aSet yi x)) (compV seed yi zi x) f]
                ]
           in case found of
                ((x, e) : _) -> case evalSeg (compV seed yi zi x) e of
                  Just w -> go (st + 1) e (Found yi zi x w : recs)
                  Nothing -> go (st + 1) e recs
                [] -> go (st + 1) f (NoExt yi zi f : recs)

lemmaVChecks :: [(String, Bool)]
lemmaVChecks =
  concat
    [ map (check seed fN) recs
        ++ [ ( "seed " ++ show seed ++ ": both answers of stage 2n + 2 occur"
             , any isFound recs && any isNoExt recs ) ]
    | seed <- [1 .. 12]
    , let (fN, recs) = lemmaV seed 44
    ]
  where
    aSet seed y = bits (seed + 100) y
    isFound r = case r of Found {} -> True; _ -> False
    isNoExt r = case r of NoExt {} -> True; _ -> False
    check seed fN (Diag y z xm) =
      ( "seed " ++ show seed ++ ": f(x_m) /= phi_z^(A_y)(x_m), y = " ++ show y ++ ", z = " ++ show z
      , Just (toInteger (headOr (drop xm fN))) /= evalTotal (compV seed y z xm) (aSet seed y) )
    check seed fN (Found y z x w) =
      ( "seed " ++ show seed ++ ": phi_z^f(x) = " ++ show w ++ " /= c_(A_y)(x) on every total f, y = " ++ show y
      , definedOnAll (compV seed y z x) fN == Just w && w /= toInteger (aSet seed y x) )
    check seed _ (NoExt y z fm) =
      ( "seed " ++ show seed ++ ": no extension: E is inside c_(A_y), y = " ++ show y ++ ", z = " ++ show z
      , and
          [ o `elem` [Nothing, Just (toInteger (aSet seed y u))]
          | u <- inputsV, o <- outcomes (compV seed y z u) fm ] )
    headOr (v : _) = v
    headOr [] = -1

-- * th:double-jump-sets: psi

-- | A model: K with the step at which each element appears, and the
-- quadruples <x, y, D_u, D_v> of W_(rho(z_0)) with their steps.
data KModel = KModel [(Integer, Int)] [(Int, (Integer, [Integer], [Integer]))]

inKJump :: KModel -> Integer -> Bool
inKJump (KModel ks qs) x =
  or [all (`elem` kAll) du && not (any (`elem` kAll) dv) | (_, (x', du, dv)) <- qs, x' == x]
  where
    kAll = map fst ks

-- | psi(w) is defined.  Cumulative: the quadruples that have appeared by
-- step w; literal: those that appear exactly at step w.
psiDefined :: Bool -> KModel -> Integer -> Int -> Bool
psiDefined cumulative (KModel ks qs) x w =
  null considered || all (\dv -> any (`elem` kAll) dv) considered
  where
    kAll = map fst ks
    kw = [k | (k, t) <- ks, t <= w]
    considered =
      [ dv
      | (t, (x', du, dv)) <- qs
      , x' == x
      , if cumulative then t <= w else t == w
      , all (`elem` kw) du
      ]

randomKModel :: Word64 -> KModel
randomKModel seed = KModel ks qs
  where
    g0 = mkGen (seed * 31337 + 7)
    (ks, g1) = elems (0 :: Int) g0
    elems k g
      | k >= 12 = ([], g)
      | otherwise =
          let (r, ga) = below 2 g
              (t, gb) = below 30 ga
              (rest, gc) = elems (k + 1) gb
           in (if r == 0 then (toInteger k, t + 1) : rest else rest, gc)
    qs = fst (quads 0 g1)
    quads i g
      | i >= 10 = ([], g)
      | otherwise =
          let (x, ga) = below 4 g
              (nu, gb) = below 3 ga
              (du, gc) = nums nu gb
              (nv, gd) = below 3 gc
              (dv, ge) = nums nv gd
              (rest, gf) = quads (i + 1) ge
           in ((i + 1, (toInteger x, du, dv)) : rest, gf)
    nums 0 g = ([], g)
    nums k g = let (v, g') = below 12 g; (vs, g'') = nums (k - 1 :: Int) g' in (toInteger v : vs, g'')

psiChecks :: [(String, Bool)]
psiChecks =
  [ ( "cumulative: x in K' <=> psi(w) undefined for some w, seed " ++ show seed ++ ", x = " ++ show x
    , inKJump m x == any (not . psiDefined True m x) [0 .. 40] )
  | seed <- [1 .. 300], let m = randomKModel seed, x <- [0 .. 3]
  ]
    ++ [ ("model: x = 0 is in K'", inKJump counter 0)
       , ("cumulative reading: psi(3) is undefined", not (psiDefined True counter 0 3))
       , ("literal reading refuted: psi(w) defined for all w", all (psiDefined False counter 0) [0 .. 40])
       ]
  where
    -- the only quadruple of x = 0 appears at step 1, with D_u = {5};
    -- 5 enters K at step 3; D_v is empty.
    counter = KModel [(5, 3), (7, 1)] [(1, (0, [5], []))]

-- * th:jump-inversion

-- | Stages n + 1 for n < s: (f_s, [(found, x_n)]).
thIX :: Word64 -> (Int -> Int) -> Int -> (Seg, [(Bool, Int)])
thIX seed g s = go 0 [] []
  where
    go n f recs
      | n == s = (f, reverse recs)
      | otherwise =
          let (found, fstar) = case firstExt (family seed n n) f of
                Just e -> (True, e)
                Nothing -> (False, f)
           in go (n + 1) (fstar ++ [g n]) ((found, length fstar) : recs)

-- | Part (ii): from f (and the searches) rebuild x_n and g(n) = f(x_n).
decodeIX :: Word64 -> Seg -> Int -> [Int]
decodeIX seed fN s = go 0 []
  where
    go n f
      | n == s = []
      | otherwise =
          let fstar = maybe f id (firstExt (family seed n n) f)
              v = headOr (drop (length fstar) fN)
           in v : go (n + 1) (fstar ++ [v])
    headOr (v : _) = v
    headOr [] = -1

thIXChecks :: [(String, Bool)]
thIXChecks =
  concat
    [ [ ( "seed " ++ show seed ++ ": n = " ++ show n ++ " in (tau f)' <=> found at stage n + 1"
        , if found then isJust (definedOnAll (family seed n n) fN) else undefinedOnAll (family seed n n) fN )
      | (n, (found, _)) <- zip [0 ..] recs
      ]
        ++ [ ("seed " ++ show seed ++ ": f(x_n) = g(n)", and [take 1 (drop xn fN) == [g n] | (n, (_, xn)) <- zip [0 ..] recs])
           , ("seed " ++ show seed ++ ": part (ii) recovers g", decodeIX seed fN s == map g [0 .. s - 1])
           , ("seed " ++ show seed ++ ": both answers occur", any fst recs && any (not . fst) recs)
           ]
    | seed <- [1 .. 20]
    , let s = 40
          g = bits (seed + 200) 0
          (fN, recs) = thIX seed g s
    ]

-- * th:spector-jump-join

-- | Stages 1..s from f_0 = g_0 = start: (f, g, [(n, odd stage, found)]).
thX :: Word64 -> Seg -> Int -> (Seg, Seg, [(Int, Bool, Bool)], Bool)
thX seed start s = go 0 start start [] True
  where
    go st f g recs sameLen
      | st == s = (f, g, reverse recs, sameLen)
      | otherwise =
          let n = st `div` 2
              sl = sameLen && length f == length g
           in if even st
                then case firstExt (family seed n n) f of
                  Just e -> go (st + 1) (e ++ [1]) (g ++ drop (length f) e ++ [0]) ((n, True, True) : recs) sl
                  Nothing -> go (st + 1) (f ++ [0]) (g ++ [1]) ((n, True, False) : recs) sl
                else case firstExt (family seed n n) g of
                  Just e -> go (st + 1) (f ++ drop (length g) e ++ [0]) (e ++ [1]) ((n, False, True) : recs) sl
                  Nothing -> go (st + 1) (f ++ [1]) (g ++ [0]) ((n, False, False) : recs) sl

thXChecks :: [(String, Bool)]
thXChecks =
  concat
    [ [ ("seed " ++ show seed ++ ", start " ++ show start ++ ": f_m, g_m of equal length", sameLen && length fN == length gN)
      , ( "seed " ++ show seed ++ ", start " ++ show start ++ ": one new point f /= g per stage"
        , length diffs == s )
      ]
        ++ [ ( "seed " ++ show seed ++ ", start " ++ show start ++ ": n in (tau f)' <=> f(x_(2n)) = 1, n = " ++ show n
             , let comp = family seed n n
                   v = valueAt' fN (diffs !!! (2 * n))
                in if v == 1 then isJust (definedOnAll comp fN) else undefinedOnAll comp fN )
           | n <- [0 .. s `div` 2 - 1]
           ]
        ++ [ ( "seed " ++ show seed ++ ", start " ++ show start ++ ": n in (tau g)' <=> g(x_(2n+1)) = 1, n = " ++ show n
             , let comp = family seed n n
                   v = valueAt' gN (diffs !!! (2 * n + 1))
                in if v == 1 then isJust (definedOnAll comp gN) else undefinedOnAll comp gN )
           | n <- [0 .. s `div` 2 - 1]
           ]
        ++ [ ("seed " ++ show seed ++ ": both answers occur", any thd recs && any (not . thd) recs) | null start ]
    | seed <- [1 .. 20]
    , start <- [[], [1, 0, 1]]
    , let s = 40
          (fN, gN, recs, sameLen) = thX seed start s
          diffs = [x | (x, a, b) <- zip3 [0 ..] fN gN, a /= b]
    ]
  where
    thd (_, _, x) = x
    valueAt' f p = case drop p f of (v : _) -> v; [] -> -1
    xs !!! i = case drop i xs of (v : _) -> v; [] -> -1

-- * th:non-re-below-zero-jump

-- | The computations of the model of th:non-re-below-zero-jump: index
-- 0 mod 3 copies the oracle (phi^[f](j) = f(j)), 1 mod 3 copies it with
-- 0 and 1 exchanged, 2 mod 3 is the random family.  (With copying phi_y
-- and phi_z both h = f^0 and h = f^1 can occur, so substage (c) is used.)
compXI :: Word64 -> Int -> Int -> Comp
compXI seed k j = case k `mod` 3 of
  0 -> Ask j (Out 0) (Out 1)
  1 -> Ask j (Out 1) (Out 0)
  _ -> family seed k j

-- | The longest run phi_y^[f](0), phi_y^[f](1), ... of defined 0/1 values,
-- at most len values.
runOf :: Word64 -> Int -> Seg -> Int -> Seg
runOf seed y f len = go 0
  where
    go j
      | j >= len = []
      | otherwise = case evalSeg (compXI seed y j) f of
          Just v | v == 0 || v == 1 -> fromInteger v : go (j + 1)
          _ -> []

-- | h subset phi_z^[g].
inside :: Word64 -> Int -> Seg -> Seg -> Bool
inside seed z h g = and [evalSeg (compXI seed z i) g == Just (toInteger v) | (i, v) <- zip [0 ..] h]

-- | Substage search: an extension f~ of f_n and g with R(f~, y, g, z, h).
-- The model computations on input j ask below j + 6, so extensions of
-- length m + 12 and runs of length m + 6 decide it exactly.
searchR :: Word64 -> Int -> Int -> Seg -> Seg -> Maybe (Seg, Seg)
searchR seed y z fn h =
  case [(e, gr) | e <- exts, let gr = runOf seed y e (m + 6), inside seed z h gr] of
    (r : _) -> Just r
    [] -> Nothing
  where
    m = length fn
    exts = [fn ++ b | b <- allBits 12]
    allBits 0 = [[]]
    allBits k = [v : r | r <- allBits (k - 1 :: Int), v <- [0, 1]]

data RecXI = ViaC Int Int Int Seg Int | ViaAB Int Int Int Seg Int

thXI :: Word64 -> Int -> (Seg, [RecXI], Bool)
thXI seed s = go 0 [] [] True
  where
    cx x = bits (seed + 300) x
    go n f recs okDiff
      | n == s = (f, reverse recs, okDiff)
      | otherwise =
          let (x, y, z) = case piN 3 (toInteger n) of
                [a, b, c] -> (fromInteger a, fromInteger b, fromInteger c)
                _ -> (0, 0, 0)
              m = length f
              f0 = f ++ [0]
              f1 = f ++ [1]
           in case searchR seed y z f f0 of
                Nothing -> go (n + 1) f0 (ViaAB x y z f0 m : recs) okDiff
                Just (e0, g0) -> case searchR seed y z f f1 of
                  Nothing -> go (n + 1) f1 (ViaAB x y z f1 m : recs) okDiff
                  Just (e1, g1) ->
                    case [w | (w, a, b) <- zip3 [0 ..] g0 g1, a /= b] of
                      (w : _) ->
                        let e = if take 1 (drop w g0) /= [cx x w] then e0 else e1
                         in go (n + 1) e (ViaC x y z e w : recs) okDiff
                      [] -> go (n + 1) f0 recs False

thXIChecks :: [(String, Bool)]
thXIChecks =
  concat
    [ [("seed " ++ show seed ++ ": in (c) g^0 and g^1 differ at a point", okDiff)]
        ++ map (check seed) recs
        ++ [("seed " ++ show seed ++ ": substages (a)/(b) and (c) both occur", any isC recs && any (not . isC) recs)]
    | seed <- [1 .. 6]
    , let (_, recs, okDiff) = thXI seed 40
    ]
  where
    isC r = case r of ViaC {} -> True; _ -> False
    cx seed x = bits (seed + 300) x
    check seed (ViaC x y _ e w) =
      ( "seed " ++ show seed ++ ": (c) phi_y^[f_(n+1)](w) /= c_x(w), x = " ++ show x
      , case evalSeg (compXI seed y w) e of
          Just v -> v /= toInteger (cx seed x w)
          Nothing -> False )
    check seed (ViaAB x y z h m) =
      ( "seed " ++ show seed ++ ": (a)/(b) f_(n+1) not in phi_z^(c_x) or phi_y^F /= c_x, x = " ++ show x
      , let cseg = map (cx seed x) [0 .. m + 5]
            notInside = not (inside seed z h cseg)
            noExt = and [take (m + 6) (runOf seed y e (m + 6)) /= cseg | e <- [h ++ b | b <- allBits 11]]
         in notInside || noExt )
    allBits 0 = [[]]
    allBits k = [v : r | r <- allBits (k - 1 :: Int), v <- [0, 1]]

-- * th:rational-chain-degrees, parts 2-3

sx :: Integer -> Integer -> Integer
sx x z = if z < x then z else z + 1

-- | All rationals in lowest terms: 0, then +-p/q by p + q.
rationals :: [Rational]
rationals = 0 : concat [[r, negate r] | k <- [2 ..], p <- [1 .. k - 1], let q = k - p, gcd p q == 1, let r = p % q]

rationalChecks :: [(String, Bool)]
rationalChecks =
  [ ( "s_" ++ show x ++ " is increasing onto [0, 40] - {x}"
    , let vs = map (sx x) [0 .. 39] in vs == [v | v <- [0 .. 40], v /= x] )
  | x <- [0 .. 40]
  ]
    ++ [ ( "f^((" ++ show x ++ ")) is f without its " ++ show x ++ "-th section"
         , [[f (sx x z) y | y <- [0 .. 5]] | z <- [0 .. 6]] == [row | (i, row) <- zip [0 ..] rows, i /= x] )
       | x <- [0 .. 7 :: Integer]
       , let f a b = toInteger (bits 400 (fromInteger a) (fromInteger b))
             rows = [[f a b | b <- [0 .. 5]] | a <- [0 .. 7]]
       ]
    ++ [ ( "r <= s <=> {n | r_n < r} subset {n | r_n < s}: " ++ show (r, s)
         , (r <= s) == all (\q -> q >= r || q < s) codes )
       | let codes = take 400 rationals, r <- take 40 rationals, s <- take 40 rationals
       ]
    ++ [ ( "{n | r_n < " ++ show r ++ "} grows with the list"
         , let cnt k = length (filter (< r) (take k rationals)) in cnt 100 < cnt 400 && cnt 400 < cnt 1600 )
       | r <- take 40 rationals
       ]
    ++ [("first rationals are distinct", length (sortNub (take 400 rationals)) == 400)]
    ++ [("tau and untau agree on the codes used", all (\n -> uncurry tau (untau n) == n) [0 .. 2000])]
