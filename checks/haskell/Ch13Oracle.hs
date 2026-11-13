-- | Shared definitions of the checks of chapter 13 (CheckCh13*.hs), base
-- only: model oracle computations on segments (§ 13.1, p. 332).
--
-- * A segment f is an initial segment with values in {0, 1}, kept as the
--   list f(0), ..., f(len - 1) (p. 332, point 2).
-- * An oracle computation of phi_z on input x is a finite tree of
--   questions "f(p) = ?" with answers 0, 1; a leaf gives an output or
--   loops.  phi_z^[f](x) (p. 332, point 3) is defined exactly when the
--   computation along f stops and every question it asks is about a
--   p < len f; for a total function F, phi_z^F(x) follows the tree with
--   F.  The trees are finite, so "exists an extension of f on which
--   phi_z^[.](x) is defined" and "for every total extension F of f" are
--   decided by walking the tree.
-- * Model families of such computations are drawn by the generator of
--   Ch08Coding (fixed seeds, every run draws the same cases).  They stand
--   for the oracle computations phi_z^[f]; nothing here is about their
--   recursiveness.
module Ch13Oracle
  ( Comp (..), Seg
  , evalSeg, evalTotal, outcomes, definedOnAll, undefinedOnAll
  , firstExt, firstExtWhere, isPrefixOf'
  , randComp, family
  ) where

import Ch08Coding (Gen, below, mkGen, sortNub)
import Data.Word (Word64)

-- | Ask p c0 c1: the question "f(p) = ?"; c0 after the answer 0, c1 after 1.
data Comp = Out Integer | Ask Int Comp Comp | Loop

type Seg = [Int]

valueAt :: Seg -> Int -> Maybe Int
valueAt f p = case drop p f of
  (v : _) -> Just v
  [] -> Nothing

-- | phi^[f](x): Nothing when the computation loops or asks about a point
-- outside the domain of f.
evalSeg :: Comp -> Seg -> Maybe Integer
evalSeg (Out y) _ = Just y
evalSeg Loop _ = Nothing
evalSeg (Ask p c0 c1) f = case valueAt f p of
  Just v -> evalSeg (if v == 0 then c0 else c1) f
  Nothing -> Nothing

-- | phi^F(x) for a total 0/1 function F.
evalTotal :: Comp -> (Int -> Int) -> Maybe Integer
evalTotal (Out y) _ = Just y
evalTotal Loop _ = Nothing
evalTotal (Ask p c0 c1) fun = evalTotal (if fun p == 0 then c0 else c1) fun

-- | The results of the computation over all total extensions F of f
-- (Nothing: it does not stop).  A question asked twice on a branch gets the
-- earlier answer.
outcomes :: Comp -> Seg -> [Maybe Integer]
outcomes c f = sortNub (go c [])
  where
    go :: Comp -> [(Int, Int)] -> [Maybe Integer]
    go (Out y) _ = [Just y]
    go Loop _ = [Nothing]
    go (Ask p c0 c1) fixed = case valueAt f p of
      Just v -> go (branch v) fixed
      Nothing -> case lookup p fixed of
        Just v -> go (branch v) fixed
        Nothing -> go c0 ((p, 0) : fixed) ++ go c1 ((p, 1) : fixed)
      where
        branch v = if v == 0 then c0 else c1

-- | phi^F(x) = y for every total extension F of f.
definedOnAll :: Comp -> Seg -> Maybe Integer
definedOnAll c f = case outcomes c f of
  [Just y] -> Just y
  _ -> Nothing

-- | phi^F(x) is undefined for every total extension F of f.
undefinedOnAll :: Comp -> Seg -> Bool
undefinedOnAll c f = outcomes c f == [Nothing]

-- | The first initial segment extending f (depth first, answer 0 first;
-- new points not asked about are 0) on which phi^[.](x) is defined and the
-- output satisfies the condition.
firstExtWhere :: (Integer -> Bool) -> Comp -> Seg -> Maybe Seg
firstExtWhere ok c f = go c []
  where
    go (Out y) fixed = if ok y then Just (fill fixed) else Nothing
    go Loop _ = Nothing
    go (Ask p c0 c1) fixed = case valueAt f p of
      Just v -> go (branch v) fixed
      Nothing -> case lookup p fixed of
        Just v -> go (branch v) fixed
        Nothing -> case go c0 ((p, 0) : fixed) of
          Just s -> Just s
          Nothing -> go c1 ((p, 1) : fixed)
      where
        branch v = if v == 0 then c0 else c1
    fill fixed =
      f ++ [maybe 0 id (lookup i fixed) | i <- [length f .. top fixed]]
    top fixed = maximum (length f - 1 : map fst fixed)

firstExt :: Comp -> Seg -> Maybe Seg
firstExt = firstExtWhere (const True)

isPrefixOf' :: Seg -> Seg -> Bool
isPrefixOf' a b = take (length a) b == a

-- | A random computation: at most d questions on a branch about points in
-- [0, hi), outputs 0 or 1, loops with probability 3/10 at a leaf.
randComp :: Int -> Int -> Gen -> (Comp, Gen)
randComp d hi g
  | d == 0 = leaf g
  | otherwise =
      let (r, g1) = below 10 g
       in if r < 2
            then leaf g1
            else
              let (p, g2) = below hi g1
                  (c0, g3) = randComp (d - 1) hi g2
                  (c1, g4) = randComp (d - 1) hi g3
               in (Ask p c0 c1, g4)
  where
    leaf g' =
      let (r, g1) = below 10 g'
       in if r < 3
            then (Loop, g1)
            else let (v, g2) = below 2 g1 in (Out (toInteger v), g2)

-- | A model family phi_z^[.](x): the computation with index z on input x
-- asks only about points below x + 6 (so the searches are finite).
family :: Word64 -> Int -> Int -> Comp
family seed z x =
  fst (randComp 3 (x + 6) (mkGen (seed * 1000003 + fromIntegral z * 7919 + fromIntegral x)))
