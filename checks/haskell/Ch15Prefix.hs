-- | Shared definitions of the checks of chapters 15-16 (CheckCh15*.hs,
-- CheckCh16*.hs), base only: the Tarski-Kuratowski algorithm as a
-- computation of levels, and the prefix rules of theorems 16-III and
-- 16-VII.
--
-- * The Tarski-Kuratowski algorithm (§ 14.3, used in §§ 15.1, 15.2 and in
--   ch. 16): a formula is built from atoms of known level by negation,
--   conjunction, disjunction, implication, equivalence and by quantifiers
--   over numbers (type 0) and over functions or sets (type 1).  'level'
--   computes, for each formula, the least n with the formula in Sigma_n
--   and the least n with it in Pi_n that the rules give, first in the
--   arithmetical hierarchy and, once a type-1 quantifier is present, in
--   the analytical one.  The rules used: a recursive matrix is Sigma_0 =
--   Pi_0; Sigma_n and Pi_n (n > 0) are closed under & and or; an
--   existential number quantifier over Sigma_n (n > 0) gives Sigma_n
--   (contraction of quantifiers, § 14.3), over Pi_n gives Sigma_(n+1);
--   dummy quantifiers give Sigma_n u Pi_n inside Sigma_(n+1) n Pi_(n+1)
--   (theorem 14-II); for the analytical levels n > 0 a number quantifier
--   changes nothing (theorem 16-III (iii), (iv) and (ii)); a function
--   quantifier over an arithmetical formula gives Sigma^1_1 or Pi^1_1,
--   except that a function quantifier over a Sigma_1 (for exists) or Pi_1
--   (for forall) formula gives back Sigma_1 or Pi_1 (theorem 16-VII (i),
--   after contracting the number quantifier into the function one).  The
--   result is the level the algorithm proves, an upper bound; it is not a
--   proof that the relation is not lower.
--
-- * Prefixes (§ 16.1): a quantifier is (kind, type), kind E or A, type 0
--   or 1.  'ruleSteps' lists every prefix obtained from a prefix by one
--   application of a rule of theorem 16-III ((i) contraction of two equal
--   type-0 quantifiers, (ii) the same for type 1, (iii) a type-0
--   quantifier made type 1, (iv) forall^0 exists^1 -> exists^1 forall^0
--   and exists^0 forall^1 -> forall^1 exists^0), of a dummy quantifier
--   added at the end, or of theorem 16-VII (i) (the last quantifier made
--   type 0).
module Ch15Prefix
  ( Form (..), Cx (..), level, inf, inSigma, inPi, inSigma1, inPi1
  , Kind (..), Q (..), Rule (..), applyRule, isStep, reduced, alternations
  , normalize, validChain
  ) where

-- * Levels by the Tarski-Kuratowski algorithm

data Form
  = Rec                  -- ^ a recursive relation
  | Known Int Int        -- ^ an arithmetical atom in Sigma_s and Pi_p
  | KnownA Int Int       -- ^ an analytical atom in Sigma^1_s and Pi^1_p
  | Not Form
  | And Form Form
  | Or Form Form
  | Imp Form Form
  | Iff Form Form
  | E0 Form | A0 Form    -- ^ number quantifiers
  | E1 Form | A1 Form    -- ^ function (set) quantifiers
  deriving (Eq, Show)

-- | Levels: arithmetical Sigma, Pi (inf when not arithmetical by the
-- rules) and analytical Sigma^1, Pi^1 (0, 0 for arithmetical formulas).
data Cx = Cx {aS :: Int, aP :: Int, hS :: Int, hP :: Int}
  deriving (Eq, Show)

inf :: Int
inf = 1000

arith :: Int -> Int -> Cx
arith s p = close (Cx s p 0 0)

anal :: Int -> Int -> Cx
anal s p = close (Cx inf inf s p)

-- | Dummy quantifiers: Sigma_n u Pi_n inside Sigma_(n+1) n Pi_(n+1).
close :: Cx -> Cx
close (Cx s p s1 p1) =
  Cx (min s (p + 1)) (min p (s + 1)) (min s1 (p1 + 1)) (min p1 (s1 + 1))

isArith :: Cx -> Bool
isArith c = hS c == 0 && hP c == 0

level :: Form -> Cx
level f = case f of
  Rec -> arith 0 0
  Known s p -> arith s p
  KnownA s p -> anal s p
  Not g -> let Cx s p s1 p1 = level g in Cx p s p1 s1
  And g h -> both (level g) (level h)
  Or g h -> both (level g) (level h)
  Imp g h -> level (Or (Not g) h)
  Iff g h -> level (And (Imp g h) (Imp h g))
  E0 g -> number True (level g)
  A0 g -> number False (level g)
  E1 g -> function True (level g)
  A1 g -> function False (level g)
  where
    both (Cx s p s1 p1) (Cx s' p' s1' p1') =
      close (Cx (max s s') (max p p') (max s1 s1') (max p1 p1'))
    number ex c
      | isArith c =
          if ex
            then let s = min (max 1 (aS c)) (aP c + 1) in arith s (s + 1)
            else let p = min (max 1 (aP c)) (aS c + 1) in arith (p + 1) p
      | otherwise = c
    function ex c
      | isArith c && ex && aS c <= 1 = arith 1 2
      | isArith c && not ex && aP c <= 1 = arith 2 1
      | ex = let s = min (max 1 (hS c)) (hP c + 1) in anal s (s + 1)
      | otherwise = let p = min (max 1 (hP c)) (hS c + 1) in anal (p + 1) p

inSigma, inPi, inSigma1, inPi1 :: Int -> Form -> Bool
inSigma n f = let c = level f in isArith c && aS c <= n
inPi n f = let c = level f in isArith c && aP c <= n
inSigma1 n f = hS (level f) <= n
inPi1 n f = hP (level f) <= n

-- * Prefixes and the rules of theorems 16-III and 16-VII

data Kind = E | A deriving (Eq, Show)

data Q = Q Kind Int deriving (Eq, Show)

data Rule
  = R1 | R2 | R3 | R4   -- ^ theorem 16-III (i)-(iv)
  | Dummy               -- ^ a dummy quantifier at the end
  | AK1                 -- ^ theorem 16-VII (i)
  deriving (Eq, Show)

-- | All prefixes obtained by one application of the rule.
applyRule :: Rule -> [Q] -> [[Q]]
applyRule r p = case r of
  R1 -> contract 0
  R2 -> contract 1
  R3 -> [ before ++ [Q k 1] ++ after
        | (before, Q k 0 : after) <- splits ]
  R4 -> [ before ++ [Q k' 1, Q k 0] ++ after
        | (before, Q k 0 : Q k' 1 : after) <- splits, k /= k' ]
  Dummy -> [p ++ [Q k t] | k <- [E, A], t <- [0, 1]]
  AK1 -> case reverse p of
    Q k 1 : rest -> [reverse (Q k 0 : rest)]
    _ -> []
  where
    splits = [splitAt i p | i <- [0 .. length p - 1]]
    contract t = [ before ++ [Q k t] ++ after
                 | (before, Q k u : Q k' u' : after) <- splits
                 , u == t, u' == t, k == k' ]

isStep :: Rule -> [Q] -> [Q] -> Bool
isStep r p q = q `elem` applyRule r p

-- | The reduced prefix (type-1 quantifiers only).
reduced :: [Q] -> [Kind]
reduced p = [k | Q k 1 <- p]

-- | The number of changes of kind in a list of kinds.
alternations :: [Kind] -> Int
alternations ks = length [() | (a, b) <- zip ks (drop 1 ks), a /= b]

-- | The procedure of the proof of corollary 16-III (exercise 16-3), as a
-- chain of rule applications ending in an alternating prefix of n
-- type-1 quantifiers and one type-0 quantifier.  Only for prefixes with
-- a type-1 quantifier.
normalize :: [Q] -> [(Rule, [Q])]
normalize p = case stepOnce p of
  Just (r, q) -> (r, q) : normalize q
  Nothing -> []

stepOnce :: [Q] -> Maybe (Rule, [Q])
stepOnce p
  -- (iv): a type-0 quantifier moves right past a type-1 one of the
  -- other kind
  | (b, Q k 0 : Q k' 1 : a) : _ <- [s | s@(_, Q k 0 : Q k' 1 : _) <- sp, k /= k']
  = Just (R4, b ++ [Q k' 1, Q k 0] ++ a)
  -- (iii): a type-0 quantifier before a type-1 one of the same kind
  | (b, Q k 0 : a@(Q _ 1 : _)) : _ <- [s | s@(_, Q k 0 : Q k' 1 : _) <- sp, k == k']
  = Just (R3, b ++ Q k 1 : a)
  -- (ii), (i): contraction
  | (b, Q k t : Q _ _ : a) : _ <- [s | s@(_, Q k t : Q k' t' : _) <- sp, k == k', t == t']
  = Just (if t == 1 then R2 else R1, b ++ Q k t : a)
  -- now the type-1 quantifiers come first; a type-0 quantifier of the
  -- same kind as the last type-1 one is made type 1 (it then moves left)
  | Q k1 1 : _ <- reverse [q | q@(Q _ 1) <- p]
  , (b, Q _ 0 : a) : _ <- [s | s@(_, Q k 0 : _) <- sp, k == k1]
  = Just (R3, b ++ Q k1 1 : a)
  -- finally a dummy type-0 quantifier of the other kind at the end
  | Q k1 1 : _ <- reverse p = Just (Dummy, p ++ [Q (other k1) 0])
  | otherwise = Nothing
  where
    sp = [splitAt i p | i <- [0 .. length p - 1]]
    other E = A
    other A = E

-- | Every link of the chain is an application of its rule.
validChain :: [Q] -> [(Rule, [Q])] -> Bool
validChain _ [] = True
validChain p ((r, q) : rest) = isStep r p q && validChain q rest
