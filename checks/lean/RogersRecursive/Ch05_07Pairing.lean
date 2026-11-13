import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Basic

/-!
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная вычислимость»
(Мир, 1972), § 5.3 (pp. 89–90), § 5.6 (p. 98), § 7.6 (p. 121).

Notation.  `tau x y` is τ(x, y) = 1/2 (x² + 2xy + y² + 3x + y) of p. 89
(`/` is integer division; the numerator is even, so it is exact).
`tri n` = 0 + 1 + … + n.  A tuple ⟨x₁, …, xₙ⟩ (n ≥ 1) is the list
`x₁ :: [x₂, …, xₙ]`, and τⁿ(x₁, …, xₙ) is `List.foldl tau x₁ [x₂, …, xₙ]`,
which is the inductive definition of p. 90: τ¹ = λx[x],
τⁿ⁺¹(x₁, …, xₙ₊₁) = τ(τⁿ(x₁, …, xₙ), xₙ₊₁) (`tauN_snoc`).  All finite
tuples, the empty one included, are the lists of naturals; `tauStar` is τ*
of p. 98: τ*(∅) = 0, τ*(⟨x₁, …, xₙ⟩) = τ(τⁿ(x₁, …, xₙ), n − 1) + 1.
For § 7.6, `timesN A` is A × N = τ(A ⨯ N) (p. 90, `times`), and a reduction
"A to B via f" is `∀ x, x ∈ A ↔ f x ∈ B`.

What is proved, for all natural numbers: τ = tri(x + y) + x; the lemma of
§ 5.3, τ is one-one from N ⨯ N onto N (`tau_inj`, `tau_surjective`); the
listing of p. 89 of the pairs coded by 0, …, 7 and example 1 of p. 90
(⟨2, 1, 0⟩ = ⟨⟨2, 1⟩, 0⟩ = ⟨8, 0⟩ = 44); for every n, τⁿ is one-one on
n-tuples and onto N; the two printed forms of τ* agree and τ* is one-one
from all finite tuples onto N (p. 98–99: «эффективным взаимно однозначным
отображением на»).  Theorem 7-VIII (a)–(d) and its corollary as
statements about the reducing maps: λx[⟨x, 0⟩] is one-one and reduces A to
A × N; π₁ reduces A × N to A; for f reducing B to C, λx[⟨f(x), x⟩] is
one-one and reduces B to C × N; the composites of the proof of (d).

Not covered: that the maps are recursive (Church's thesis in the book;
they are given by explicit formulas), π₁ and π₂ as functions (only through
τ), the codings' use in the rest of the chapter, the canonical indices.
-/

namespace RogersRecursive.Ch05_07

/-- τ of p. 89. -/
def tau (x y : ℕ) : ℕ := (x * x + 2 * x * y + y * y + 3 * x + y) / 2

/-- tri n = 0 + 1 + … + n. -/
def tri : ℕ → ℕ
  | 0 => 0
  | k + 1 => tri k + (k + 1)

theorem two_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [tri]
    rw [Nat.mul_add, ih]
    ring

theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + k + 1 := by
  simp only [tri]
  omega

theorem tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih =>
    rw [tri_succ]
    omega

/-- τ(x, y) = (0 + 1 + … + (x + y)) + x: "the identity 0 + 1 + … + n = n(n + 1)/2". -/
theorem tau_eq (x y : ℕ) : tau x y = tri (x + y) + x := by
  unfold tau
  have h := two_tri (x + y)
  have e : x * x + 2 * x * y + y * y + 3 * x + y = 2 * (tri (x + y) + x) := by
    rw [Nat.mul_add, h]
    ring
  rw [e, Nat.mul_div_cancel_left _ (by norm_num)]

/-- The lemma of § 5.3: τ is one-one. -/
theorem tau_inj {x y x' y' : ℕ} (h : tau x y = tau x' y') : x = x' ∧ y = y' := by
  rw [tau_eq, tau_eq] at h
  have hs : x + y = x' + y' := by
    rcases lt_trichotomy (x + y) (x' + y') with hlt | heq | hgt
    · have h1 := tri_mono (show x + y + 1 ≤ x' + y' by omega)
      have h2 := tri_succ (x + y)
      omega
    · exact heq
    · have h1 := tri_mono (show x' + y' + 1 ≤ x + y by omega)
      have h2 := tri_succ (x' + y')
      omega
  rw [hs] at h
  omega

/-- The lemma of § 5.3: τ is onto N. -/
theorem tau_surjective (z : ℕ) : ∃ x y, tau x y = z := by
  induction z with
  | zero => exact ⟨0, 0, rfl⟩
  | succ z ih =>
    obtain ⟨x, y, h⟩ := ih
    rw [tau_eq] at h
    cases y with
    | zero =>
      refine ⟨0, x + 1, ?_⟩
      rw [tau_eq, Nat.zero_add, tri_succ]
      simp only [Nat.add_zero] at h
      omega
    | succ y =>
      refine ⟨x + 1, y, ?_⟩
      rw [tau_eq, show x + 1 + y = x + (y + 1) by omega]
      omega

/-- p. 89: 0, 1, …, 7 code ⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨0,2⟩, ⟨1,1⟩, ⟨2,0⟩, ⟨0,3⟩, ⟨1,2⟩. -/
theorem pairs_listing :
    [tau 0 0, tau 0 1, tau 1 0, tau 0 2, tau 1 1, tau 2 0, tau 0 3, tau 1 2] =
      [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide

/-- τⁿ(x₁, …, xₙ) for the tuple `x₁ :: xs`. -/
def tauN (x : ℕ) (xs : List ℕ) : ℕ := xs.foldl tau x

/-- The inductive definition of p. 90: τⁿ⁺¹(x₁, …, xₙ₊₁) = τ(τⁿ(x₁, …, xₙ), xₙ₊₁). -/
theorem tauN_snoc (x : ℕ) (xs : List ℕ) (y : ℕ) : tauN x (xs ++ [y]) = tau (tauN x xs) y := by
  simp [tauN, List.foldl_append]

/-- Example 1 of p. 90: ⟨2, 1, 0⟩ = ⟨⟨2, 1⟩, 0⟩ = ⟨8, 0⟩ = 44. -/
theorem example_one : tauN 2 [1, 0] = tau (tau 2 1) 0 ∧ tau 2 1 = 8 ∧ tau 8 0 = 44 := by
  decide

/-- τⁿ is one-one on tuples of the same length. -/
theorem tauN_inj : ∀ (xs xs' : List ℕ) (x x' : ℕ), xs.length = xs'.length →
    tauN x xs = tauN x' xs' → x = x' ∧ xs = xs'
  | [], [], _, _, _, h => ⟨h, rfl⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | y :: ys, y' :: ys', x, x', hl, h => by
    simp only [tauN, List.foldl_cons] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨h1, h2⟩ := tauN_inj ys ys' (tau x y) (tau x' y') hl h
    obtain ⟨hx, hy⟩ := tau_inj h1
    exact ⟨hx, by rw [hy, h2]⟩

/-- τⁿ is onto N for every n ≥ 1 (tuples `x :: xs` with `xs.length = n`). -/
theorem tauN_surjective (n z : ℕ) : ∃ x xs, xs.length = n ∧ tauN x xs = z := by
  induction n generalizing z with
  | zero => exact ⟨z, [], rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, y, ha⟩ := tau_surjective z
    obtain ⟨x, xs, hl, hx⟩ := ih a
    exact ⟨x, xs ++ [y], by simp [hl], by rw [tauN_snoc, hx, ha]⟩

/-- τ* of p. 98 on all finite tuples. -/
def tauStar : List ℕ → ℕ
  | [] => 0
  | x :: xs => tau (tauN x xs) xs.length + 1

/-- The second printed form: τ*(⟨x₁, …, xₙ⟩) = ⟨x₁, …, xₙ, n − 1⟩ + 1. -/
theorem tauStar_second_form (x : ℕ) (xs : List ℕ) :
    tauStar (x :: xs) = tauN x (xs ++ [xs.length]) + 1 := by
  rw [tauN_snoc]
  rfl

/-- τ* is one-one. -/
theorem tauStar_injective : Function.Injective tauStar := by
  intro l l' h
  cases l with
  | nil =>
    cases l' with
    | nil => rfl
    | cons x' xs' => simp [tauStar] at h
  | cons x xs =>
    cases l' with
    | nil => simp [tauStar] at h
    | cons x' xs' =>
      simp only [tauStar, Nat.add_right_cancel_iff] at h
      obtain ⟨h1, h2⟩ := tau_inj h
      obtain ⟨hx, hxs⟩ := tauN_inj xs xs' x x' h2 h1
      rw [hx, hxs]

/-- τ* is onto N. -/
theorem tauStar_surjective : Function.Surjective tauStar := by
  intro z
  cases z with
  | zero => exact ⟨[], rfl⟩
  | succ z =>
    obtain ⟨a, m, ha⟩ := tau_surjective z
    obtain ⟨x, xs, hl, hx⟩ := tauN_surjective m a
    refine ⟨x :: xs, ?_⟩
    simp only [tauStar, hl, hx, ha]

/-! ### Theorem 7-VIII: the reducing maps -/

/-- A × N = τ(A ⨯ N). -/
def timesN (A : Set ℕ) : Set ℕ := {z | ∃ a n, a ∈ A ∧ z = tau a n}

theorem mem_prod_tau (A : Set ℕ) (a n : ℕ) : tau a n ∈ timesN A ↔ a ∈ A := by
  constructor
  · rintro ⟨a', n', ha', h⟩
    rw [(tau_inj h).1]
    exact ha'
  · intro ha
    exact ⟨a, n, ha, rfl⟩

/-- The first inverse function π₁ (p. 90), chosen through `tau_surjective`. -/
noncomputable def pi1 (z : ℕ) : ℕ := Classical.choose (tau_surjective z)

theorem tau_pi1 (z : ℕ) : ∃ n, tau (pi1 z) n = z := Classical.choose_spec (tau_surjective z)

theorem pi1_tau (a n : ℕ) : pi1 (tau a n) = a := by
  obtain ⟨m, hm⟩ := tau_pi1 (tau a n)
  exact (tau_inj hm).1

/-- 7-VIII (a): A ≤₁ A × N via λx[⟨x, 0⟩]. -/
theorem viii_a (A : Set ℕ) :
    Function.Injective (fun x => tau x 0) ∧ ∀ x, x ∈ A ↔ tau x 0 ∈ timesN A :=
  ⟨fun _ _ h => (tau_inj h).1, fun x => (mem_prod_tau A x 0).symm⟩

/-- 7-VIII (b): A × N ≤m A via π₁. -/
theorem viii_b (A : Set ℕ) : ∀ z, z ∈ timesN A ↔ pi1 z ∈ A := by
  intro z
  obtain ⟨n, hn⟩ := tau_pi1 z
  rw [← hn, mem_prod_tau, pi1_tau]

/-- 7-VIII (c), ⇒: if B ≤m C via f, then B ≤₁ C × N via f' = λx[⟨f(x), x⟩]. -/
theorem viii_c (B C : Set ℕ) (f : ℕ → ℕ) (hf : ∀ x, x ∈ B ↔ f x ∈ C) :
    Function.Injective (fun x => tau (f x) x) ∧ ∀ x, x ∈ B ↔ tau (f x) x ∈ timesN C :=
  ⟨fun _ _ h => (tau_inj h).2, fun x => by rw [mem_prod_tau]; exact hf x⟩

/-- 7-VIII (d), ⇒: A ≤m B via f gives A × N ≤₁ B × N via λz[⟨f(π₁ z), z⟩]. -/
theorem viii_d_forward (A B : Set ℕ) (f : ℕ → ℕ) (hf : ∀ x, x ∈ A ↔ f x ∈ B) :
    Function.Injective (fun z => tau (f (pi1 z)) z) ∧
      ∀ z, z ∈ timesN A ↔ tau (f (pi1 z)) z ∈ timesN B :=
  ⟨fun _ _ h => (tau_inj h).2, fun z => by rw [viii_b, mem_prod_tau]; exact hf _⟩

/-- 7-VIII (d), ⇐: A × N ≤₁ B × N via F gives A ≤m B via λx[π₁ F(⟨x, 0⟩)]. -/
theorem viii_d_backward (A B : Set ℕ) (F : ℕ → ℕ) (hF : ∀ z, z ∈ timesN A ↔ F z ∈ timesN B) :
    ∀ x, x ∈ A ↔ pi1 (F (tau x 0)) ∈ B := by
  intro x
  rw [← viii_b, ← hF, mem_prod_tau]

end RogersRecursive.Ch05_07

#print axioms RogersRecursive.Ch05_07.tau_eq
#print axioms RogersRecursive.Ch05_07.tau_inj
#print axioms RogersRecursive.Ch05_07.tau_surjective
#print axioms RogersRecursive.Ch05_07.pairs_listing
#print axioms RogersRecursive.Ch05_07.tauN_snoc
#print axioms RogersRecursive.Ch05_07.example_one
#print axioms RogersRecursive.Ch05_07.tauN_inj
#print axioms RogersRecursive.Ch05_07.tauN_surjective
#print axioms RogersRecursive.Ch05_07.tauStar_second_form
#print axioms RogersRecursive.Ch05_07.tauStar_injective
#print axioms RogersRecursive.Ch05_07.tauStar_surjective
#print axioms RogersRecursive.Ch05_07.viii_a
#print axioms RogersRecursive.Ch05_07.viii_b
#print axioms RogersRecursive.Ch05_07.viii_c
#print axioms RogersRecursive.Ch05_07.viii_d_forward
#print axioms RogersRecursive.Ch05_07.viii_d_backward
