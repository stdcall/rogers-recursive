import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Functionals (§ 15.3) and set-theoretic steps of chapter 16

Places in the book:

* § 15.3, p. 459, the functional `F` of an enumeration operator `Φ`, in
  the corrected reading of the weak domain (`Φ(τ(φ))` has at most one
  element).  Exercise 15-26 (a) (`ex:recursive-functional-weak-domain`):
  if `Φ(τ(f))` has at most one element for every total `f`, then for every
  partial `φ` (`weak_domain`); 15-26 (b): if every `Φ(τ(φ))` has exactly one
  element, `F` is constant (`strong_domain_const`).  The printed reading
  (`Φ(τ(φ))` not empty) fails 15-26 (a): `Φ₀`, an enumeration operator with
  `Φ₀(A) = {0}` when `A` contains a pair `⟨0, b⟩`, is nonempty on all total
  functions and empty on the nowhere defined one (`printed_fails`).
* Theorem 15-XXXI (Friedberg, `th:friedberg-effective-operation`, p. 464):
  the function `ψ` of the proof and the step "then `F(g)` is undefined".
  With `k ≠ 0` and `φ_(x')(n) ≠ k` for all `x' < n` (the corrected choice of
  `k`), `ψ` diverges on every index of `g` (`friedberg_corrected`), and every
  index of `g` is `≥ n` (`friedberg_indices`).  The printed choice ("every
  Gödel number of `g` is `≥ n`") does not suffice: on a numbering with an
  `x' < n` agreeing with `g` up to `n`, `ψ` converges on an index of `g`
  (`friedberg_printed_insufficient`), and for `k = 0` `ψ` converges on every
  index of `g` (`friedberg_k_zero`).
* Theorem 16-XXVII (`th:pi11-reduction`, p. 517): with the printed
  `A' ∩ B = ∅` and `A = N` one gets `A' = N - B` (`reduction_printed`), so
  `B ∈ Π¹₁ - Σ¹₁` (e.g. `T`) admits no such `A' ∈ Π¹₁`; the theorem needs
  `A' ∩ B' = ∅`.
* Exercise 16-46 (a) (`ex:h-isomorphic-not-recursive`), the hint as
  corrected: `f(y) = p_x(z)` with `y ∈ B ⊆ T`, `z ∈ C ⊆ N - T` gives
  `f(T) ≠ p_x(T)` (`image_ne`); the printed `f(y) ≠ p_x(z)` does not
  (`printed_hint_useless`).
* Exercise 16-93 (`ex:shoenfield-chain`): with `D_(β+1) = D_β ∩ (D_β)'` the
  printed union at the limit gives `D_ω = D_0 = N` for every jump operator
  (`shoenfield_union`), not a set of degree `h_(ω+1)`.

Notation: partial functions are single-valued sets of pairs (`SV`), total
functions their graphs; an enumeration operator is used only through its
monotonicity (theorem 9-XXI).  `φ x` is any numbering of partial
functions (`Option`), `ψ(x)` converges iff `Dom φ x`.

Not covered: recursiveness of the operators, functionals and numberings;
the other steps of the proofs.
-/

namespace RogersRecursive.Ch15_16.Functionals

/-! ### The weak domain (p. 459) -/

/-- A single-valued set of pairs (a partial function). -/
def SV (A : Set (ℕ × ℕ)) : Prop := ∀ p ∈ A, ∀ q ∈ A, p.1 = q.1 → p.2 = q.2

/-- The graph of a total function. -/
def graph (f : ℕ → ℕ) : Set (ℕ × ℕ) := {p | p.2 = f p.1}

theorem sv_sub_graph {A : Set (ℕ × ℕ)} (hA : SV A) : ∃ f, A ⊆ graph f := by
  classical
  refine ⟨fun a => if h : ∃ b, (a, b) ∈ A then Classical.choose h else 0, ?_⟩
  rintro ⟨a, b⟩ hab
  have h : ∃ b, (a, b) ∈ A := ⟨b, hab⟩
  show b = (if h : ∃ b, (a, b) ∈ A then Classical.choose h else 0)
  rw [dite_eq_left h]
  exact hA _ hab _ (Classical.choose_spec h) rfl

/-- A set with at most one element. -/
def AtMostOne (S : Set ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, x = y

/-- Exercise 15-26 (a), corrected reading. -/
theorem weak_domain (Φ : Set (ℕ × ℕ) → Set ℕ) (hΦ : Monotone Φ)
    (htot : ∀ f, AtMostOne (Φ (graph f))) : ∀ A, SV A → AtMostOne (Φ A) := by
  intro A hA x hx y hy
  obtain ⟨f, hf⟩ := sv_sub_graph hA
  exact htot f x (hΦ hf hx) y (hΦ hf hy)

/-- Exercise 15-26 (b): a strongly everywhere defined functional is constant. -/
theorem strong_domain_const (Φ : Set (ℕ × ℕ) → Set ℕ) (hΦ : Monotone Φ)
    (h : ∀ A, SV A → ∃ x, Φ A = {x}) : ∀ A, SV A → Φ A = Φ ∅ := by
  have h0 : SV ∅ := fun p hp => absurd hp (Set.notMem_empty p)
  obtain ⟨c, hc⟩ := h ∅ h0
  intro A hA
  obtain ⟨x, hx⟩ := h A hA
  have : c ∈ Φ A := hΦ (Set.empty_subset A) (hc ▸ rfl)
  rw [hx] at this
  rw [hx, hc, this]

/-- The operator of the counterexample: `Φ₀(A) = {0}` if some `⟨0, b⟩ ∈ A`. -/
def Φ₀ (A : Set (ℕ × ℕ)) : Set ℕ := {x | x = 0 ∧ ∃ b, (0, b) ∈ A}

theorem Φ₀_mono : Monotone Φ₀ := by
  rintro A B hAB x ⟨hx, b, hb⟩
  exact ⟨hx, b, hAB hb⟩

/-- The printed reading ("not empty") fails exercise 15-26 (a). -/
theorem printed_fails : (∀ f, (Φ₀ (graph f)).Nonempty) ∧ ¬ (Φ₀ ∅).Nonempty := by
  refine ⟨fun f => ⟨0, rfl, f 0, rfl⟩, ?_⟩
  rintro ⟨x, -, b, hb⟩
  exact hb

/-! ### Theorem 15-XXXI (Friedberg), the choice of `k` -/

section Friedberg

variable (φ : ℕ → ℕ → Option ℕ)

/-- `ψ(x)` converges (the definition in the proof of theorem XXXI). -/
def Dom (x : ℕ) : Prop :=
  (∀ y ≤ x, φ x y = some 0) ∨
    ∃ z, (∃ v, φ x z = some v ∧ v ≠ 0) ∧ (∀ y < z, φ x y = some 0) ∧
      ∃ x' < z, ∀ u ≤ z, φ x' u = φ x u

/-- `g(x) = 0` for `x ≠ n`, `g(n) = k`. -/
def g (n k : ℕ) : ℕ → ℕ := fun y => if y = n then k else 0

/-- `x` is a Gödel number of the total function `f`. -/
def IsIndex (x : ℕ) (f : ℕ → ℕ) : Prop := ∀ y, φ x y = some (f y)

/-- The corrected choice of `k`: `ψ` diverges on every index of `g`. -/
theorem friedberg_corrected (n k : ℕ) (hk : k ≠ 0) (hφ : ∀ x' < n, φ x' n ≠ some k) :
    ∀ x, IsIndex φ x (g n k) → ¬ Dom φ x := by
  intro x hx hD
  have hxn : φ x n = some k := by simpa [g] using hx n
  rcases hD with h1 | ⟨z, ⟨v, hv, hv0⟩, -, x', hx', hagree⟩
  · by_cases hnx : n ≤ x
    · rw [h1 n hnx] at hxn
      exact hk (Option.some.inj hxn).symm
    · exact hφ x (by omega) hxn
  · have hz : z = n := by
      by_contra hzn
      have := hx z
      simp only [g, hzn, ↓reduceIte] at this
      rw [this] at hv
      exact hv0 (Option.some.inj hv).symm
    subst hz
    exact hφ x' hx' ((hagree z le_rfl).trans hxn)

/-- With the corrected choice every index of `g` is `≥ n`. -/
theorem friedberg_indices (n k : ℕ) (hφ : ∀ x' < n, φ x' n ≠ some k) :
    ∀ x, IsIndex φ x (g n k) → n ≤ x := by
  intro x hx
  by_contra hlt
  exact hφ x (by omega) (by simpa [g] using hx n)

/-- For `k = 0` the function `g` is `λx [0]` and `ψ` converges on all its
indices. -/
theorem friedberg_k_zero (n x : ℕ) (hx : IsIndex φ x (g n 0)) : Dom φ x :=
  Or.inl fun y _ => by simpa [g] using hx y

end Friedberg

/-- A numbering for the counterexample: `φ₀ = (0, 1, 5, 5, ...)`,
`φ₂ = g = (0, 1, 0, 0, ...)` (`n = k = 1`), the others nowhere defined. -/
def φc : ℕ → ℕ → Option ℕ := fun x y =>
  if x = 0 then some (if y = 0 then 0 else if y = 1 then 1 else 5)
  else if x = 2 then some (g 1 1 y) else none

/-- The printed choice of `k` does not suffice. -/
theorem friedberg_printed_insufficient :
    (∀ x, IsIndex φc x (g 1 1) → 1 ≤ x) ∧ IsIndex φc 2 (g 1 1) ∧ Dom φc 2 := by
  refine ⟨fun x hx => ?_, fun y => by simp [φc], Or.inr ⟨1, ⟨1, by simp [φc, g], by decide⟩,
    fun y hy => ?_, 0, by decide, fun u hu => ?_⟩⟩
  · by_contra h0
    have hx0 : x = 0 := by omega
    subst hx0
    have := hx 2
    simp [φc, g] at this
  · have : y = 0 := by omega
    subst this
    simp [φc, g]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with rfl | rfl <;> decide

/-! ### Chapter 16: three set-theoretic steps -/

/-- Theorem 16-XXVII as printed (`A' ∩ B = ∅`), with `A = N`. -/
theorem reduction_printed {A B A' B' : Set ℕ} (hA : A = Set.univ) (h2 : B' ⊆ B)
    (hU : A ∪ B = A' ∪ B') (hI : A' ∩ B = ∅) : A' = Bᶜ := by
  ext x
  constructor
  · intro hx hb
    have : x ∈ A' ∩ B := ⟨hx, hb⟩
    rw [hI] at this
    exact this
  · intro hb
    have : x ∈ A ∪ B := Or.inl (hA ▸ Set.mem_univ x)
    rw [hU] at this
    rcases this with h | h
    · exact h
    · exact absurd (h2 h) hb

/-- Exercise 16-46 (a), the hint as corrected. -/
theorem image_ne {T : Set ℕ} {f p : ℕ → ℕ} (hp : Function.Injective p) {y z : ℕ}
    (hy : y ∈ T) (hz : z ∉ T) (h : f y = p z) : f '' T ≠ p '' T := by
  intro heq
  have : f y ∈ p '' T := heq ▸ Set.mem_image_of_mem f hy
  obtain ⟨z', hz', hpz⟩ := this
  rw [h] at hpz
  exact hz (hp hpz ▸ hz')

/-- The printed hint `f(y) ≠ p_x(z)` does not give `f(T) ≠ p_x(T)`. -/
theorem printed_hint_useless :
    ∃ (T : Set ℕ) (f p : ℕ → ℕ), Function.Injective p ∧
      (∃ y ∈ T, ∃ z, z ∉ T ∧ f y ≠ p z) ∧ f '' T = p '' T :=
  ⟨{x | x = 0}, id, id, Function.injective_id,
    ⟨0, rfl, 1, fun h => absurd (h : (1 : ℕ) = 0) (by decide), by decide⟩, rfl⟩

/-- Exercise 16-93 as printed: `D_(β+1) = D_β ∩ (D_β)'` and a union at the
limit give `D_ω = D_0` for every operator `J` in place of the jump. -/
theorem shoenfield_union (J : Set ℕ → Set ℕ) (D : ℕ → Set ℕ)
    (hD : ∀ n, D (n + 1) = D n ∩ J (D n)) : {x | ∃ n, x ∈ D n} = D 0 := by
  have hsub : ∀ n, D n ⊆ D 0 := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => rw [hD n]; exact Set.inter_subset_left.trans ih
  ext x
  exact ⟨fun ⟨n, hn⟩ => hsub n hn, fun h => ⟨0, h⟩⟩

end RogersRecursive.Ch15_16.Functionals

#print axioms RogersRecursive.Ch15_16.Functionals.weak_domain
#print axioms RogersRecursive.Ch15_16.Functionals.strong_domain_const
#print axioms RogersRecursive.Ch15_16.Functionals.printed_fails
#print axioms RogersRecursive.Ch15_16.Functionals.friedberg_corrected
#print axioms RogersRecursive.Ch15_16.Functionals.friedberg_indices
#print axioms RogersRecursive.Ch15_16.Functionals.friedberg_k_zero
#print axioms RogersRecursive.Ch15_16.Functionals.friedberg_printed_insufficient
#print axioms RogersRecursive.Ch15_16.Functionals.reduction_printed
#print axioms RogersRecursive.Ch15_16.Functionals.image_ne
#print axioms RogersRecursive.Ch15_16.Functionals.printed_hint_useless
#print axioms RogersRecursive.Ch15_16.Functionals.shoenfield_union
