/-
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная
вычислимость» (Мир, 1972), chapter 4: theorem I (§ 4.2, pp. 74-75,
the recursive permutations form a group), theorem II (§ 4.3, p. 76,
φ ≡ ψ iff φ = f⁻¹ψf), theorem III and corollaries (a), (b) (§ 4.5,
p. 78, universality is invariant under resemblance).

Notation.  A partial function is `Nat → Option Nat` (`none`: diverges);
`φ x` is φ_x of the fixed numbering.  A recursive permutation is a
bijection of Nat (`Nat ≃ Nat` in theorems II, III); composition ψφ of
the book is `fun x => (φ x).bind ψ`, and for total f, g it is
`fun z => (ψ (h z)).map g` etc.  `image f R` is the book's f(R) =
{⟨f(x), f(y)⟩ | ⟨x, y⟩ ∈ R} for a binary relation R (p. 76), `graph φ`
the relation of φ.  As in Ch01_04Diagonal.lean the recursiveness facts
that the book takes from Church's thesis, the s-m-n theorem and theorem
1-VI are explicit hypotheses on arbitrary classes `Rec1`, `Rec2`, `PR`.

What is proved:
* theorem I: the search "compute f(0), f(1), ... until f(n) = x" gives
  the inverse of a bijection f (both sides); with `Rec1` closed under
  composition (theorem 1-VI) and under this search (Church's thesis),
  {f ∈ Rec1 | f bijective} is closed under composition and inverse;
* theorem II, for every bijection f and partial functions φ, ψ:
  graph ψ = f(graph φ) iff φ = f⁻¹ψf (in both directions, as in the book's
  proof);
* theorem III: if ψ is universal (ψ ∈ PR, φ_x = λy[ψ f(x, y)] with f ∈
  Rec2), g, h recursive permutations, k recursive with φ_(k(x)) = gφ_x
  (s-m-n), then η = g⁻¹ψh is universal with f^ = λxy[h⁻¹ f(k(x), y)] (the
  computation of p. 78); corollaries (a) g⁻¹ψg and (b) gψ.

Not covered: that the classes are those of recursive functions; the
recursive permutations of § 4.2 beyond these closure properties.
-/
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.Defs

namespace RogersRecursive.Ch01_04.Invariance

abbrev PFn := Nat → Option Nat

/-! Theorem I. -/

section Search

open Classical

/-- f⁻¹(x): compute f(0), f(1), ... until f(n) = x (p. 75). -/
noncomputable def search (f : Nat → Nat) (hs : Function.Surjective f) (x : Nat) : Nat :=
  Nat.find (hs x)

theorem search_right (f : Nat → Nat) (hs : Function.Surjective f) (x : Nat) :
    f (search f hs x) = x :=
  Nat.find_spec (hs x)

theorem search_left (f : Nat → Nat) (hf : Function.Injective f)
    (hs : Function.Surjective f) (n : Nat) : search f hs (f n) = n :=
  hf (search_right f hs (f n))

theorem search_bijective (f : Nat → Nat) (hf : Function.Bijective f) :
    Function.Bijective (search f hf.2) :=
  ⟨fun a b hab => by
      rw [← search_right f hf.2 a, ← search_right f hf.2 b, hab],
    fun n => ⟨f n, search_left f hf.1 hf.2 n⟩⟩

/-- 𝒢* is closed under composition and inverse. -/
theorem group_closure (Rec1 : Set (Nat → Nat))
    (hcomp : ∀ f ∈ Rec1, ∀ g ∈ Rec1, (fun x => f (g x)) ∈ Rec1)
    (hsearch : ∀ f ∈ Rec1, ∀ hs : Function.Surjective f, search f hs ∈ Rec1)
    (f g : Nat → Nat) (hfR : f ∈ Rec1) (hgR : g ∈ Rec1)
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    ((fun x => f (g x)) ∈ Rec1 ∧ Function.Bijective (fun x => f (g x))) ∧
      (search f hf.2 ∈ Rec1 ∧ Function.Bijective (search f hf.2) ∧
        (∀ x, f (search f hf.2 x) = x) ∧ ∀ n, search f hf.2 (f n) = n) :=
  ⟨⟨hcomp f hfR g hgR, hf.comp hg⟩,
    ⟨hsearch f hfR hf.2, search_bijective f hf, search_right f hf.2,
      search_left f hf.1 hf.2⟩⟩

end Search

/-! Theorem II. -/

def graph (φ : PFn) : Nat → Nat → Prop := fun x y => φ x = some y

/-- f(R) for a binary relation R (p. 76). -/
def image (f : Nat → Nat) (R : Nat → Nat → Prop) : Nat → Nat → Prop :=
  fun u v => ∃ x y, R x y ∧ u = f x ∧ v = f y

theorem isomorphic_functions (f : Nat ≃ Nat) (φ ψ : PFn) :
    graph ψ = image f (graph φ) ↔ ∀ x, φ x = (ψ (f x)).map f.symm := by
  constructor
  · intro h x
    cases hx : φ x with
    | some y =>
      have : graph ψ (f x) (f y) := by rw [h]; exact ⟨x, y, hx, rfl, rfl⟩
      simp only [graph] at this
      simp [this]
    | none =>
      cases hv : ψ (f x) with
      | none => rfl
      | some v =>
        have : graph ψ (f x) v := hv
        rw [h] at this
        obtain ⟨x', y', hxy, hu, -⟩ := this
        rw [f.injective hu] at hx
        simp only [graph] at hxy
        rw [hx] at hxy
        cases hxy
  · intro h
    funext u v
    apply propext
    constructor
    · intro huv
      refine ⟨f.symm u, f.symm v, ?_, by simp, by simp⟩
      simp only [graph] at huv ⊢
      rw [h, Equiv.apply_symm_apply, huv]
      rfl
    · rintro ⟨x, y, hxy, rfl, rfl⟩
      simp only [graph] at hxy ⊢
      rw [h] at hxy
      cases hw : ψ (f x) with
      | none => rw [hw] at hxy; cases hxy
      | some w =>
        rw [hw] at hxy
        simp only [Option.map_some, Option.some.injEq] at hxy
        rw [← hxy, Equiv.apply_symm_apply]

/-! Theorem III. -/

/-- ψ is universal (definition of § 4.5). -/
def Universal (φ : Nat → PFn) (PR : Set PFn) (Rec2 : Set (Nat → Nat → Nat)) (ψ : PFn) :
    Prop :=
  ψ ∈ PR ∧ ∃ f ∈ Rec2, ∀ x y, φ x y = ψ (f x y)

/-- The computation of p. 78: λy[η f^(x, y)] = φ_x. -/
theorem eta_identity (φ : Nat → PFn) (ψ : PFn) (f : Nat → Nat → Nat)
    (hf : ∀ x y, φ x y = ψ (f x y)) (g h : Nat ≃ Nat) (k : Nat → Nat)
    (hk : ∀ x y, φ (k x) y = (φ x y).map g) (x y : Nat) :
    (ψ (h (h.symm (f (k x) y)))).map g.symm = φ x y := by
  rw [Equiv.apply_symm_apply, ← hf, hk, Option.map_map]
  cases φ x y <;> simp

theorem universality_invariance (φ : Nat → PFn) (PR : Set PFn) (Rec1 : Set (Nat → Nat))
    (Rec2 : Set (Nat → Nat → Nat)) (g h : Nat ≃ Nat)
    (hPR : ∀ ψ ∈ PR, (fun z => (ψ (h z)).map g.symm) ∈ PR)
    (hsmn : ∃ k ∈ Rec1, ∀ x y, φ (k x) y = (φ x y).map g)
    (hRec2 : ∀ f ∈ Rec2, ∀ k ∈ Rec1, (fun x y => h.symm (f (k x) y)) ∈ Rec2)
    (ψ : PFn) (hψ : Universal φ PR Rec2 ψ) :
    Universal φ PR Rec2 (fun z => (ψ (h z)).map g.symm) := by
  obtain ⟨hψPR, f, hfR, hf⟩ := hψ
  obtain ⟨k, hkR, hk⟩ := hsmn
  exact ⟨hPR ψ hψPR, _, hRec2 f hfR k hkR,
    fun x y => (eta_identity φ ψ f hf g h k hk x y).symm⟩

/-- Corollary (a): g⁻¹ψg. -/
theorem universality_recursive_invariance (φ : Nat → PFn) (PR : Set PFn)
    (Rec1 : Set (Nat → Nat)) (Rec2 : Set (Nat → Nat → Nat)) (g : Nat ≃ Nat)
    (hPR : ∀ ψ ∈ PR, (fun z => (ψ (g z)).map g.symm) ∈ PR)
    (hsmn : ∃ k ∈ Rec1, ∀ x y, φ (k x) y = (φ x y).map g)
    (hRec2 : ∀ f ∈ Rec2, ∀ k ∈ Rec1, (fun x y => g.symm (f (k x) y)) ∈ Rec2)
    (ψ : PFn) (hψ : Universal φ PR Rec2 ψ) :
    Universal φ PR Rec2 (fun z => (ψ (g z)).map g.symm) :=
  universality_invariance φ PR Rec1 Rec2 g g hPR hsmn hRec2 ψ hψ

/-- Corollary (b): gψ (theorem III with g⁻¹ for g and the identity for h). -/
theorem universality_range_permutation (φ : Nat → PFn) (PR : Set PFn)
    (Rec1 : Set (Nat → Nat)) (Rec2 : Set (Nat → Nat → Nat)) (g : Nat ≃ Nat)
    (hPR : ∀ ψ ∈ PR, (fun z => (ψ z).map g) ∈ PR)
    (hsmn : ∃ k ∈ Rec1, ∀ x y, φ (k x) y = (φ x y).map g.symm)
    (hRec2 : ∀ f ∈ Rec2, ∀ k ∈ Rec1, (fun x y => f (k x) y) ∈ Rec2)
    (ψ : PFn) (hψ : Universal φ PR Rec2 ψ) :
    Universal φ PR Rec2 (fun z => (ψ z).map g) :=
  universality_invariance φ PR Rec1 Rec2 g.symm (Equiv.refl Nat) hPR hsmn hRec2 ψ hψ

end RogersRecursive.Ch01_04.Invariance

#print axioms RogersRecursive.Ch01_04.Invariance.search_right
#print axioms RogersRecursive.Ch01_04.Invariance.search_left
#print axioms RogersRecursive.Ch01_04.Invariance.search_bijective
#print axioms RogersRecursive.Ch01_04.Invariance.group_closure
#print axioms RogersRecursive.Ch01_04.Invariance.isomorphic_functions
#print axioms RogersRecursive.Ch01_04.Invariance.eta_identity
#print axioms RogersRecursive.Ch01_04.Invariance.universality_invariance
#print axioms RogersRecursive.Ch01_04.Invariance.universality_recursive_invariance
#print axioms RogersRecursive.Ch01_04.Invariance.universality_range_permutation
