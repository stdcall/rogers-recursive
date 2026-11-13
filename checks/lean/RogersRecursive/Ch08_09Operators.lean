import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Fin.Basic

/-!
# Enumeration operators and the set (*) of theorem 9-XXIII

Places in the book (§§ 9.7-9.8, pp. 191-197):

* The definition of `A ≤_e B` by `z` and of `Φ_z` (p. 191), and theorem
  9-XXI (`th:enumeration-operator-properties`, p. 193): `Φ` is monotone
  (`Phi_mono`) and continuous (`Phi_cont`).  Here `Φ` is built from any set
  `W` of pairs `(x, u)` and any assignment `D` of finite sets to indices.
* Theorem 9-XXII (`th:total-domain-recursive-operator`, p. 195), in a
  set-theoretic form: a monotone map of sets of pairs that sends the graph
  of every total function to a single-valued set sends every single-valued
  set to a single-valued set (`total_domain`).  (The book extends a finite
  single-valued `D`; extending the single-valued set itself also works.)
* Theorem 9-XXIII (`th:fundamental-operator-theorem`, pp. 196-197), the set
  (*) (`eq:operator-extension-set`) as corrected: `⟨⟨x, y⟩, t⟩ ∈ W_σ(z)` if
  `D_t` is single-valued and for some element `⟨⟨x, y⟩, s⟩` of `W_z`,
  `D_s ⊂ D_t` and `D_(s') ∪ D_t` is not single-valued for every preceding
  `⟨⟨x, y'⟩, s'⟩` (`Star`).  The lemma `lem:operator-extension-monotone`
  (`star_mono`) and the first part of the proof, that `Φ_σ(z)` maps
  single-valued sets to single-valued sets (`star_sv`, `phiSigma_sv`).
  As printed (`D_t ⊂ D_s` and `D_(s') ∪ D_s`, `StarPrinted`) the lemma
  fails for `W_z = (⟨⟨0, 0⟩, {⟨0, 0⟩}⟩)` (`printed_not_mono`) and the image
  of the single-valued `∅` is not single-valued for the identity operator
  on the argument 0 (`printed_not_sv`).

Notation: pairs are `ℕ × ℕ` (the codes `τ(a, b)` of § 5.3, `τ` is a
bijection); `W_z` in its standard order is a list of `Entry`; `D_t` is a
`Finset (ℕ × ℕ)`.

Not covered: recursive enumerability of `W_σ(z)` and the function `σ`;
the last part of the proof (`Φ_σ(z)(τ(f)) = Φ_z(τ(f))` when the latter is
single-valued), checked on finite models in
`checks/haskell/CheckCh09Operators.hs`; theorems 9-XX, 9-XXIV.
-/

namespace RogersRecursive.Ch08_09.Operators

/-! ### Enumeration operators (theorem 9-XXI) -/

/-- `Φ(X) = {x | ∃ u, (x, u) ∈ W ∧ D u ⊆ X}`. -/
def Phi (D : ℕ → Finset ℕ) (W : Set (ℕ × ℕ)) (X : Set ℕ) : Set ℕ :=
  {x | ∃ u, (x, u) ∈ W ∧ ↑(D u) ⊆ X}

theorem Phi_mono (D : ℕ → Finset ℕ) (W : Set (ℕ × ℕ)) {X Y : Set ℕ}
    (h : X ⊆ Y) : Phi D W X ⊆ Phi D W Y := by
  rintro x ⟨u, hu, hD⟩
  exact ⟨u, hu, hD.trans h⟩

theorem Phi_cont (D : ℕ → Finset ℕ) (W : Set (ℕ × ℕ)) {X : Set ℕ} {x : ℕ}
    (h : x ∈ Phi D W X) : ∃ F : Finset ℕ, ↑F ⊆ X ∧ x ∈ Phi D W ↑F := by
  obtain ⟨u, hu, hD⟩ := h
  exact ⟨D u, hD, u, hu, le_refl _⟩

/-! ### Single-valued sets (theorem 9-XXII) -/

/-- A single-valued set of pairs. -/
def SV (A : Set (ℕ × ℕ)) : Prop := ∀ p ∈ A, ∀ q ∈ A, p.1 = q.1 → p.2 = q.2

/-- The graph of a total function. -/
def graph (f : ℕ → ℕ) : Set (ℕ × ℕ) := {p | p.2 = f p.1}

theorem SV_mono {A B : Set (ℕ × ℕ)} (h : A ⊆ B) (hB : SV B) : SV A :=
  fun p hp q hq hpq => hB p (h hp) q (h hq) hpq

/-- Theorem 9-XXII: if `F` is monotone and `F (graph f)` is single-valued
for all total `f`, then `F A` is single-valued for all single-valued `A`. -/
theorem total_domain (F : Set (ℕ × ℕ) → Set (ℕ × ℕ)) (hF : Monotone F)
    (htot : ∀ f, SV (F (graph f))) : ∀ A, SV A → SV (F A) := by
  classical
  intro A hA
  let f : ℕ → ℕ := fun a => if h : ∃ b, (a, b) ∈ A then Classical.choose h else 0
  have hsub : A ⊆ graph f := by
    rintro ⟨a, b⟩ hab
    have h : ∃ b, (a, b) ∈ A := ⟨b, hab⟩
    show b = f a
    simp only [f, h, ↓reduceDIte]
    exact hA (a, b) hab (a, _) (Classical.choose_spec h) rfl
  exact SV_mono (hF hsub) (htot f)

/-- The enumeration operator on sets of pairs given by `W` (pairs of an
output pair and a finite set) is monotone, so theorem 9-XXII applies. -/
def PhiP (W : Set ((ℕ × ℕ) × Finset (ℕ × ℕ))) (A : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  {p | ∃ d, (p, d) ∈ W ∧ ↑d ⊆ A}

theorem PhiP_mono (W : Set ((ℕ × ℕ) × Finset (ℕ × ℕ))) : Monotone (PhiP W) := by
  intro A B h p ⟨d, hd, hdA⟩
  exact ⟨d, hd, hdA.trans h⟩

theorem total_domain_PhiP (W : Set ((ℕ × ℕ) × Finset (ℕ × ℕ)))
    (htot : ∀ f, SV (PhiP W (graph f))) : ∀ A, SV A → SV (PhiP W A) :=
  total_domain (PhiP W) (PhiP_mono W) htot

/-! ### The set (*) of theorem 9-XXIII -/

/-- A finite single-valued set. -/
def SVf (t : Finset (ℕ × ℕ)) : Prop := ∀ p ∈ t, ∀ q ∈ t, p.1 = q.1 → p.2 = q.2

theorem SVf_mono {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) (ht : SVf t) : SVf s :=
  fun p hp q hq hpq => ht p (h hp) q (h hq) hpq

/-- An element `⟨⟨x, y⟩, s⟩` of `W_z`. -/
structure Entry where
  x : ℕ
  y : ℕ
  s : Finset (ℕ × ℕ)

/-- `⟨⟨x, y⟩, t⟩ ∈ W_σ(z)`, by (*) as corrected. -/
def Star (W : List Entry) (x y : ℕ) (t : Finset (ℕ × ℕ)) : Prop :=
  SVf t ∧ ∃ i : Fin W.length, W[i].x = x ∧ W[i].y = y ∧ W[i].s ⊆ t ∧
    ∀ j : Fin W.length, j < i → W[j].x = x → ¬ SVf (W[j].s ∪ t)

/-- `⟨⟨x, y⟩, t⟩ ∈ W_σ(z)`, by (*) as printed. -/
def StarPrinted (W : List Entry) (x y : ℕ) (t : Finset (ℕ × ℕ)) : Prop :=
  SVf t ∧ ∃ i : Fin W.length, W[i].x = x ∧ W[i].y = y ∧ t ⊆ W[i].s ∧
    ∀ j : Fin W.length, j < i → W[j].x = x → ¬ SVf (W[j].s ∪ W[i].s)

/-- The lemma `lem:operator-extension-monotone`. -/
theorem star_mono {W : List Entry} {x y : ℕ} {t t₁ : Finset (ℕ × ℕ)}
    (h : Star W x y t) (ht : t ⊆ t₁) (h₁ : SVf t₁) : Star W x y t₁ := by
  obtain ⟨-, i, hx, hy, hs, hpre⟩ := h
  refine ⟨h₁, i, hx, hy, hs.trans ht, fun j hj hjx hsv => ?_⟩
  exact hpre j hj hjx (SVf_mono (Finset.union_subset_union (le_refl _) ht) hsv)

/-- Two elements of `W_σ(z)` with the same `x` and compatible `D_t` have
the same `y`. -/
theorem star_sv {W : List Entry} {x y₁ y₂ : ℕ} {t₁ t₂ : Finset (ℕ × ℕ)}
    (h₁ : Star W x y₁ t₁) (h₂ : Star W x y₂ t₂) (h : SVf (t₁ ∪ t₂)) : y₁ = y₂ := by
  obtain ⟨-, i, hix, hiy, his, hi⟩ := h₁
  obtain ⟨-, j, hjx, hjy, hjs, hj⟩ := h₂
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact absurd (SVf_mono (Finset.union_subset_union his (le_refl _)) h) (hj i hij hix)
  · rw [← hiy, ← hjy]
  · have h' : SVf (t₂ ∪ t₁) := by rwa [Finset.union_comm]
    exact absurd (SVf_mono (Finset.union_subset_union hjs (le_refl _)) h') (hi j hji hjx)

/-- `Φ_σ(z)(A)`. -/
def PhiSigma (W : List Entry) (A : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  {p | ∃ t : Finset (ℕ × ℕ), ↑t ⊆ A ∧ Star W p.1 p.2 t}

/-- The first part of the proof of theorem 9-XXIII: `Φ_σ(z)` maps
single-valued sets to single-valued sets. -/
theorem phiSigma_sv (W : List Entry) {A : Set (ℕ × ℕ)} (hA : SV A) :
    SV (PhiSigma W A) := by
  rintro ⟨x, y₁⟩ ⟨t₁, ht₁, h₁⟩ ⟨x', y₂⟩ ⟨t₂, ht₂, h₂⟩ hxx
  simp only at hxx h₁ h₂ ⊢
  subst hxx
  have hsv : SVf (t₁ ∪ t₂) := by
    intro p hp q hq hpq
    have hp' : p ∈ A := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ht₁ hp
      · exact ht₂ hp
    have hq' : q ∈ A := by
      rcases Finset.mem_union.mp hq with hq | hq
      · exact ht₁ hq
      · exact ht₂ hq
    exact hA p hp' q hq' hpq
  exact star_sv h₁ h₂ hsv

/-- `W_z = (⟨⟨0, 0⟩, {⟨0, 0⟩}⟩)`. -/
def w₁ : List Entry := [⟨0, 0, {(0, 0)}⟩]

/-- As printed the lemma fails: `⟨⟨0, 0⟩, ∅⟩ ∈ W_σ(z)`, `∅ ⊂ {⟨1, 0⟩}`,
`{⟨1, 0⟩}` is single-valued, but `⟨⟨0, 0⟩, {⟨1, 0⟩}⟩ ∉ W_σ(z)`. -/
theorem printed_not_mono :
    StarPrinted w₁ 0 0 ∅ ∧ SVf {(1, 0)} ∧ ¬ StarPrinted w₁ 0 0 {(1, 0)} := by
  refine ⟨⟨fun p hp => absurd hp (Finset.notMem_empty p), ⟨0, by simp [w₁]⟩, rfl, rfl,
      Finset.empty_subset _, fun j hj => absurd (show j.val < 0 from hj) (Nat.not_lt_zero _)⟩, ?_, ?_⟩
  · intro p hp q hq _
    rw [Finset.mem_singleton] at hp hq
    rw [hp, hq]
  · rintro ⟨-, i, -, -, hs, -⟩
    have hv : i.val = 0 := by have := i.isLt; simp [w₁] at this; omega
    have hi : i = ⟨0, by simp [w₁]⟩ := Fin.ext hv
    subst hi
    have : ((1, 0) : ℕ × ℕ) ∈ ({(0, 0)} : Finset (ℕ × ℕ)) := hs (Finset.mem_singleton_self _)
    simp at this

/-- The identity operator on the argument 0 and the values 0, 1. -/
def w₂ : List Entry := [⟨0, 0, {(0, 0)}⟩, ⟨0, 1, {(0, 1)}⟩]

/-- As printed `Φ_σ(z)(∅)` contains `⟨0, 0⟩` and `⟨0, 1⟩`: the image of the
single-valued set `∅` is not single-valued. -/
theorem printed_not_sv : StarPrinted w₂ 0 0 ∅ ∧ StarPrinted w₂ 0 1 ∅ := by
  have hsv : SVf ∅ := fun p hp => absurd hp (Finset.notMem_empty p)
  refine ⟨⟨hsv, ⟨0, by simp [w₂]⟩, rfl, rfl, Finset.empty_subset _,
      fun j hj => absurd (show j.val < 0 from hj) (Nat.not_lt_zero _)⟩, ⟨hsv, ⟨1, by simp [w₂]⟩, rfl, rfl,
      Finset.empty_subset _, ?_⟩⟩
  intro j hj _ hj'
  have hv : j.val = 0 := by have : j.val < 1 := hj; omega
  have hj0 : j = ⟨0, by simp [w₂]⟩ := Fin.ext hv
  subst hj0
  have := hj' (0, 0) (by simp [w₂]) (0, 1) (by simp [w₂]) rfl
  simp at this

end RogersRecursive.Ch08_09.Operators

#print axioms RogersRecursive.Ch08_09.Operators.Phi_mono
#print axioms RogersRecursive.Ch08_09.Operators.Phi_cont
#print axioms RogersRecursive.Ch08_09.Operators.SV_mono
#print axioms RogersRecursive.Ch08_09.Operators.total_domain
#print axioms RogersRecursive.Ch08_09.Operators.PhiP_mono
#print axioms RogersRecursive.Ch08_09.Operators.total_domain_PhiP
#print axioms RogersRecursive.Ch08_09.Operators.SVf_mono
#print axioms RogersRecursive.Ch08_09.Operators.star_mono
#print axioms RogersRecursive.Ch08_09.Operators.star_sv
#print axioms RogersRecursive.Ch08_09.Operators.phiSigma_sv
#print axioms RogersRecursive.Ch08_09.Operators.printed_not_mono
#print axioms RogersRecursive.Ch08_09.Operators.printed_not_sv
