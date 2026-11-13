/-
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная
вычислимость» (Мир, 1972), chapter 12: theorem I (quotient lattices,
§ 12.1, pp. 288-290) with exercises 12-3, 12-4, 12-6, 12-7, 12-8, and the
diagonal step of Lachlan's theorem XX (§ 12.6, p. 315).

Notation.  An ideal of a lattice is, as on p. 288, a nonempty set closed
under ⊔ and under a ⊓ (·) for every a; a dual ideal dually.  `rel I a b`
is a ≈_I b: (∃ c₁ c₂ ∈ I) [a ⊔ c₁ = b ⊔ c₂].

What is proved.  Theorem I (a): in a distributive lattice ≈_I is an
equivalence (exercise 12-7) compatible with ⊔ and ⊓ (the congruence step
of the proof, here through a single c: a ≈_I b ⇔ (∃ c ∈ I) a ⊔ c = b ⊔ c),
I is an equivalence class and the least one (exercise 12-8), and
exercise 12-6 (the order of L/I).  Theorem I (c) in a Boolean algebra: the
complement respects ≈_I, I is an ideal iff D = {a | aᶜ ∈ I} is a dual
ideal, and then ≈_I and ≈_D coincide (the chain of p. 290, with its
corrected step aᶜ ⊔ c₁ = (a ⊓ c₁ᶜ)ᶜ).  Exercise 12-3 (complements are
unique in a distributive lattice, by the hint) and exercise 12-4 (each
distributive law implies the other, in any lattice).  Theorem XX, ⇐:
for W : ℕ → Set ℕ (the r.e. sets), A and f with the W_(f(x)) pairwise
disjoint and each meeting A-bar, B = A ∪ ⋃_x (W_x ∩ W_(f(x))) has
A ∪ (N − B) different from every W_y.

Not covered: recursive enumerability (W is an arbitrary family); theorem
I (b), (d) (checked on finite lattices in checks/haskell/CheckCh12Lattice.hs).
-/
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Set.Basic

namespace RogersRecursive.Ch10_12.Lattice

section Distributive

variable {L : Type*} [DistribLattice L]

/-- An ideal (p. 288). -/
structure IsIdeal (I : Set L) : Prop where
  nonempty : ∃ c, c ∈ I
  sup_mem : ∀ c₁ c₂, c₁ ∈ I → c₂ ∈ I → c₁ ⊔ c₂ ∈ I
  inf_mem : ∀ a c, c ∈ I → a ⊓ c ∈ I

/-- a ≈_I b. -/
def rel (I : Set L) (a b : L) : Prop := ∃ c₁ ∈ I, ∃ c₂ ∈ I, a ⊔ c₁ = b ⊔ c₂

variable {I : Set L}

theorem rel_iff_single (hI : IsIdeal I) (a b : L) :
    rel I a b ↔ ∃ c ∈ I, a ⊔ c = b ⊔ c := by
  constructor
  · rintro ⟨c₁, h₁, c₂, h₂, e⟩
    refine ⟨c₁ ⊔ c₂, hI.sup_mem _ _ h₁ h₂, ?_⟩
    calc a ⊔ (c₁ ⊔ c₂) = (a ⊔ c₁) ⊔ c₂ := (sup_assoc _ _ _).symm
      _ = (b ⊔ c₂) ⊔ c₂ := by rw [e]
      _ = b ⊔ c₂ := by rw [sup_assoc, sup_idem]
      _ = (b ⊔ c₂) ⊔ c₁ := by rw [← e, sup_assoc, sup_idem]
      _ = b ⊔ (c₁ ⊔ c₂) := by rw [sup_assoc, sup_comm c₂ c₁]
  · rintro ⟨c, h, e⟩
    exact ⟨c, h, c, h, e⟩

/-- Exercise 12-7: ≈_I is an equivalence. -/
theorem rel_equivalence (hI : IsIdeal I) : Equivalence (rel I) := by
  obtain ⟨c₀, h₀⟩ := hI.nonempty
  refine ⟨fun a => ⟨c₀, h₀, c₀, h₀, rfl⟩, fun ⟨c₁, h₁, c₂, h₂, e⟩ => ⟨c₂, h₂, c₁, h₁, e.symm⟩, ?_⟩
  intro a b d hab hbd
  obtain ⟨c, hc, e₁⟩ := (rel_iff_single hI a b).1 hab
  obtain ⟨c', hc', e₂⟩ := (rel_iff_single hI b d).1 hbd
  refine (rel_iff_single hI a d).2 ⟨c ⊔ c', hI.sup_mem _ _ hc hc', ?_⟩
  calc a ⊔ (c ⊔ c') = (a ⊔ c) ⊔ c' := (sup_assoc _ _ _).symm
    _ = (b ⊔ c) ⊔ c' := by rw [e₁]
    _ = (b ⊔ c') ⊔ c := by rw [sup_assoc, sup_comm c c', ← sup_assoc]
    _ = (d ⊔ c') ⊔ c := by rw [e₂]
    _ = d ⊔ (c ⊔ c') := by rw [sup_assoc, sup_comm c' c]

/-- Theorem I (a): ⊔ respects ≈_I. -/
theorem rel_sup (hI : IsIdeal I) {a₁ a₂ b₁ b₂ : L} (ha : rel I a₁ a₂) (hb : rel I b₁ b₂) :
    rel I (a₁ ⊔ b₁) (a₂ ⊔ b₂) := by
  obtain ⟨c, hc, e₁⟩ := (rel_iff_single hI _ _).1 ha
  obtain ⟨c', hc', e₂⟩ := (rel_iff_single hI _ _).1 hb
  refine (rel_iff_single hI _ _).2 ⟨c ⊔ c', hI.sup_mem _ _ hc hc', ?_⟩
  calc a₁ ⊔ b₁ ⊔ (c ⊔ c') = (a₁ ⊔ c) ⊔ (b₁ ⊔ c') := by
        simp only [sup_assoc, sup_left_comm b₁ c c']
    _ = (a₂ ⊔ c) ⊔ (b₂ ⊔ c') := by rw [e₁, e₂]
    _ = a₂ ⊔ b₂ ⊔ (c ⊔ c') := by simp only [sup_assoc, sup_left_comm b₂ c c']

/-- Theorem I (a): ⊓ respects ≈_I (by distributivity). -/
theorem rel_inf (hI : IsIdeal I) {a₁ a₂ b₁ b₂ : L} (ha : rel I a₁ a₂) (hb : rel I b₁ b₂) :
    rel I (a₁ ⊓ b₁) (a₂ ⊓ b₂) := by
  obtain ⟨c, hc, e₁⟩ := (rel_iff_single hI _ _).1 ha
  obtain ⟨c', hc', e₂⟩ := (rel_iff_single hI _ _).1 hb
  have k₁ : a₁ ⊔ (c ⊔ c') = a₂ ⊔ (c ⊔ c') := by rw [← sup_assoc, e₁, sup_assoc]
  have k₂ : b₁ ⊔ (c ⊔ c') = b₂ ⊔ (c ⊔ c') := by
    rw [sup_comm c c', ← sup_assoc, e₂, sup_assoc]
  refine (rel_iff_single hI _ _).2 ⟨c ⊔ c', hI.sup_mem _ _ hc hc', ?_⟩
  rw [sup_inf_right, sup_inf_right, k₁, k₂]

/-- Exercise 12-8: I is an equivalence class ... -/
theorem ideal_is_class (hI : IsIdeal I) {c : L} (hc : c ∈ I) (a : L) : rel I a c ↔ a ∈ I := by
  constructor
  · intro h
    obtain ⟨e, he, k⟩ := (rel_iff_single hI _ _).1 h
    have hs : a ⊔ e ∈ I := by rw [k]; exact hI.sup_mem _ _ hc he
    have := hI.inf_mem a _ hs
    rwa [inf_sup_self] at this
  · intro ha
    exact ⟨c, hc, a, ha, sup_comm a c⟩

/-- ... and the zero of L/I: [c] ⊔ [a] = [a]. -/
theorem ideal_is_zero {c : L} (hc : c ∈ I) (a : L) : rel I (c ⊔ a) a :=
  ⟨c, hc, c, hc, by rw [sup_comm c a, sup_assoc, sup_idem]⟩

/-- Exercise 12-6: [a] ≤ [b] in L/I (i.e. [a ⊔ b] = [b]) iff a ≤ b ⊔ c
for some c ∈ I. -/
theorem quotient_order (hI : IsIdeal I) (a b : L) :
    rel I (a ⊔ b) b ↔ ∃ c ∈ I, a ≤ b ⊔ c := by
  rw [rel_iff_single hI]
  constructor
  · rintro ⟨c, hc, e⟩
    refine ⟨c, hc, ?_⟩
    calc a ≤ a ⊔ b ⊔ c := le_sup_of_le_left le_sup_left
      _ = b ⊔ c := e
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, le_antisymm ?_ (sup_le_sup_right le_sup_right c)⟩
    exact sup_le (sup_le h le_sup_left) le_sup_right

/-- Exercise 12-4: each distributive law implies the other (in any
lattice; here the first gives the second). -/
theorem distrib_sup_to_inf {M : Type*} [Lattice M]
    (h : ∀ a b c : M, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)) (a b c : M) :
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  calc a ⊓ (b ⊔ c) = a ⊓ (c ⊔ b) := by rw [sup_comm]
    _ = (a ⊓ (c ⊔ a)) ⊓ (c ⊔ b) := by rw [inf_sup_self' a c]
    _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := inf_assoc _ _ _
    _ = a ⊓ (c ⊔ (a ⊓ b)) := by rw [h c a b]
    _ = a ⊓ ((a ⊓ b) ⊔ c) := by rw [sup_comm]
    _ = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c) := by rw [inf_sup_self'']
    _ = (a ⊓ b) ⊔ (a ⊓ c) := (h _ _ _).symm
  where
    inf_sup_self' (a c : M) : a ⊓ (c ⊔ a) = a := by rw [sup_comm]; exact inf_sup_self
    inf_sup_self'' : (a ⊓ b) ⊔ a = a := by rw [sup_comm]; exact sup_inf_self

/-- Exercise 12-4, the other direction. -/
theorem distrib_inf_to_sup {M : Type*} [Lattice M]
    (h : ∀ a b c : M, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)) (a b c : M) :
    a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  calc a ⊔ (b ⊓ c) = a ⊔ (c ⊓ b) := by rw [inf_comm]
    _ = (a ⊔ (c ⊓ a)) ⊔ (c ⊓ b) := by rw [sup_inf_self' a c]
    _ = a ⊔ ((c ⊓ a) ⊔ (c ⊓ b)) := sup_assoc _ _ _
    _ = a ⊔ (c ⊓ (a ⊔ b)) := by rw [h c a b]
    _ = a ⊔ ((a ⊔ b) ⊓ c) := by rw [inf_comm]
    _ = ((a ⊔ b) ⊓ a) ⊔ ((a ⊔ b) ⊓ c) := by rw [sup_inf_self'']
    _ = (a ⊔ b) ⊓ (a ⊔ c) := (h _ _ _).symm
  where
    sup_inf_self' (a c : M) : a ⊔ (c ⊓ a) = a := by rw [inf_comm]; exact sup_inf_self
    sup_inf_self'' : (a ⊔ b) ⊓ a = a := by rw [inf_comm]; exact inf_sup_self

end Distributive

/-- Exercise 12-3 (by the hint): complements are unique in a distributive
lattice with 0 and 1. -/
theorem complement_unique {L : Type*} [DistribLattice L] [BoundedOrder L] {a b c : L}
    (hb₁ : a ⊓ b = ⊥) (hb₂ : a ⊔ b = ⊤) (hc₁ : a ⊓ c = ⊥) (hc₂ : a ⊔ c = ⊤) : b = c := by
  have e₁ : b = b ⊓ c := by
    calc b = b ⊓ (a ⊔ c) := by rw [hc₂, inf_top_eq]
      _ = (b ⊓ a) ⊔ (b ⊓ c) := inf_sup_left _ _ _
      _ = b ⊓ c := by rw [inf_comm b a, hb₁, bot_sup_eq]
  have e₂ : c = c ⊓ b := by
    calc c = c ⊓ (a ⊔ b) := by rw [hb₂, inf_top_eq]
      _ = (c ⊓ a) ⊔ (c ⊓ b) := inf_sup_left _ _ _
      _ = c ⊓ b := by rw [inf_comm c a, hc₁, bot_sup_eq]
  rw [e₁, inf_comm]
  exact e₂.symm

section Boolean

variable {L : Type*} [BooleanAlgebra L]

/-- A dual ideal (p. 288). -/
structure IsDual (D : Set L) : Prop where
  nonempty : ∃ c, c ∈ D
  inf_mem : ∀ c₁ c₂, c₁ ∈ D → c₂ ∈ D → c₁ ⊓ c₂ ∈ D
  sup_mem : ∀ a c, c ∈ D → a ⊔ c ∈ D

/-- a ≈_D b. -/
def relD (D : Set L) (a b : L) : Prop := ∃ d₁ ∈ D, ∃ d₂ ∈ D, a ⊓ d₁ = b ⊓ d₂

/-- The corrected step of p. 290: aᶜ ⊔ c = (a ⊓ cᶜ)ᶜ. -/
theorem compl_step (a c : L) : aᶜ ⊔ c = (a ⊓ cᶜ)ᶜ := by
  rw [compl_inf, compl_compl]

/-- Theorem I (c): the complement respects ≈_I. -/
theorem rel_compl {I : Set L} (hI : IsIdeal I) {a b : L} (h : rel I a b) : rel I aᶜ bᶜ := by
  obtain ⟨c, hc, e⟩ := (rel_iff_single hI _ _).1 h
  refine (rel_iff_single hI _ _).2 ⟨c, hc, ?_⟩
  have key : ∀ x : L, (x ⊓ cᶜ) ⊔ c = x ⊔ c := fun x => by
    rw [sup_inf_right, compl_sup_eq_top, inf_top_eq]
  have e' : aᶜ ⊓ cᶜ = bᶜ ⊓ cᶜ := by rw [← compl_sup, ← compl_sup, e]
  rw [← key aᶜ, e', key]

/-- Theorem I (c): I is an ideal iff D = {a | aᶜ ∈ I} is a dual ideal. -/
theorem ideal_iff_dual (I : Set L) : IsIdeal I ↔ IsDual {a : L | aᶜ ∈ I} := by
  constructor
  · intro hI
    obtain ⟨c, hc⟩ := hI.nonempty
    refine ⟨⟨cᶜ, by simpa using hc⟩, fun c₁ c₂ h₁ h₂ => ?_, fun a c h => ?_⟩
    · show (c₁ ⊓ c₂)ᶜ ∈ I
      rw [compl_inf]; exact hI.sup_mem _ _ h₁ h₂
    · show (a ⊔ c)ᶜ ∈ I
      rw [compl_sup]; exact hI.inf_mem _ _ h
  · intro hD
    obtain ⟨c, hc⟩ := hD.nonempty
    refine ⟨⟨cᶜ, hc⟩, fun c₁ c₂ h₁ h₂ => ?_, fun a c h => ?_⟩
    · have := hD.inf_mem c₁ᶜ c₂ᶜ (by simpa using h₁) (by simpa using h₂)
      simpa [compl_inf] using this
    · have := hD.sup_mem aᶜ cᶜ (by simpa using h)
      simpa [compl_sup] using this

/-- Theorem I (c): for an ideal I, ≈_I and ≈_D coincide (D as above). -/
theorem rel_eq_relD {I : Set L} (hI : IsIdeal I) (a b : L) :
    rel I a b ↔ relD {d : L | dᶜ ∈ I} a b := by
  constructor
  · intro h
    obtain ⟨c₁, h₁, c₂, h₂, e⟩ := rel_compl hI h
    refine ⟨c₁ᶜ, by simpa using h₁, c₂ᶜ, by simpa using h₂, ?_⟩
    rw [← compl_compl (a ⊓ c₁ᶜ), ← compl_compl (b ⊓ c₂ᶜ), ← compl_step, ← compl_step, e]
  · rintro ⟨d₁, h₁, d₂, h₂, e⟩
    have h' : rel I aᶜ bᶜ := ⟨d₁ᶜ, h₁, d₂ᶜ, h₂, by rw [compl_step, compl_step, compl_compl, compl_compl, e]⟩
    simpa using rel_compl hI h'

end Boolean

/-- Theorem XX (Lachlan), ⇐, the diagonal step (p. 315). -/
theorem lachlan_diagonal (W : ℕ → Set ℕ) (A : Set ℕ) (f : ℕ → ℕ)
    (hmeet : ∀ x, ∃ z, z ∈ W (f x) ∧ z ∉ A)
    (hdisj : ∀ x y, x ≠ y → ∀ z, z ∈ W (f x) → z ∉ W (f y)) (y : ℕ) :
    W y ≠ A ∪ {z | z ∉ A ∪ {u | ∃ x, u ∈ W x ∧ u ∈ W (f x)}} := by
  intro hy
  obtain ⟨z, hz, hzA⟩ := hmeet y
  -- z ∈ N − B ⇔ z ∈ B − A, impossible for z ∉ A
  by_cases hB : z ∈ A ∪ {u | ∃ x, u ∈ W x ∧ u ∈ W (f x)}
  · rcases hB with hA | ⟨x, hx, hfx⟩
    · exact hzA hA
    · have hxy : x = y := by
        by_contra hne
        exact hdisj x y hne z hfx hz
      subst hxy
      have : z ∈ A ∪ {z | z ∉ A ∪ {u | ∃ x, u ∈ W x ∧ u ∈ W (f x)}} := hy ▸ hx
      rcases this with h | h
      · exact hzA h
      · exact h (Or.inr ⟨x, hx, hfx⟩)
  · have hzW : z ∈ W y := by rw [hy]; exact Or.inr hB
    exact hB (Or.inr ⟨y, hzW, hz⟩)

end RogersRecursive.Ch10_12.Lattice

#print axioms RogersRecursive.Ch10_12.Lattice.rel_iff_single
#print axioms RogersRecursive.Ch10_12.Lattice.rel_equivalence
#print axioms RogersRecursive.Ch10_12.Lattice.rel_sup
#print axioms RogersRecursive.Ch10_12.Lattice.rel_inf
#print axioms RogersRecursive.Ch10_12.Lattice.ideal_is_class
#print axioms RogersRecursive.Ch10_12.Lattice.ideal_is_zero
#print axioms RogersRecursive.Ch10_12.Lattice.quotient_order
#print axioms RogersRecursive.Ch10_12.Lattice.distrib_sup_to_inf
#print axioms RogersRecursive.Ch10_12.Lattice.distrib_inf_to_sup
#print axioms RogersRecursive.Ch10_12.Lattice.complement_unique
#print axioms RogersRecursive.Ch10_12.Lattice.compl_step
#print axioms RogersRecursive.Ch10_12.Lattice.rel_compl
#print axioms RogersRecursive.Ch10_12.Lattice.ideal_iff_dual
#print axioms RogersRecursive.Ch10_12.Lattice.rel_eq_relD
#print axioms RogersRecursive.Ch10_12.Lattice.lachlan_diagonal
