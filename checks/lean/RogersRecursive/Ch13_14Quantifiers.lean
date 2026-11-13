import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic

/-!
# Quantifier rules of chapter 14

Places in the book:

* § 14.3, point 2 (p. 395, used by `th:definable-in-hierarchy`): the eight
  pairs of prenex rules, for a formula `G` without the variable `a`.  Four
  of them need a nonempty domain (here any nonempty type, in the book `N`);
  over the empty domain the rule for `(∀ a) F ⇒ G` fails
  (`forall_imp_fails_empty`).
* § 14.8, the quantifier `U` ("for infinitely many", p. 421, before
  `th:pi-two-u-form`): `(U a) F` says that `{a | F a}` is infinite.  The
  four rules of p. 421 for moving `U` to the left, and the example
  `(U x)(U y)[x < y]` true, `(U y)(U x)[x < y]` false.
* `th:pi-two-u-form` (p. 421), the step `⇐`:
  `(U y) S(y) ⇔ (∀ u)(∃ y)[y > u & S(y)]`; the lemma of
  `th:kreisel-shoenfield-wang` (p. 422), the step `⇐`:
  `(U y)(∀ z) S(y, z) ⇔ (∀ x)(∃ y)(∀ z)[y ≥ x & S(y, z)]`.

Not covered: the recursion-theoretic parts of these theorems (the
completeness of `{z | W_z infinite}`, the relativized hierarchy).
-/

namespace RogersRecursive.Ch13_14.Quantifiers

section Prenex

variable {α : Type*} (F : α → Prop) (G : Prop)

theorem exists_or_rule [Nonempty α] : ((∃ a, F a) ∨ G) ↔ ∃ a, F a ∨ G := by
  constructor
  · rintro (⟨a, h⟩ | h)
    · exact ⟨a, Or.inl h⟩
    · obtain ⟨a⟩ := ‹Nonempty α›
      exact ⟨a, Or.inr h⟩
  · rintro ⟨a, h | h⟩
    · exact Or.inl ⟨a, h⟩
    · exact Or.inr h

theorem forall_or_rule : ((∀ a, F a) ∨ G) ↔ ∀ a, F a ∨ G := by
  constructor
  · rintro (h | h) a
    · exact Or.inl (h a)
    · exact Or.inr h
  · intro h
    by_cases hG : G
    · exact Or.inr hG
    · exact Or.inl fun a => (h a).resolve_right hG

theorem exists_and_rule : ((∃ a, F a) ∧ G) ↔ ∃ a, F a ∧ G := by
  constructor
  · rintro ⟨⟨a, h⟩, hG⟩
    exact ⟨a, h, hG⟩
  · rintro ⟨a, h, hG⟩
    exact ⟨⟨a, h⟩, hG⟩

theorem forall_and_rule [Nonempty α] : ((∀ a, F a) ∧ G) ↔ ∀ a, F a ∧ G := by
  constructor
  · rintro ⟨h, hG⟩ a
    exact ⟨h a, hG⟩
  · intro h
    obtain ⟨a⟩ := ‹Nonempty α›
    exact ⟨fun b => (h b).1, (h a).2⟩

theorem exists_imp_rule : ((∃ a, F a) → G) ↔ ∀ a, F a → G := by
  constructor
  · intro h a ha
    exact h ⟨a, ha⟩
  · rintro h ⟨a, ha⟩
    exact h a ha

theorem forall_imp_rule [Nonempty α] : ((∀ a, F a) → G) ↔ ∃ a, F a → G := by
  constructor
  · intro h
    by_cases hall : ∀ a, F a
    · obtain ⟨a⟩ := ‹Nonempty α›
      exact ⟨a, fun _ => h hall⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hall
      exact ⟨a, fun h' => absurd h' ha⟩
  · rintro ⟨a, h⟩ hall
    exact h (hall a)

theorem imp_exists_rule [Nonempty α] : (G → ∃ a, F a) ↔ ∃ a, G → F a := by
  constructor
  · intro h
    by_cases hG : G
    · obtain ⟨a, ha⟩ := h hG
      exact ⟨a, fun _ => ha⟩
    · obtain ⟨a⟩ := ‹Nonempty α›
      exact ⟨a, fun h' => absurd h' hG⟩
  · rintro ⟨a, h⟩ hG
    exact ⟨a, h hG⟩

theorem imp_forall_rule : (G → ∀ a, F a) ↔ ∀ a, G → F a :=
  ⟨fun h a hG => h hG a, fun h hG a => h a hG⟩

end Prenex

/-- Over the empty domain the rule for `(∀ a) F ⇒ G` fails (`F`, `G` true). -/
theorem forall_imp_fails_empty :
    ¬ (((∀ _a : Empty, True) → True) ↔ ∃ _a : Empty, True → True) := by
  intro h
  obtain ⟨a, _⟩ := h.1 (fun _ => trivial)
  exact a.elim

/-- `(U a) F`: there are infinitely many `a` with `F a`. -/
def U (F : ℕ → Prop) : Prop := Set.Infinite {a | F a}

theorem U_or (F : ℕ → Prop) (G : Prop) : (U F ∨ G) ↔ U fun a => F a ∨ G := by
  show (Set.Infinite {a | F a} ∨ G) ↔ Set.Infinite {a | F a ∨ G}
  by_cases hG : G
  · have h : {a | F a ∨ G} = Set.univ := Set.eq_univ_of_forall fun a => Or.inr hG
    rw [h]
    exact ⟨fun _ => Set.infinite_univ, fun _ => Or.inr hG⟩
  · have h : {a | F a ∨ G} = {a | F a} :=
      Set.ext fun a => ⟨fun ha => ha.resolve_right hG, Or.inl⟩
    rw [h]
    exact ⟨fun h' => h'.resolve_right hG, Or.inl⟩

theorem U_and (F : ℕ → Prop) (G : Prop) : (U F ∧ G) ↔ U fun a => F a ∧ G := by
  show (Set.Infinite {a | F a} ∧ G) ↔ Set.Infinite {a | F a ∧ G}
  by_cases hG : G
  · have h : {a | F a ∧ G} = {a | F a} := Set.ext fun a => ⟨fun ha => ha.1, fun ha => ⟨ha, hG⟩⟩
    rw [h]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', hG⟩⟩
  · have h : {a | F a ∧ G} = ∅ := Set.ext fun a => ⟨fun ha => absurd ha.2 hG, fun ha => ha.elim⟩
    rw [h]
    exact ⟨fun h' => absurd h'.2 hG, fun h' => absurd Set.finite_empty h'⟩

theorem imp_U (F : ℕ → Prop) (G : Prop) : (G → U F) ↔ U fun a => G → F a := by
  show (G → Set.Infinite {a | F a}) ↔ Set.Infinite {a | G → F a}
  by_cases hG : G
  · have h : {a | G → F a} = {a | F a} := Set.ext fun a => ⟨fun ha => ha hG, fun ha _ => ha⟩
    rw [h]
    exact ⟨fun h' => h' hG, fun h' _ => h'⟩
  · have h : {a | G → F a} = Set.univ := Set.eq_univ_of_forall fun a h' => absurd h' hG
    rw [h]
    exact ⟨fun _ => Set.infinite_univ, fun _ h' => absurd h' hG⟩

theorem U_imp (F : ℕ → Prop) (G : Prop) : (U F → G) ↔ ¬ U fun a => ¬ (F a → G) := by
  show (Set.Infinite {a | F a} → G) ↔ ¬ Set.Infinite {a | ¬ (F a → G)}
  by_cases hG : G
  · have h : {a | ¬ (F a → G)} = ∅ :=
      Set.ext fun a => ⟨fun ha => absurd (fun _ => hG) ha, fun ha => ha.elim⟩
    rw [h]
    exact ⟨fun _ h' => h' Set.finite_empty, fun _ _ => hG⟩
  · have h : {a | ¬ (F a → G)} = {a | F a} :=
      Set.ext fun a => ⟨fun ha => by_contra fun hF => ha fun h' => absurd h' hF,
        fun ha h' => hG (h' ha)⟩
    rw [h]
    exact ⟨fun h' hU => hG (h' hU), fun h' hU => absurd hU h'⟩

/-- `(U x)(U y)[x < y]` is true. -/
theorem U_U_lt : U fun x => U fun y => x < y := by
  show Set.Infinite {x : ℕ | Set.Infinite {y | x < y}}
  have h : {x : ℕ | Set.Infinite {y | x < y}} = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    show Set.Infinite {y | x < y}
    rw [Set.infinite_iff_exists_gt]
    intro a
    exact ⟨max x a + 1, show x < max x a + 1 by omega, by omega⟩
  rw [h]
  exact Set.infinite_univ

/-- `(U y)(U x)[x < y]` is false. -/
theorem not_U_U_lt_swapped : ¬ U fun y => U fun x => x < y := by
  show ¬ Set.Infinite {y : ℕ | Set.Infinite {x | x < y}}
  have h : {y : ℕ | Set.Infinite {x | x < y}} = ∅ :=
    Set.ext fun y => ⟨fun hy => absurd (Set.finite_lt_nat y) hy, fun hy => hy.elim⟩
  rw [h]
  exact fun h' => h' Set.finite_empty

/-- `th:pi-two-u-form`, `⇐`: `(U y) S(y) ⇔ (∀ u)(∃ y)[y > u & S(y)]`. -/
theorem U_iff_forall_exists_gt (S : ℕ → Prop) : U S ↔ ∀ u, ∃ y, u < y ∧ S y := by
  show Set.Infinite {y | S y} ↔ _
  rw [Set.infinite_iff_exists_gt]
  exact forall_congr' fun u => ⟨fun ⟨y, hy, h⟩ => ⟨y, h, hy⟩, fun ⟨y, h, hy⟩ => ⟨y, hy, h⟩⟩

/-- The lemma of `th:kreisel-shoenfield-wang`, `⇐`:
`(U y)(∀ z) S(y, z) ⇔ (∀ x)(∃ y)(∀ z)[y ≥ x & S(y, z)]`. -/
theorem U_forall_iff (S : ℕ → ℕ → Prop) :
    (U fun y => ∀ z, S y z) ↔ ∀ x, ∃ y, ∀ z, x ≤ y ∧ S y z := by
  rw [U_iff_forall_exists_gt]
  constructor
  · intro h x
    obtain ⟨y, hy, hS⟩ := h x
    exact ⟨y, fun z => ⟨hy.le, hS z⟩⟩
  · intro h u
    obtain ⟨y, hy⟩ := h (u + 1)
    exact ⟨y, by have := (hy 0).1; omega, fun z => (hy z).2⟩

end RogersRecursive.Ch13_14.Quantifiers

#print axioms RogersRecursive.Ch13_14.Quantifiers.exists_or_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.forall_or_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.exists_and_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.forall_and_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.exists_imp_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.forall_imp_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.imp_exists_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.imp_forall_rule
#print axioms RogersRecursive.Ch13_14.Quantifiers.forall_imp_fails_empty
#print axioms RogersRecursive.Ch13_14.Quantifiers.U_or
#print axioms RogersRecursive.Ch13_14.Quantifiers.U_and
#print axioms RogersRecursive.Ch13_14.Quantifiers.imp_U
#print axioms RogersRecursive.Ch13_14.Quantifiers.U_imp
#print axioms RogersRecursive.Ch13_14.Quantifiers.U_U_lt
#print axioms RogersRecursive.Ch13_14.Quantifiers.not_U_U_lt_swapped
#print axioms RogersRecursive.Ch13_14.Quantifiers.U_iff_forall_exists_gt
#print axioms RogersRecursive.Ch13_14.Quantifiers.U_forall_iff
