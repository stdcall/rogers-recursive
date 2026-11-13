import Mathlib.Data.Set.Basic

/-!
# Exercise 8-42 (vi): the hint

Place in the book: § 8.8, exercise 8-42 (`ex:semicreative-not-creative`,
p. 165), (vi) and its hint.  `A ⊂ B`, `B − A` is recursively enumerable by
(ii), `B` is simple by (v).  The hint as printed uses "продуктивность
множества `B − A`"; an r.e. set is never productive
(`not_productive_of_index`).  As corrected the hint uses the productiveness
of `Ā − (B − A)`: if `A` were creative, `Ā` would be productive, then so is
`Ā − (B − A)` (`productive_diff`, with the uniform index of a union,
`W_{u(x)} = W_x ∪ (B − A)`), and `Ā − (B − A) = B̄` (`compl_diff_eq`);
a productive set has an infinite r.e. subset (`th:productive-infinite-re-subset`),
which contradicts the simplicity of `B`.

Notation: `W : ℕ → Set ℕ` is any numbering of sets (the r.e. sets `W_x`);
`p` is a productive function of `P`: `W x ⊆ P → p x ∈ P ∧ p x ∉ W x`.

Not covered: recursiveness of `p ∘ u` (composition of recursive
functions), the existence of `u` (theorem `th:re-closure-uniform`), the
infinite r.e. subset of a productive set, the other parts of the exercise.
-/

namespace RogersRecursive.Ch08_09.Productive

/-- `p` is a productive function of `P` for the numbering `W`. -/
def IsProductive (W : ℕ → Set ℕ) (P : Set ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ x, W x ⊆ P → p x ∈ P ∧ p x ∉ W x

/-- The printed hint fails: a set with an index (`B − A = W e`) is not
productive. -/
theorem not_productive_of_index (W : ℕ → Set ℕ) (P : Set ℕ) (p : ℕ → ℕ)
    (e : ℕ) (he : W e = P) : ¬ IsProductive W P p := by
  intro h
  obtain ⟨h1, h2⟩ := h e he.le
  exact h2 (he ▸ h1)

/-- A productive set minus an r.e. subset `R` is productive, with the
productive function `p ∘ u`, where `W (u x) = W x ∪ R`. -/
theorem productive_diff (W : ℕ → Set ℕ) (P R : Set ℕ) (p u : ℕ → ℕ)
    (hu : ∀ x, W (u x) = W x ∪ R) (hR : R ⊆ P) (hp : IsProductive W P p) :
    IsProductive W (P \ R) (p ∘ u) := by
  intro x hx
  have hsub : W (u x) ⊆ P := by
    rw [hu]
    exact Set.union_subset (fun n hn => (hx hn).1) hR
  obtain ⟨h1, h2⟩ := hp (u x) hsub
  rw [hu] at h2
  exact ⟨⟨h1, fun h => h2 (Or.inr h)⟩, fun h => h2 (Or.inl h)⟩

/-- `Ā − (B − A) = B̄` when `A ⊆ B`. -/
theorem compl_diff_eq (A B : Set ℕ) (h : A ⊆ B) : Aᶜ \ (B \ A) = Bᶜ := by
  ext n
  simp only [Set.mem_sdiff, Set.mem_compl_iff, not_and, not_not]
  constructor
  · rintro ⟨hA, hB⟩ hnB
    exact hA (hB hnB)
  · intro hnB
    exact ⟨fun hA => hnB (h hA), fun hB => absurd hB hnB⟩

/-- The corrected hint: if `Ā` is productive and `B − A` is r.e., then
`B̄` is productive. -/
theorem complement_productive (W : ℕ → Set ℕ) (A B : Set ℕ) (h : A ⊆ B)
    (p u : ℕ → ℕ) (hu : ∀ x, W (u x) = W x ∪ (B \ A))
    (hp : IsProductive W Aᶜ p) : IsProductive W Bᶜ (p ∘ u) := by
  have hR : B \ A ⊆ Aᶜ := fun n hn => hn.2
  have := productive_diff W Aᶜ (B \ A) p u hu hR hp
  rwa [compl_diff_eq A B h] at this

end RogersRecursive.Ch08_09.Productive

#print axioms RogersRecursive.Ch08_09.Productive.not_productive_of_index
#print axioms RogersRecursive.Ch08_09.Productive.productive_diff
#print axioms RogersRecursive.Ch08_09.Productive.compl_diff_eq
#print axioms RogersRecursive.Ch08_09.Productive.complement_productive
