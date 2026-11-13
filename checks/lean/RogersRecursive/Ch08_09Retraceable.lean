import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Basic

/-!
# Exercise 9-44 (i): tracing a retraceable set from a larger element

Place in the book: § 9.9, exercise 9-44 (`ex:retraceable-sets`, p. 206),
the definition of a retraceable set and (i), as corrected:
"`[A` ретрассируемо `& B ⊂ A & B` бесконечно`] ⇒ A ≤_T B`" (printed
`B ⊃ A`).  The bounded step (`trace`): if `ψ` retraces `A` and `b ∈ A`,
then for `x ≤ b`, `x ∈ A ↔ ψ^[k] b = x` for some `k ≤ b - x`.  With
`B ⊆ A` infinite, an oracle for `B` finds `b ∈ B` with `b ≥ x`, and
`b - x + 1` values of `ψ` decide `x ∈ A`: so `A ≤_T B`.  For `B ⊃ A`
the step needs `b ∈ A`, which `B` does not give: with `B = N` the
printed claim would make every retraceable set recursive, while (iv) gives
a retraceable set that is not recursive.

Notation: `ψ : ℕ → ℕ` (the partial function of the book is used only on
`A`, where it is defined); `Retraces ψ A`: for `a ∈ A`, `ψ a = a` if `a`
is the least element of `A`, otherwise `ψ a` is the nearest smaller
element of `A`.

Not covered: the recursiveness of the procedure in `B` (searching `B`
for `b ≥ x` with the oracle), parts (ii)-(x), the set of (iv).
-/

namespace RogersRecursive.Ch08_09.Retraceable

/-- `ψ` retraces `A`. -/
structure Retraces (ψ : ℕ → ℕ) (A : Set ℕ) : Prop where
  least : ∀ a ∈ A, (∀ b ∈ A, a ≤ b) → ψ a = a
  mem : ∀ a ∈ A, (∃ b ∈ A, b < a) → ψ a ∈ A
  lt : ∀ a ∈ A, (∃ b ∈ A, b < a) → ψ a < a
  nearest : ∀ a ∈ A, ∀ b ∈ A, b < a → b ≤ ψ a

theorem iterate_mem {ψ : ℕ → ℕ} {A : Set ℕ} (h : Retraces ψ A) :
    ∀ k b, b ∈ A → ψ^[k] b ∈ A := by
  intro k
  induction k with
  | zero => intro b hb; simpa using hb
  | succ k ih =>
    intro b hb
    rw [Function.iterate_succ_apply]
    apply ih
    by_cases hl : ∃ c ∈ A, c < b
    · exact h.mem b hb hl
    · simp only [not_exists, not_and, not_lt] at hl
      rw [h.least b hb hl]
      exact hb

/-- Exercise 9-44 (i), the bounded step: from `b ∈ A` the chain
`b, ψ b, ψ (ψ b), …` lists exactly the elements of `A` below `b`. -/
theorem trace {ψ : ℕ → ℕ} {A : Set ℕ} (h : Retraces ψ A) :
    ∀ b ∈ A, ∀ x ≤ b, (x ∈ A ↔ ∃ k ≤ b - x, ψ^[k] b = x) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb x hxb
    constructor
    · intro hx
      rcases Nat.eq_or_lt_of_le hxb with hxe | hxl
      · exact ⟨0, Nat.zero_le _, by simp [hxe]⟩
      · have hex : ∃ c ∈ A, c < b := ⟨x, hx, hxl⟩
        have hψA := h.mem b hb hex
        have hψlt := h.lt b hb hex
        have hxψ := h.nearest b hb x hx hxl
        obtain ⟨k, hk, hkx⟩ := (ih (ψ b) hψlt hψA x hxψ).mp hx
        refine ⟨k + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply]
        exact hkx
    · rintro ⟨k, -, hk⟩
      rw [← hk]
      exact iterate_mem h k b hb

end RogersRecursive.Ch08_09.Retraceable

#print axioms RogersRecursive.Ch08_09.Retraceable.iterate_mem
#print axioms RogersRecursive.Ch08_09.Retraceable.trace
