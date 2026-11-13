import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Data.Set.Basic

/-!
# Order-theoretic steps of chapter 13

Places in the book:

* `cor:incomparable-with-countable` (§ 13.3, p. 348), the proof, as
  corrected: with `𝒜_x = {c | c ≤ a_x or a_x ≤ c}` every `b` outside
  `𝒜* = ⋃_x 𝒜_x` is incomparable with every `a_x`
  (`incomparable_of_not_mem`).  With the printed strict inequalities the
  step fails already for `𝒜 = {a}` (`a_x = a` for all `x`): `b = a` lies
  outside the union and is not incomparable with `a`
  (`printed_strict_fails`).  The category statements
  (`cor:incomparable-second-category` (b)) are not formalized.
* `cor:minimal-degree-below-0-double-jump` (§ 13.5, p. 359), as printed
  with `(∃ b)[b < a ⇒ b = 0]`: this holds for every `a` (take `b = a`),
  so it does not express minimality (`printed_minimality_trivial`); the
  corrected `(∀ b)` is the minimality of `th:minimal-degree`.
* § 13.7, p. 372: with the printed values `¬A = 1` for `A ≠ 1`,
  `¬A = 0` for `A = 1`, `0` the least and `1` the greatest degree and `∨`
  the greatest lower bound, `¬A ∨ ¬¬A = 0` for every `A`
  (`medvedev_not_or_not_not`): the expression `¬A ∨ ¬¬A` is true in the
  sense of p. 372.  On the Kripke frame `r < a`, `r < b` with `p` true at
  `a` only, `r` forces neither `¬p` nor `¬¬p` (`kripke_root_fails`).  By
  the soundness of the intuitionistic propositional calculus for Kripke
  frames (quoted, not formalized: A. Chagrov, M. Zakharyaschev, Modal
  Logic, 1997, § 2.5, Proposition 2.37, Corollary 2.44) `¬p ∨ ¬¬p` is not
  an intuitionistic theorem, so the true expressions with `¬` are not
  exactly the intuitionistic theorems.
* `ex:jump-productive` (v) (p. 381): `A' = B' ⇒ A = B`, from the
  consequence of the `s`-`m`-`n` theorem that for every `n` there is an
  index `e n` with `e n ∈ X' ⇔ n ∈ X` for all `X`, stated as a hypothesis
  (`jump_injective`).

Notation: degrees are the elements of a preorder `D`; the Medvedev degrees
are the elements of a bounded lattice `L` (`⊥` the degree `0`, `⊤` the
degree `1`, `⊓` the book's `∨`).
-/

namespace RogersRecursive.Ch13_14.Degrees

section Order

variable {D : Type*} [Preorder D]

/-- `a | b`: `a` and `b` are incomparable. -/
def Incomp (a b : D) : Prop := ¬ a ≤ b ∧ ¬ b ≤ a

/-- `𝒜* = ⋃_x 𝒜_x` with `𝒜_x = {c | c ≤ a_x or a_x ≤ c}` (as corrected). -/
def unionLe (a : ℕ → D) : Set D := {c | ∃ x, c ≤ a x ∨ a x ≤ c}

/-- The printed `𝒜_x = {c | c < a_x or a_x < c}`. -/
def unionLt (a : ℕ → D) : Set D := {c | ∃ x, c < a x ∨ a x < c}

theorem incomparable_of_not_mem (a : ℕ → D) (b : D) (hb : b ∉ unionLe a) :
    ∀ x, Incomp b (a x) :=
  fun x => ⟨fun h => hb ⟨x, Or.inl h⟩, fun h => hb ⟨x, Or.inr h⟩⟩

theorem printed_strict_fails [Nonempty D] :
    ¬ ∀ (a : ℕ → D) (b : D), b ∉ unionLt a → ∀ x, Incomp b (a x) := by
  intro h
  obtain ⟨d⟩ := ‹Nonempty D›
  have hout : d ∉ unionLt (fun _ => d) := by
    rintro ⟨_, h' | h'⟩ <;> exact lt_irrefl d h'
  exact (h (fun _ => d) d hout 0).1 le_rfl

theorem printed_minimality_trivial (zero a : D) : ∃ b, b < a → b = zero :=
  ⟨a, fun h => absurd h (lt_irrefl a)⟩

end Order

theorem medvedev_not_or_not_not {L : Type*} [Lattice L] [BoundedOrder L]
    (neg : L → L) (hneg_top : neg ⊤ = ⊥)
    (hneg_ne : ∀ A, A ≠ ⊤ → neg A = ⊤) (A : L) : neg A ⊓ neg (neg A) = ⊥ := by
  by_cases hA : A = ⊤
  · rw [hA, hneg_top]
    exact bot_inf_eq _
  · rw [hneg_ne A hA, hneg_top]
    exact inf_bot_eq _

/-- The worlds of the frame `r < a`, `r < b`. -/
inductive World | r | a | b

/-- `v` is accessible from `w` (reflexive). -/
def Above : World → World → Prop
  | .r, _ => True
  | .a, .a => True
  | .b, .b => True
  | _, _ => False

/-- Forcing of `¬ φ` from the forcing of `φ`. -/
def forcesNot (φ : World → Prop) (w : World) : Prop := ∀ v, Above w v → ¬ φ v

/-- `p` is true at `a` only (an upward closed set). -/
def P : World → Prop
  | .a => True
  | _ => False

theorem kripke_root_fails : ¬ (forcesNot P .r ∨ forcesNot (forcesNot P) .r) := by
  rintro (h | h)
  · exact h .a trivial trivial
  · refine h .b trivial ?_
    intro v hv
    cases v with
    | r => exact hv.elim
    | a => exact hv.elim
    | b => exact fun hp => hp.elim

theorem jump_injective (jump : Set ℕ → Set ℕ) (e : ℕ → ℕ)
    (he : ∀ n X, e n ∈ jump X ↔ n ∈ X) : Function.Injective jump := by
  intro A B h
  ext n
  rw [← he n A, ← he n B, h]

end RogersRecursive.Ch13_14.Degrees

#print axioms RogersRecursive.Ch13_14.Degrees.incomparable_of_not_mem
#print axioms RogersRecursive.Ch13_14.Degrees.printed_strict_fails
#print axioms RogersRecursive.Ch13_14.Degrees.printed_minimality_trivial
#print axioms RogersRecursive.Ch13_14.Degrees.medvedev_not_or_not_not
#print axioms RogersRecursive.Ch13_14.Degrees.kripke_root_fails
#print axioms RogersRecursive.Ch13_14.Degrees.jump_injective
