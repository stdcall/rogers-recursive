import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Arithmetic steps of chapter 14

Places in the book:

* § 14.3, property 1 of bounded quantifiers (p. 398), as corrected:
  `(∀ a ≤ b)(∃ c) R(a, c) ⇔ (∃ c)(∀ a ≤ b) R(a, π_(a+1)^(b+1)(c))`
  (`R(a, c)` stands for `(∀ d) R(a, b, c, d)`).  Proved for any decoding
  `dec c a` under which every `b + 1`-tuple has a code (`bounded_swap`);
  for `dec c a = π_(a+1)^(b+1)(c)` this holds since `τ^(b+1)` maps
  `N^(b+1)` onto `N` with the inverses `π_j^(b+1)`, `1 ≤ j ≤ b + 1`
  (§ 5.3).  As printed, `π_a^b`, the index `a = 0` has no function
  `π_0^b`, and `a` takes `b + 1` values.
* § 14.3, p. 399, and the proof of `th:strong-hierarchy` (p. 404): a member
  `x` of `D_u` satisfies `x < u` (in particular `x ≤ u`), so the
  quantifier `(∀ x)[x ∈ D_u ⇒ …]` is bounded by `u` (`mem_canonical_lt`;
  `x ∈ D_u` is bit `x` of `u`).
* The editorial footnote to `th:goedel-polynomial` (p. 401), the third
  operation: `(α = 0) ∨ (β = 0)` is `α β = 0` (`mul_eq_zero_iff_int`);
  the negation `¬(α = 0)` is `(∃ c)(α α = c + 1)` for an integer
  polynomial value `α` (`ne_zero_iff_mul_self_eq_succ`, as corrected); the
  printed `(∃ c)(α = c + 1)` fails for `α = -1` (`printed_rule_fails`),
  e.g. for `¬(0 = 1)`, `γ = 0 - 1`.
* § 14.7, p. 414: the printed formula
  `(∀ x)(∀ y)(∀ z)(∀ w)[w > 2 ⇒ x^w + y^w ≠ z^w]` is false
  (`printed_fermat_false`: `x = 0`, `y = z = 1`, `w = 3`); with
  `x > 0 & y > 0` (as corrected) a solution would have `z > 0`
  (`fermat_z_pos`), so the condition is the one of Fermat's theorem.

Not covered: Fermat's theorem itself, the bounded-quantifier elimination
in the Tarski–Kuratowski algorithm (checked on prefix skeletons in
`checks/haskell/CheckCh14Hierarchy.hs`).
-/

namespace RogersRecursive.Ch13_14.Arithmetic

/-- Property 1 of bounded quantifiers, as corrected (p. 398). -/
theorem bounded_swap (b : ℕ) (R : ℕ → ℕ → Prop) (dec : ℕ → ℕ → ℕ)
    (hcode : ∀ t : ℕ → ℕ, ∃ c, ∀ a ≤ b, dec c a = t a) :
    (∀ a ≤ b, ∃ c, R a c) ↔ ∃ c, ∀ a ≤ b, R a (dec c a) := by
  constructor
  · intro h
    classical
    let t : ℕ → ℕ := fun a => if ha : a ≤ b then Classical.choose (h a ha) else 0
    obtain ⟨c, hc⟩ := hcode t
    refine ⟨c, fun a ha => ?_⟩
    rw [hc a ha]
    simp only [t, ha, ↓reduceDIte]
    exact Classical.choose_spec (h a ha)
  · rintro ⟨c, hc⟩ a ha
    exact ⟨dec c a, hc a ha⟩

/-- A member `x` of `D_u` (bit `x` of `u` is 1) is below `u`. -/
theorem mem_canonical_lt (u x : ℕ) (h : u.testBit x = true) : x < u :=
  lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.ge_two_pow_of_testBit h)

theorem mul_eq_zero_iff_int (α β : ℤ) : α * β = 0 ↔ α = 0 ∨ β = 0 := mul_eq_zero

/-- The footnote of p. 401, as corrected: `¬(α = 0) ⇔ (∃ c)(α α = c + 1)`. -/
theorem ne_zero_iff_mul_self_eq_succ (α : ℤ) : α ≠ 0 ↔ ∃ c : ℕ, α * α = c + 1 := by
  constructor
  · intro h
    have hpos : 0 < α * α := mul_self_pos.mpr h
    generalize α * α = m at hpos ⊢
    refine ⟨(m - 1).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  · rintro ⟨c, hc⟩ h0
    rw [h0, mul_zero] at hc
    omega

/-- The printed rule `¬(α = 0) ⇔ (∃ c)(α = c + 1)` fails for `α = -1`. -/
theorem printed_rule_fails : ¬ ∀ α : ℤ, (α ≠ 0 ↔ ∃ c : ℕ, α = c + 1) := by
  intro h
  obtain ⟨c, hc⟩ := (h (-1)).mp (by norm_num)
  omega

/-- The printed formula for Fermat's theorem (p. 414) is false. -/
theorem printed_fermat_false : ¬ ∀ x y z w : ℕ, w > 2 → x ^ w + y ^ w ≠ z ^ w :=
  fun h => h 0 1 1 3 (by norm_num) (by norm_num)

/-- With `x > 0` a solution of `x^w + y^w = z^w` (`w > 0`) has `z > 0`. -/
theorem fermat_z_pos (x y z w : ℕ) (hx : 0 < x) (hw : 0 < w)
    (h : x ^ w + y ^ w = z ^ w) : 0 < z := by
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hw)] at h
    have : 0 < x ^ w := Nat.pow_pos hx
    omega
  · exact hz

end RogersRecursive.Ch13_14.Arithmetic

#print axioms RogersRecursive.Ch13_14.Arithmetic.bounded_swap
#print axioms RogersRecursive.Ch13_14.Arithmetic.mem_canonical_lt
#print axioms RogersRecursive.Ch13_14.Arithmetic.mul_eq_zero_iff_int
#print axioms RogersRecursive.Ch13_14.Arithmetic.ne_zero_iff_mul_self_eq_succ
#print axioms RogersRecursive.Ch13_14.Arithmetic.printed_rule_fails
#print axioms RogersRecursive.Ch13_14.Arithmetic.printed_fermat_false
#print axioms RogersRecursive.Ch13_14.Arithmetic.fermat_z_pos
