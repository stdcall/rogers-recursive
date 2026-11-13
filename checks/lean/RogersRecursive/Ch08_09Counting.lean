import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Counting steps of chapters 8 and 9

Places in the book:

* § 8.1, the proof of Post's theorem `th:simple-set-exists` (p. 141),
  part (ii): "самое большее `k` чисел из `{0, 1, …, 2k}` может принадлежать
  `S`".  `S` is the set of values of a partial function that gives to `x`
  (at most) one `y` with `y > 2x`; here it is any `sel : ℕ → Option ℕ` with
  `sel x = some y → 2x < y` (`post_selection_card`).
* § 8.4, the proof of `th:simple-tt-complete` (p. 148): every block
  `S_x = {2^x - 1, …, 2^(x+1) - 2}` meets the complement of `S`
  (`block_not_subset`): it has `2^x = k + 1` elements in `{0, …, 2k}`,
  `k = 2^x - 1`.
* § 8.5, the lemma of `th:btt-complete-not-simple` (p. 153), (iii):
  `2^(2^0) + 2^(2^1) + … + 2^(2^m) < 2^(2^(m+1))`, the number of boolean
  functions of at most `m` arguments (`boolean_count_lt`).
* § 9.6, the lemma of `th:tt-complete-not-hypersimple` (p. 186), (iii):
  `2^(2^d) · 2^d = 2^(2^d + d) < 2^(2^(d+1))` (`derived_count_lt`).

Not covered: recursive enumerability of `S`, the simplicity of `S` and
`S*`, the derivability argument of the lemmas (checked on finite models in
`checks/haskell/CheckCh08TruthTable.hs` and `CheckCh09Turing.hs`).
-/

namespace RogersRecursive.Ch08_09.Counting

open Classical in
/-- Theorem 8-II (ii): at most `k` numbers of `{0, …, 2k}` are selected. -/
theorem post_selection_card (sel : ℕ → Option ℕ)
    (hsel : ∀ x y, sel x = some y → 2 * x < y) (k : ℕ) :
    ((Finset.range (2 * k + 1)).filter (fun y => ∃ x, sel x = some y)).card ≤ k := by
  calc ((Finset.range (2 * k + 1)).filter (fun y => ∃ x, sel x = some y)).card
      ≤ ((Finset.range k).image (fun x => (sel x).getD 0)).card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_range] at hy
        obtain ⟨hy, x, hx⟩ := hy
        have h2 := hsel x y hx
        exact Finset.mem_image.mpr ⟨x, Finset.mem_range.mpr (by omega), by simp [hx]⟩
    _ ≤ (Finset.range k).card := Finset.card_image_le
    _ = k := Finset.card_range k

/-- Theorem 8-VI: the block `S_x` is not inside the set of selected numbers. -/
theorem block_not_subset (sel : ℕ → Option ℕ)
    (hsel : ∀ x y, sel x = some y → 2 * x < y) (x : ℕ) :
    ¬ ∀ y, 2 ^ x - 1 ≤ y → y ≤ 2 ^ (x + 1) - 2 → ∃ z, sel z = some y := by
  classical
  intro hall
  have hpow : 2 ^ (x + 1) = 2 * 2 ^ x := by rw [pow_succ]; omega
  have hone : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have hsub : Finset.Icc (2 ^ x - 1) (2 ^ (x + 1) - 2) ⊆
      (Finset.range (2 * (2 ^ x - 1) + 1)).filter (fun y => ∃ x, sel x = some y) := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hall y hy.1 hy.2⟩
  have hcard := (Finset.card_le_card hsub).trans (post_selection_card sel hsel (2 ^ x - 1))
  rw [Nat.card_Icc] at hcard
  omega

/-- The lemma of theorem 8-XII, (iii): fewer than `2^(2^(m+1))` boolean
functions of at most `m` arguments. -/
theorem boolean_count_lt (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), 2 ^ (2 ^ i) < 2 ^ (2 ^ (m + 1)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have ha : 2 ≤ 2 ^ (2 ^ (m + 1)) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ (m + 1)) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    have hsq : 2 ^ (2 ^ (m + 1 + 1)) = 2 ^ (2 ^ (m + 1)) * 2 ^ (2 ^ (m + 1)) := by
      rw [pow_succ 2 (m + 1), pow_mul, sq]
    rw [hsq]
    nlinarith

/-- The lemma of theorem 9-XVIII, (iii): `2^(2^d) · 2^d < 2^(2^(d+1))`. -/
theorem derived_count_lt (d : ℕ) : 2 ^ (2 ^ d) * 2 ^ d < 2 ^ (2 ^ (d + 1)) := by
  rw [← pow_add]
  apply Nat.pow_lt_pow_right (by norm_num)
  have h := Nat.lt_two_pow_self (n := d)
  rw [pow_succ]
  omega

end RogersRecursive.Ch08_09.Counting

#print axioms RogersRecursive.Ch08_09.Counting.post_selection_card
#print axioms RogersRecursive.Ch08_09.Counting.block_not_subset
#print axioms RogersRecursive.Ch08_09.Counting.boolean_count_lt
#print axioms RogersRecursive.Ch08_09.Counting.derived_count_lt
