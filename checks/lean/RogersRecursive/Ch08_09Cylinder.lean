import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Set

/-!
# Exercise 8-29 (b): `A ⊕ A ≤₁ A` and cylinders

Place in the book: § 8.8, exercise 8-29 (`ex:join-of-cylinders`, p. 163),
part (b), as corrected: "`A ⊕ A ≤₁ A ⇔ A` есть цилиндр" (printed
`A ⊕ B ≤₁ A`).  `A ⊕ B = {2x | x ∈ A} ∪ {2x + 1 | x ∈ B}` (§ 7.6).

* The step `⇒` (`iterate_reduction`): from a one-one `f` with
  `n ∈ A ⊕ A ↔ f n ∈ A`, the maps `f₀ x = f (2x)`, `f₁ x = f (2x + 1)` and
  `h (x, n) = f₁^[n] (f₀ x)` give a one-one map of `ℕ × ℕ` with
  `x ∈ A ↔ h (x, n) ∈ A`, i.e. `A × N ≤₁ A` (through `τ`); then `A` is a
  cylinder by the characterization of cylinders in § 7.6
  (`th:cylinder-properties`), not formalized here.
* The printed reading fails in both directions: `⇐` for the cylinder
  `A = ∅ = ∅ × N` and `B = N` (`printed_backward_fails`; a nondegenerate
  example is `A = K`, `B = K̄`, since `K̄` is not 1-reducible to `K`);
  `⇒` because `A ⊕ N ≤₁ A` for every `A` containing the multiples of 3
  (`printed_forward_fails`; every simple set contains an infinite
  recursive set, which plays this part, and is not a cylinder by
  `th:simple-sets-properties` (d)).

Not covered: recursiveness of the maps (they are compositions and iterates
of recursive functions), the cylinder theorem of § 7.6, the facts about
`K` and simple sets quoted above.
-/

namespace RogersRecursive.Ch08_09.Cylinder

/-- The join `A ⊕ B` of § 7.6. -/
def join (A B : Set ℕ) : Set ℕ :=
  {n | (n % 2 = 0 ∧ n / 2 ∈ A) ∨ (n % 2 = 1 ∧ n / 2 ∈ B)}

theorem mem_join_even (A B : Set ℕ) (x : ℕ) : 2 * x ∈ join A B ↔ x ∈ A := by
  have h1 : 2 * x % 2 = 0 := by omega
  have h2 : 2 * x / 2 = x := by omega
  simp [join, h1, h2]

theorem mem_join_odd (A B : Set ℕ) (x : ℕ) : 2 * x + 1 ∈ join A B ↔ x ∈ B := by
  have h1 : (2 * x + 1) % 2 = 1 := by omega
  have h2 : (2 * x + 1) / 2 = x := by omega
  simp [join, h1, h2]

/-- Two one-one maps with disjoint ranges: `f₁^[n] (f₀ x)` determines `n`
and `x`. -/
theorem iterate_aux (f₀ f₁ : ℕ → ℕ) (h₀ : Function.Injective f₀)
    (h₁ : Function.Injective f₁) (hd : ∀ a b, f₀ a ≠ f₁ b) :
    ∀ n k x x', f₁^[n] (f₀ x) = f₁^[n + k] (f₀ x') → k = 0 ∧ x = x' := by
  intro n k x x' h
  rw [Function.iterate_add_apply] at h
  have h' := (h₁.iterate n) h
  cases k with
  | zero => exact ⟨rfl, h₀ (by simpa using h')⟩
  | succ k =>
    rw [Function.iterate_succ_apply'] at h'
    exact absurd h' (hd _ _)

/-- Exercise 8-29 (b), `⇒`: from `A ⊕ A ≤₁ A` by `f`, the one-one map
`h (x, n) = f₁^[n] (f₀ x)` keeps membership in `A`. -/
theorem iterate_reduction (A : Set ℕ) (f : ℕ → ℕ) (hf : Function.Injective f)
    (hred : ∀ n, n ∈ join A A ↔ f n ∈ A) :
    Function.Injective (fun p : ℕ × ℕ => (fun x => f (2 * x + 1))^[p.2] (f (2 * p.1))) ∧
      ∀ x n, x ∈ A ↔ (fun x => f (2 * x + 1))^[n] (f (2 * x)) ∈ A := by
  set f₀ : ℕ → ℕ := fun x => f (2 * x) with hf₀
  set f₁ : ℕ → ℕ := fun x => f (2 * x + 1) with hf₁
  have h₀ : Function.Injective f₀ := fun a b h => by
    have := hf h
    omega
  have h₁ : Function.Injective f₁ := fun a b h => by
    have := hf h
    omega
  have hd : ∀ a b, f₀ a ≠ f₁ b := fun a b h => by
    have := hf h
    omega
  refine ⟨?_, ?_⟩
  · rintro ⟨x, n⟩ ⟨x', m⟩ h
    simp only at h
    rcases le_total n m with hnm | hmn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      obtain ⟨hk, hx⟩ := iterate_aux f₀ f₁ h₀ h₁ hd n k x x' h
      subst hk hx
      rfl
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      obtain ⟨hk, hx⟩ := iterate_aux f₀ f₁ h₀ h₁ hd m k x' x h.symm
      subst hk hx
      rfl
  · intro x n
    induction n with
    | zero =>
      simp only [Function.iterate_zero, id]
      rw [← mem_join_even A A x]
      exact hred (2 * x)
    | succ n ih =>
      rw [ih, Function.iterate_succ_apply']
      rw [← mem_join_odd A A]
      exact hred _

/-- The printed `⇐` fails: `∅` is a cylinder, but `∅ ⊕ N` is not reducible
to `∅` by any map (it contains 1). -/
theorem printed_backward_fails :
    ¬ ∃ g : ℕ → ℕ, ∀ n, n ∈ join (∅ : Set ℕ) Set.univ ↔ g n ∈ (∅ : Set ℕ) := by
  rintro ⟨g, hg⟩
  have h1 : (1 : ℕ) ∈ join (∅ : Set ℕ) Set.univ := by
    simpa using (mem_join_odd (∅ : Set ℕ) Set.univ 0)
  exact ((hg 1).mp h1).elim

/-- The one-one map of `printed_forward_fails`: `2x ↦ 2x` if `3 ∣ x`,
`2x ↦ x` otherwise, `2x + 1 ↦ 6x + 3`. -/
def g (n : ℕ) : ℕ :=
  if n % 2 = 0 then (if n / 2 % 3 = 0 then n else n / 2) else 6 * (n / 2) + 3

/-- The printed `⇒` fails: `A ⊕ N ≤₁ A` for every `A` containing the
multiples of 3 (simple sets among them, up to a recursive permutation). -/
theorem printed_forward_fails (A : Set ℕ) (hA : ∀ k, 3 * k ∈ A) :
    Function.Injective g ∧ ∀ n, n ∈ join A Set.univ ↔ g n ∈ A := by
  refine ⟨?_, ?_⟩
  · intro a b h
    unfold g at h
    split_ifs at h <;> omega
  · intro n
    obtain ⟨x, rfl | rfl⟩ : ∃ x, n = 2 * x ∨ n = 2 * x + 1 := ⟨n / 2, by omega⟩
    · rw [mem_join_even]
      unfold g
      have h2 : 2 * x / 2 = x := by omega
      have he : 2 * x % 2 = 0 := by omega
      simp only [he, h2, ite_true]
      split_ifs with h3
      · have hx : x = 3 * (x / 3) := by omega
        have hn : 2 * x = 3 * (2 * (x / 3)) := by omega
        rw [hn]
        exact ⟨fun _ => hA _, fun _ => hx ▸ hA _⟩
      · exact Iff.rfl
    · rw [mem_join_odd]
      unfold g
      have ho : (2 * x + 1) % 2 = 1 := by omega
      have h2 : (2 * x + 1) / 2 = x := by omega
      simp only [ho, h2, Set.mem_univ, true_iff]
      have hn : 6 * x + 3 = 3 * (2 * x + 1) := by omega
      simp only [show ¬ (1 = 0) from by omega, ite_false]
      rw [hn]
      exact hA _

end RogersRecursive.Ch08_09.Cylinder

#print axioms RogersRecursive.Ch08_09.Cylinder.mem_join_even
#print axioms RogersRecursive.Ch08_09.Cylinder.mem_join_odd
#print axioms RogersRecursive.Ch08_09.Cylinder.iterate_aux
#print axioms RogersRecursive.Ch08_09.Cylinder.iterate_reduction
#print axioms RogersRecursive.Ch08_09.Cylinder.printed_backward_fails
#print axioms RogersRecursive.Ch08_09.Cylinder.printed_forward_fails
