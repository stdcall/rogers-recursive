/-
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная
вычислимость» (Мир, 1972): theorem 11-XI (the weak recursion theorem for
enumeration operators, § 11.5, pp. 249-250), parts (i) and (ii), and the
step with the function h in Young's theorem 10-IV (§ 10.3, p. 218).

Theorem XI.  Φ : 2^ℕ → 2^ℕ is monotone and continuous in the sense of
theorem 9-XXI (x ∈ Φ(B) ⇒ x ∈ Φ(D) for a finite D ⊆ B), the only
properties of enumeration operators the proof uses; A_0 = ∅,
A_(n+1) = Φ(A_n), A = ⋃_n A_n.  Proved: A_n ⊆ A_(n+1), Φ(A) = A, and
A ⊆ B for every B with Φ(B) = B.  Not covered: (iii) (A is r.e.).

Theorem IV (Young).  g one-one with B = g⁻¹(D), m ∉ D, n ∉ D, n not a
value of g, h(x) = n if g(x) = m, g(x) otherwise: h is one-one and
B = h⁻¹(D ∪ {m}); with f as in the proof (m not a value of f),
A = f⁻¹(D ∪ {m}).  So D ∪ {m} is an upper bound of A and B under ≤_1.
Not covered: simplicity, Tennenbaum's exercise 10-10 and the lemma of
theorem 8-XIV used by the proof.
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

namespace RogersRecursive.Ch10_12.Sets

section WeakRecursion

variable (Φ : Set ℕ → Set ℕ)

/-- A_n = Φ^n(∅). -/
def stage (n : ℕ) : Set ℕ := Φ^[n] ∅

/-- A = ⋃_n A_n. -/
def limitSet : Set ℕ := {x | ∃ n, x ∈ stage Φ n}

variable {Φ}

theorem stage_succ (n : ℕ) : stage Φ (n + 1) = Φ (stage Φ n) := by
  simp only [stage, Function.iterate_succ_apply']

theorem stage_mono (hmono : ∀ A B, A ⊆ B → Φ A ⊆ Φ B) : Monotone (stage Φ) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => intro x hx; exact absurd hx (by simp [stage])
  | succ n ih => rw [stage_succ, stage_succ]; exact hmono _ _ ih

/-- A finite subset of A lies in some A_n. -/
theorem finite_in_stage (hmono : ∀ A B, A ⊆ B → Φ A ⊆ Φ B) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d ∈ limitSet Φ) : ∃ n, ∀ d ∈ D, d ∈ stage Φ n := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨n₁, h₁⟩ := hD a (Finset.mem_insert_self a s)
    obtain ⟨n₂, h₂⟩ := ih (fun d hd => hD d (Finset.mem_insert_of_mem hd))
    refine ⟨max n₁ n₂, fun d hd => ?_⟩
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact stage_mono hmono (le_max_left _ _) h₁
    · exact stage_mono hmono (le_max_right _ _) (h₂ d hd)

/-- Theorem XI (i): Φ(A) = A. -/
theorem fixed (hmono : ∀ A B, A ⊆ B → Φ A ⊆ Φ B)
    (hcont : ∀ B x, x ∈ Φ B → ∃ D : Finset ℕ, (∀ d ∈ D, d ∈ B) ∧ x ∈ Φ {y | y ∈ D}) :
    Φ (limitSet Φ) = limitSet Φ := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨D, hDA, hxD⟩ := hcont _ x hx
    obtain ⟨n, hn⟩ := finite_in_stage hmono D hDA
    refine ⟨n + 1, ?_⟩
    rw [stage_succ]
    exact hmono _ _ (fun y hy => hn y hy) hxD
  · rintro x ⟨n, hn⟩
    cases n with
    | zero => exact absurd hn (by simp [stage])
    | succ n =>
      rw [stage_succ] at hn
      exact hmono _ _ (fun y hy => show ∃ k, y ∈ stage Φ k from ⟨n, hy⟩) hn

/-- Theorem XI (ii): A is contained in every fixed point. -/
theorem least (hmono : ∀ A B, A ⊆ B → Φ A ⊆ Φ B) (B : Set ℕ) (hB : Φ B = B) :
    limitSet Φ ⊆ B := by
  have h : ∀ n, stage Φ n ⊆ B := by
    intro n
    induction n with
    | zero => intro x hx; exact absurd hx (by simp [stage])
    | succ n ih => rw [stage_succ, ← hB]; exact hmono _ _ ih
  rintro x ⟨n, hn⟩
  exact h n hn

end WeakRecursion

/-- Theorem IV (Young), the step with h. -/
theorem young_h (D B : Set ℕ) (g : ℕ → ℕ) (hg : Function.Injective g)
    (hB : ∀ x, x ∈ B ↔ g x ∈ D) (m n : ℕ) (hm : m ∉ D) (hn : n ∉ D)
    (hng : ∀ x, g x ≠ n) :
    Function.Injective (fun x => if g x = m then n else g x) ∧
      ∀ x, x ∈ B ↔ (if g x = m then n else g x) ∈ insert m D := by
  constructor
  · intro x y e
    dsimp only at e
    split_ifs at e with hx hy hy
    · exact hg (hx.trans hy.symm)
    · exact absurd e.symm (hng y)
    · exact absurd e (hng x)
    · exact hg e
  · intro x
    split_ifs with hx
    · rw [hB, hx, Set.mem_insert_iff]
      exact ⟨fun h => absurd h hm,
        fun h => h.elim (fun e => absurd (hx.trans e.symm) (hng x)) (fun e => absurd e hn)⟩
    · rw [hB, Set.mem_insert_iff]
      exact ⟨Or.inr, fun h => h.elim (fun e => absurd e hx) id⟩

/-- Theorem IV (Young), f: A ≤_1 D ∪ {m} by f when m is not a value of f. -/
theorem young_f (D A : Set ℕ) (f : ℕ → ℕ) (hA : ∀ x, x ∈ A ↔ f x ∈ D) (m : ℕ)
    (hmf : ∀ x, f x ≠ m) : ∀ x, x ∈ A ↔ f x ∈ insert m D := by
  intro x
  rw [Set.mem_insert_iff, hA]
  constructor
  · exact Or.inr
  · rintro (h | h)
    · exact absurd h (hmf x)
    · exact h

end RogersRecursive.Ch10_12.Sets

#print axioms RogersRecursive.Ch10_12.Sets.stage_succ
#print axioms RogersRecursive.Ch10_12.Sets.stage_mono
#print axioms RogersRecursive.Ch10_12.Sets.finite_in_stage
#print axioms RogersRecursive.Ch10_12.Sets.fixed
#print axioms RogersRecursive.Ch10_12.Sets.least
#print axioms RogersRecursive.Ch10_12.Sets.young_h
#print axioms RogersRecursive.Ch10_12.Sets.young_f
