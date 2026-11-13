import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.WellFounded

/-!
# Finite-path trees and their ordinals (§ 16.3)

Places in the book (§ 16.3, pp. 502-507; §§ 16.4, 16.8):

* p. 503 and exercise 16-21 (`ex:finite-path-subtree`): a tree is a
  finite-path tree (no infinite branch) iff `(∀f)(∃x)[f̄(x) ∉ τ]`
  (`finitePath_iff_functions`), iff the relation "lies immediately below"
  on `τ` is well founded (`finitePath_iff_wf`).
* The ordinals `o_τ` of p. 503 (`ordAt`: 1 at a terminal vertex, else the
  least ordinal above the values at the vertices below) and `o(τ)`
  (`treeOrd`, 0 for the empty tree).  The sprouts of p. 505 (`sprout`):
  `o_(σ_n)(y) = o_τ(n ⊛ y)` (`ordAt_sprout`), and for a nonempty tree
  `o(τ) = sup_n (o(σ_n) + 1)` (`treeOrd_eq`).
* The basic tree lemma (`lem:basic-tree-lemma`, p. 505) in both printed
  forms (`basic_tree_lemma`, `basic_tree_lemma_two`), from the ordinal
  lemmas `ord_lemma`, `ord_lemma_two`.
* The examples of pp. 502-504: `o(𝒜₃) = 4` (`A3_ord`, with
  `A3_eq : 𝒜₃ = {(), ⟨0⟩, ⟨0, 0⟩, ⟨0, 0, 0⟩}`), `o(𝒜₅) = ω` (`A5_ord`);
  every chain of `m + 1` vertices has ordinal `m + 1` (`chain_ord`).
* The end of the proof of corollary 16-XXII (b) (`cor:boundedness-uniform`,
  p. 512): the tree with all sprouts equal to `τ` has ordinal `o(τ) + 1`
  (`succTree_ord`); the case `y = 2^s` of the proof of theorem 16-LI
  (`th:delta11-below-h`, p. 564): `o(x) < o(τ) + 1 ↔ [o(x) = 0 or all
  sprouts of x are below o(τ)]` (`succ_case`).

Notation: a vertex `⟨y₁, ..., y_k⟩` is the list `[y₁, ..., y_k]`, so
`n ⊛ y` is `n :: y`; trees are sets of lists closed under initial
segments (`IsTree`).  The book defines `o_τ(a)` through all vertices below
`a`; here through the immediate successors (the same ordinal).

Not covered: codes of tuples (they are bijective, § 5.6), recursive trees,
the transfinite cases of the sum and product of trees (exercise 16-25),
the Kleene-Brouwer ordering.
-/

namespace RogersRecursive.Ch15_16.Trees

open Ordinal

/-- A tree: closed under initial segments. -/
def IsTree (τ : Set (List ℕ)) : Prop := ∀ a b : List ℕ, a ++ b ∈ τ → a ∈ τ

/-- `b` lies immediately below `a` in `τ`. -/
def Child (τ : Set (List ℕ)) (b a : List ℕ) : Prop := b ∈ τ ∧ ∃ k, b = a ++ [k]

/-- Every branch is finite: no infinite chain of vertices from the top. -/
def FinitePath (τ : Set (List ℕ)) : Prop :=
  ¬ ∃ c : ℕ → List ℕ, c 0 = [] ∧ ∀ n, Child τ (c (n + 1)) (c n)

theorem finitePath_of_wf {τ : Set (List ℕ)} (h : WellFounded (Child τ)) : FinitePath τ := by
  rintro ⟨c, -, hc⟩
  have key : ∀ a, ∀ c : ℕ → List ℕ, c 0 = a → ¬ ∀ n, Child τ (c (n + 1)) (c n) := by
    intro a
    refine h.induction (C := fun a => ∀ c : ℕ → List ℕ, c 0 = a →
      ¬ ∀ n, Child τ (c (n + 1)) (c n)) a ?_
    intro a ih c h0 hc
    exact ih (c 1) (h0 ▸ hc 0) (fun n => c (n + 1)) rfl (fun n => hc (n + 1))
  exact key _ c rfl hc

theorem wf_of_finitePath {τ : Set (List ℕ)} (ht : IsTree τ) (h : FinitePath τ) :
    WellFounded (Child τ) := by
  refine ⟨fun a => ?_⟩
  by_contra hacc
  obtain ⟨d, hd0, hd⟩ := not_acc_iff_exists_descending_chain.1 hacc
  have ha : a ∈ τ := by
    obtain ⟨hmem, k, hk⟩ := hd 0
    rw [hd0] at hk
    exact ht a [k] (hk ▸ hmem)
  apply h
  refine ⟨fun n => if n ≤ a.length then a.take n else d (n - a.length), by simp, fun n => ?_⟩
  rcases lt_trichotomy n a.length with hn | hn | hn
  · have h1 : n + 1 ≤ a.length := hn
    have h2 : n ≤ a.length := hn.le
    simp only [h1, h2, ↓reduceIte]
    refine ⟨ht _ (a.drop (n + 1)) (by rw [List.take_append_drop]; exact ha), a[n], ?_⟩
    exact List.take_succ_eq_append_getElem hn
  · have h1 : ¬ n + 1 ≤ a.length := by omega
    have h2 : n ≤ a.length := hn.le
    simp only [h1, h2, ↓reduceIte]
    have e : n + 1 - a.length = 0 + 1 := by omega
    rw [e, hn, List.take_length, ← hd0]
    exact hd 0
  · have h1 : ¬ n + 1 ≤ a.length := by omega
    have h2 : ¬ n ≤ a.length := by omega
    simp only [h1, h2, ↓reduceIte]
    have e : n + 1 - a.length = (n - a.length) + 1 := by omega
    rw [e]
    exact hd _

/-- Finite-path trees are exactly the trees with a well-founded relation
"lies immediately below". -/
theorem finitePath_iff_wf {τ : Set (List ℕ)} (ht : IsTree τ) :
    FinitePath τ ↔ WellFounded (Child τ) :=
  ⟨wf_of_finitePath ht, finitePath_of_wf⟩

/-- `⟨f(0), ..., f(x - 1)⟩`, the tuple coded by `f̄(x)`. -/
def pre (f : ℕ → ℕ) (x : ℕ) : List ℕ := List.ofFn fun i : Fin x => f i

theorem pre_succ (f : ℕ → ℕ) (x : ℕ) : pre f (x + 1) = pre f x ++ [f x] := by
  unfold pre
  rw [List.ofFn_succ_last]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- Exercise 16-21 (p. 503): `τ` is a finite-path tree iff
`(∀f)(∃x)[f̄(x) ∉ τ]`. -/
theorem finitePath_iff_functions {τ : Set (List ℕ)} (ht : IsTree τ) :
    FinitePath τ ↔ ∀ f : ℕ → ℕ, ∃ x, pre f x ∉ τ := by
  constructor
  · intro h f
    by_contra hf
    simp only [not_exists, not_not] at hf
    exact h ⟨pre f, rfl, fun n => ⟨hf (n + 1), f n, pre_succ f n⟩⟩
  · rintro h ⟨c, hc0, hc⟩
    choose k hk using fun n => (hc n).2
    have hcn : ∀ n, c n = pre k n := by
      intro n
      induction n with
      | zero => simpa [pre] using hc0
      | succ n ih => rw [hk n, ih, pre_succ]
    obtain ⟨x, hx⟩ := h k
    apply hx
    rw [← hcn]
    cases x with
    | zero =>
      have := (hc 0).1
      exact hc0 ▸ ht [] _ (by simpa using this)
    | succ x => exact (hc x).1

/-! ### The ordinals of a tree -/

/-- The function `o_τ` of p. 503. -/
noncomputable def ordAt (τ : Set (List ℕ)) (a : List ℕ) : Ordinal.{0} := by
  classical
  exact if h : WellFounded (Child τ) then
    WellFounded.fix (C := fun _ => Ordinal.{0}) h (fun a IH => max (1 : Ordinal.{0})
      (⨆ k : {k : ℕ // a ++ [k] ∈ τ}, IH (a ++ [k.1]) ⟨k.2, k.1, rfl⟩ + 1)) a
  else 0

theorem ordAt_eq {τ : Set (List ℕ)} (h : WellFounded (Child τ)) (a : List ℕ) :
    ordAt τ a = max 1 (⨆ k : {k : ℕ // a ++ [k] ∈ τ}, ordAt τ (a ++ [k.1]) + 1) := by
  have e : ∀ x, ordAt τ x = WellFounded.fix (C := fun _ => Ordinal.{0}) h
      (fun a IH => max (1 : Ordinal.{0})
        (⨆ k : {k : ℕ // a ++ [k] ∈ τ}, IH (a ++ [k.1]) ⟨k.2, k.1, rfl⟩ + 1)) x := fun x => by
    rw [ordAt, dite_eq_left h]
  rw [e a, h.fix_eq]
  simp only [e]

/-- The ordinal `o(τ)` of a tree (0 for the empty tree). -/
noncomputable def treeOrd (τ : Set (List ℕ)) : Ordinal.{0} := by
  classical
  exact if [] ∈ τ then ordAt τ [] else 0

/-- The `n`-th sprout: the `y` with `n ⊛ y ∈ τ`. -/
def sprout (n : ℕ) (τ : Set (List ℕ)) : Set (List ℕ) := {y | n :: y ∈ τ}

theorem IsTree.sprout {τ : Set (List ℕ)} (h : IsTree τ) (n : ℕ) : IsTree (sprout n τ) :=
  fun a b hab => h (n :: a) b hab

theorem wf_sprout {τ : Set (List ℕ)} (h : WellFounded (Child τ)) (n : ℕ) :
    WellFounded (Child (sprout n τ)) :=
  Subrelation.wf (r := InvImage (Child τ) (fun y => n :: y))
    (fun {b a} hba => match hba with
      | ⟨hb, k, hk⟩ => ⟨hb, k, by subst hk; rfl⟩) (InvImage.wf _ h)

/-- Two suprema over subtypes of ℕ with the same condition. -/
theorem iSup_congr_sub {p q : ℕ → Prop} (hpq : ∀ k, p k ↔ q k) (f g : ℕ → Ordinal.{0})
    (hfg : ∀ k, p k → f k = g k) :
    (⨆ k : {k // p k}, f k.1) = ⨆ k : {k // q k}, g k.1 := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun k => (hfg k.1 k.2).le.trans
      (Ordinal.le_iSup (fun k : {k // q k} => g k.1) ⟨k.1, (hpq k.1).1 k.2⟩)
  · exact Ordinal.iSup_le fun k => (hfg k.1 ((hpq k.1).2 k.2)).symm.le.trans
      (Ordinal.le_iSup (fun k : {k // p k} => f k.1) ⟨k.1, (hpq k.1).2 k.2⟩)

/-- `o_(σ_n)(y) = o_τ(n ⊛ y)`. -/
theorem ordAt_sprout {τ : Set (List ℕ)} (h : WellFounded (Child τ)) (n : ℕ) (y : List ℕ) :
    ordAt (sprout n τ) y = ordAt τ (n :: y) := by
  refine (wf_sprout h n).induction (C := fun y => ordAt (sprout n τ) y = ordAt τ (n :: y)) y ?_
  intro y ih
  rw [ordAt_eq (wf_sprout h n), ordAt_eq h]
  congr 1
  exact iSup_congr_sub (fun k => Iff.rfl) (fun k => ordAt (sprout n τ) (y ++ [k]) + 1)
    (fun k => ordAt τ ((n :: y) ++ [k]) + 1) (fun k hk => by simp only [ih _ ⟨hk, k, rfl⟩, List.cons_append])

theorem treeOrd_sprout_pos {τ : Set (List ℕ)} (h : WellFounded (Child τ)) {n : ℕ}
    (hn : [n] ∈ τ) : treeOrd (sprout n τ) = ordAt τ [n] := by
  have : [] ∈ sprout n τ := hn
  simp only [treeOrd, this, ↓reduceIte]
  exact ordAt_sprout h n []

theorem treeOrd_sprout_neg {τ : Set (List ℕ)} {n : ℕ} (hn : [n] ∉ τ) :
    treeOrd (sprout n τ) = 0 := by
  have : [] ∉ sprout n τ := hn
  simp [treeOrd, this]

theorem one_le_succ (a : Ordinal.{0}) : 1 ≤ a + 1 := by
  simp

/-- For a nonempty tree, `o(τ) = sup_n (o(σ_n) + 1)`. -/
theorem treeOrd_eq {τ : Set (List ℕ)} (h : WellFounded (Child τ)) (hr : [] ∈ τ) :
    treeOrd τ = ⨆ n : ℕ, (treeOrd (sprout n τ) + 1) := by
  classical
  have e : treeOrd τ = ordAt τ [] := by simp [treeOrd, hr]
  rw [e, ordAt_eq h]
  apply le_antisymm
  · apply max_le
    · exact (one_le_succ _).trans (Ordinal.le_iSup (fun n => treeOrd (sprout n τ) + 1) 0)
    · refine Ordinal.iSup_le fun k => ?_
      have hk : [k.1] ∈ τ := k.2
      have : treeOrd (sprout k.1 τ) = ordAt τ [k.1] := treeOrd_sprout_pos h hk
      calc ordAt τ ([] ++ [k.1]) + 1 = treeOrd (sprout k.1 τ) + 1 := by rw [this]; rfl
        _ ≤ _ := Ordinal.le_iSup (fun n => treeOrd (sprout n τ) + 1) k.1
  · refine Ordinal.iSup_le fun n => ?_
    by_cases hn : [n] ∈ τ
    · rw [treeOrd_sprout_pos h hn]
      exact (Ordinal.le_iSup (fun k : {k : ℕ // [] ++ [k] ∈ τ} => ordAt τ ([] ++ [k.1]) + 1)
        ⟨n, hn⟩).trans (le_max_right _ _)
    · rw [treeOrd_sprout_neg hn, zero_add]
      exact le_max_left _ _

theorem treeOrd_empty {τ : Set (List ℕ)} (ht : IsTree τ) (hr : [] ∉ τ) :
    treeOrd τ = 0 ∧ ∀ n, treeOrd (sprout n τ) = 0 := by
  classical
  refine ⟨by simp [treeOrd, hr], fun n => ?_⟩
  have : [] ∉ sprout n τ := fun hn => hr (ht [] [n] hn)
  simp [treeOrd, this]

theorem tree_cases {τ : Set (List ℕ)} (ht : IsTree τ) (h : WellFounded (Child τ)) :
    (treeOrd τ = 0 ∧ ∀ n, treeOrd (sprout n τ) = 0) ∨
      treeOrd τ = ⨆ n : ℕ, (treeOrd (sprout n τ) + 1) := by
  by_cases hr : [] ∈ τ
  · exact Or.inr (treeOrd_eq h hr)
  · exact Or.inl (treeOrd_empty ht hr)

/-! ### The basic tree lemma -/

theorem iSup_succ_ne_zero (a : ℕ → Ordinal.{0}) : (⨆ n, (a n + 1)) ≠ 0 := by
  intro h0
  have := (one_le_succ (a 0)).trans (Ordinal.le_iSup (fun n => a n + 1) 0)
  rw [h0] at this
  exact absurd this (by simp)

/-- The ordinal form of the basic tree lemma, first printed form. -/
theorem ord_lemma (a b : ℕ → Ordinal.{0}) (o₁ o₂ : Ordinal.{0})
    (h₁ : (o₁ = 0 ∧ ∀ n, a n = 0) ∨ o₁ = ⨆ n, (a n + 1))
    (h₂ : (o₂ = 0 ∧ ∀ n, b n = 0) ∨ o₂ = ⨆ n, (b n + 1)) :
    o₁ < o₂ ↔ ((o₁ = 0 ∧ o₂ = 1) ∨ ∃ m, ∀ n, a n < b m) := by
  rcases h₁ with ⟨rfl, ha⟩ | rfl <;> rcases h₂ with ⟨rfl, hb⟩ | rfl
  · simp [hb]
  · have hne := iSup_succ_ne_zero b
    constructor
    · intro _
      by_cases hpos : ∃ m, 0 < b m
      · obtain ⟨m, hm⟩ := hpos
        exact Or.inr ⟨m, fun n => by rw [ha n]; exact hm⟩
      · have hb0 : ∀ m, b m = 0 := fun m => by
          by_contra hm
          exact hpos ⟨m, pos_iff_ne_zero.2 hm⟩
        exact Or.inl ⟨rfl, by simp [hb0]⟩
    · intro _
      exact pos_iff_ne_zero.2 hne
  · simp [hb, iSup_succ_ne_zero a]
  · rw [Ordinal.lt_iSup_iff]
    simp only [Order.lt_add_one_iff, Ordinal.iSup_add_one_le_iff, iSup_succ_ne_zero a,
      false_and, false_or]

/-- The ordinal form of the basic tree lemma, second printed form. -/
theorem ord_lemma_two (a b : ℕ → Ordinal.{0}) (o₁ o₂ : Ordinal.{0})
    (h₁ : (o₁ = 0 ∧ ∀ n, a n = 0) ∨ o₁ = ⨆ n, (a n + 1))
    (h₂ : (o₂ = 0 ∧ ∀ n, b n = 0) ∨ o₂ = ⨆ n, (b n + 1)) :
    o₁ < o₂ ↔ (o₂ ≠ 0 ∧ (o₁ = 0 ∨ ∃ m, ∀ n, a n < b m)) := by
  rcases h₁ with ⟨rfl, ha⟩ | rfl <;> rcases h₂ with ⟨rfl, hb⟩ | rfl
  · simp
  · have hne := iSup_succ_ne_zero b
    simp only [hne, ne_eq, not_false_eq_true, true_and, true_or, iff_true]
    exact pos_iff_ne_zero.2 hne
  · simp [hb]
  · rw [Ordinal.lt_iSup_iff]
    simp only [Order.lt_add_one_iff, Ordinal.iSup_add_one_le_iff, iSup_succ_ne_zero a,
      iSup_succ_ne_zero b, ne_eq, not_false_eq_true, true_and, false_or]

/-- The basic tree lemma (p. 505), first form. -/
theorem basic_tree_lemma {τ₁ τ₂ : Set (List ℕ)} (ht₁ : IsTree τ₁) (ht₂ : IsTree τ₂)
    (hf₁ : FinitePath τ₁) (hf₂ : FinitePath τ₂) :
    treeOrd τ₁ < treeOrd τ₂ ↔ ((treeOrd τ₁ = 0 ∧ treeOrd τ₂ = 1) ∨
      ∃ m, ∀ n, treeOrd (sprout n τ₁) < treeOrd (sprout m τ₂)) :=
  ord_lemma _ _ _ _ (tree_cases ht₁ (wf_of_finitePath ht₁ hf₁))
    (tree_cases ht₂ (wf_of_finitePath ht₂ hf₂))

/-- The basic tree lemma (p. 505), second form. -/
theorem basic_tree_lemma_two {τ₁ τ₂ : Set (List ℕ)} (ht₁ : IsTree τ₁) (ht₂ : IsTree τ₂)
    (hf₁ : FinitePath τ₁) (hf₂ : FinitePath τ₂) :
    treeOrd τ₁ < treeOrd τ₂ ↔ (treeOrd τ₂ ≠ 0 ∧ (treeOrd τ₁ = 0 ∨
      ∃ m, ∀ n, treeOrd (sprout n τ₁) < treeOrd (sprout m τ₂))) :=
  ord_lemma_two _ _ _ _ (tree_cases ht₁ (wf_of_finitePath ht₁ hf₁))
    (tree_cases ht₂ (wf_of_finitePath ht₂ hf₂))

/-! ### Trees given by their sprouts -/

/-- A tree whose sprouts are well founded is well founded. -/
theorem wf_of_sprouts {τ : Set (List ℕ)} (h : ∀ n, WellFounded (Child (sprout n τ))) :
    WellFounded (Child τ) := by
  have hcons : ∀ n y, Acc (Child (sprout n τ)) y → Acc (Child τ) (n :: y) := by
    intro n y hy
    induction hy with
    | intro y _ ih =>
      refine ⟨_, fun b hb => ?_⟩
      obtain ⟨hbm, k, rfl⟩ := hb
      exact ih (y ++ [k]) ⟨hbm, k, rfl⟩
  refine ⟨fun a => ?_⟩
  cases a with
  | cons n y => exact hcons n y ((h n).apply y)
  | nil =>
    refine ⟨_, fun b hb => ?_⟩
    obtain ⟨-, k, rfl⟩ := hb
    exact hcons k [] ((h k).apply [])

/-- All vertices of bounded length: well founded. -/
theorem wf_of_bounded {τ : Set (List ℕ)} (m : ℕ) (hb : ∀ l ∈ τ, l.length ≤ m) :
    WellFounded (Child τ) :=
  Subrelation.wf (r := InvImage (· < ·) (fun l : List ℕ => m - l.length))
    (fun {b a} hba => by
      obtain ⟨hbm, k, rfl⟩ := hba
      have := hb _ hbm
      simp only [List.length_append, List.length_singleton] at this
      show m - (a ++ [k]).length < m - a.length
      simp only [List.length_append, List.length_singleton]
      omega)
    (InvImage.wf _ wellFounded_lt)

/-- A chain of `m + 1` vertices labelled by `g`. -/
def chain (g : ℕ → ℕ) (m : ℕ) : Set (List ℕ) :=
  {l | l.length ≤ m ∧ ∀ i (hi : i < l.length), l[i] = g i}

theorem chain_isTree (g : ℕ → ℕ) (m : ℕ) : IsTree (chain g m) := by
  intro a b ⟨hl, hg⟩
  simp only [List.length_append] at hl
  refine ⟨by omega, fun i hi => ?_⟩
  have := hg i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

theorem chain_wf (g : ℕ → ℕ) (m : ℕ) : WellFounded (Child (chain g m)) :=
  wf_of_bounded m fun _ hl => hl.1

theorem chain_root (g : ℕ → ℕ) (m : ℕ) : [] ∈ chain g m :=
  ⟨by simp, fun i hi => absurd hi (by simp)⟩

theorem sprout_chain_zero (g : ℕ → ℕ) (n : ℕ) : [] ∉ sprout n (chain g 0) := by
  intro h
  have := h.1
  simp at this

theorem sprout_chain_succ (g : ℕ → ℕ) (m n : ℕ) :
    sprout n (chain g (m + 1)) = if n = g 0 then chain (fun i => g (i + 1)) m else ∅ := by
  ext y
  simp only [sprout, chain, Set.mem_ofPred_eq, List.length_cons]
  split_ifs with hn
  · subst hn
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hl, hg⟩
      refine ⟨by omega, fun i hi => ?_⟩
      have := hg (i + 1) (by omega)
      simpa using this
    · rintro ⟨hl, hg⟩
      refine ⟨by omega, fun i hi => ?_⟩
      cases i with
      | zero => rfl
      | succ i => simpa using hg i (by simpa using hi)
  · simp only [Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hg
    exact hn (by simpa using hg 0 (by simp))

/-- A chain of `m + 1` vertices has ordinal `m + 1`. -/
theorem chain_ord (m : ℕ) : ∀ g : ℕ → ℕ, treeOrd (chain g m) = (m : Ordinal) + 1 := by
  classical
  induction m with
  | zero =>
    intro g
    rw [treeOrd_eq (chain_wf g 0) (chain_root g 0)]
    have : ∀ n, treeOrd (sprout n (chain g 0)) = 0 := fun n => by
      simp [treeOrd, sprout_chain_zero g n]
    simp [this]
  | succ m ih =>
    intro g
    rw [treeOrd_eq (chain_wf g (m + 1)) (chain_root g (m + 1))]
    have hs : ∀ n, treeOrd (sprout n (chain g (m + 1))) =
        if n = g 0 then (m : Ordinal) + 1 else 0 := fun n => by
      rw [sprout_chain_succ]
      split_ifs
      · exact ih _
      · simp [treeOrd]
    simp only [hs]
    apply le_antisymm
    · refine Ordinal.iSup_le fun n => ?_
      split_ifs
      · simp
      · simp
    · refine le_trans ?_ (Ordinal.le_iSup (fun n => (if n = g 0 then (m : Ordinal) + 1 else 0) + 1) (g 0))
      simp

/-! ### The examples 𝒜₃ and 𝒜₅ (pp. 502-504) -/

/-- 𝒜₃ = {(), ⟨0⟩, ⟨0, 0⟩, ⟨0, 0, 0⟩}. -/
def A3 : Set (List ℕ) := chain (fun _ => 0) 3

theorem A3_eq : A3 = {[], [0], [0, 0], [0, 0, 0]} := by
  ext l
  simp only [A3, chain, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hl, hg⟩
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
    · exact Or.inl rfl
    · have ha : a = 0 := by simpa using hg 0 (by simp)
      exact Or.inr (Or.inl (by rw [ha]))
    · have ha : a = 0 := by simpa using hg 0 (by simp)
      have hb : b = 0 := by simpa using hg 1 (by simp)
      exact Or.inr (Or.inr (Or.inl (by rw [ha, hb])))
    · have ha : a = 0 := by simpa using hg 0 (by simp)
      have hb : b = 0 := by simpa using hg 1 (by simp)
      have hc : c = 0 := by simpa using hg 2 (by simp)
      exact Or.inr (Or.inr (Or.inr (by rw [ha, hb, hc])))
    · simp only [List.length_cons] at hl
      omega
  · have zeros : ∀ l : List ℕ, (∀ x ∈ l, x = 0) → ∀ i (hi : i < l.length), l[i] = 0 :=
      fun l h i hi => h _ (List.getElem_mem hi)
    rintro (rfl | rfl | rfl | rfl) <;> exact ⟨by simp, zeros _ (by simp)⟩

theorem A3_ord : treeOrd A3 = 4 := by
  rw [A3, chain_ord, ← Nat.cast_succ]
  rfl

/-- 𝒜₅: the empty tuple and the tuples ⟨n, n + 1, ..., m⟩, n ≤ m ≤ 2n. -/
def A5 : Set (List ℕ) :=
  {l | l = [] ∨ ∃ n, 1 ≤ l.length ∧ l.length ≤ n + 1 ∧ ∀ i (hi : i < l.length), l[i] = n + i}

theorem sprout_A5 (n : ℕ) : sprout n A5 = chain (fun i => n + 1 + i) n := by
  ext y
  simp only [sprout, A5, chain, Set.mem_ofPred_eq, List.length_cons, reduceCtorEq, false_or]
  constructor
  · rintro ⟨n', -, hl, hg⟩
    have h0 : n = n' := by simpa using hg 0 (by simp)
    subst h0
    refine ⟨by omega, fun i hi => ?_⟩
    have := hg (i + 1) (by omega)
    simp only [List.getElem_cons_succ] at this
    omega
  · rintro ⟨hl, hg⟩
    refine ⟨n, by omega, by omega, fun i hi => ?_⟩
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [hg i (by simpa using hi)]
      omega

theorem A5_isTree : IsTree A5 := by
  intro a b hab
  rcases hab with h | ⟨n, h1, hl, hg⟩
  · left
    exact List.append_eq_nil_iff.1 h |>.1
  · rcases a with _ | ⟨x, a⟩
    · left; rfl
    · right
      refine ⟨n, by simp, by simp at hl ⊢; omega, fun i hi => ?_⟩
      have := hg i (by simp at hi ⊢; omega)
      rwa [List.getElem_append_left hi] at this

theorem A5_wf : WellFounded (Child A5) :=
  wf_of_sprouts fun n => by rw [sprout_A5]; exact chain_wf _ _

/-- o(𝒜₅) = ω. -/
theorem A5_ord : treeOrd A5 = ω := by
  rw [treeOrd_eq A5_wf (Or.inl rfl)]
  simp only [sprout_A5, chain_ord]
  apply le_antisymm
  · refine Ordinal.iSup_le fun n => ?_
    have : (n : Ordinal) + 1 + 1 = ((n + 2 : ℕ) : Ordinal) := by
      rw [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two]
    rw [this]
    exact (Ordinal.natCast_lt_omega0 _).le
  · rw [← Ordinal.iSup_natCast]
    refine Ordinal.iSup_le fun n => ?_
    refine le_trans ?_ (Ordinal.le_iSup (fun n : ℕ => (n : Ordinal) + 1 + 1) n)
    exact le_self_add.trans le_self_add

/-! ### The tree of the end of the proof of corollary 16-XXII (b) -/

/-- The tree with the top vertex and every sprout equal to `τ`
(`ψ(0) = 1`, `ψ(n ⊛ s) = φ_y(s)`). -/
def succTree (τ : Set (List ℕ)) : Set (List ℕ) := {l | l = [] ∨ ∃ n y, l = n :: y ∧ y ∈ τ}

theorem sprout_succTree (τ : Set (List ℕ)) (n : ℕ) : sprout n (succTree τ) = τ := by
  ext y
  simp [sprout, succTree]

theorem succTree_isTree {τ : Set (List ℕ)} (ht : IsTree τ) : IsTree (succTree τ) := by
  intro a b hab
  rcases hab with h | ⟨n, y, h, hy⟩
  · exact Or.inl (List.append_eq_nil_iff.1 h).1
  · rcases a with _ | ⟨x, a⟩
    · exact Or.inl rfl
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨x, a, rfl, ht a b hy⟩

/-- `‖h(y)‖ = ‖y‖ + 1` (p. 512). -/
theorem succTree_ord {τ : Set (List ℕ)} (hf : WellFounded (Child τ)) :
    treeOrd (succTree τ) = treeOrd τ + 1 := by
  have hw : WellFounded (Child (succTree τ)) :=
    wf_of_sprouts fun n => by rw [sprout_succTree]; exact hf
  rw [treeOrd_eq hw (Or.inl rfl)]
  simp only [sprout_succTree, ciSup_const]

/-- The case `y = 2^s` of the proof of theorem 16-LI (p. 564):
`o(x) < o(τ) + 1 ↔ [o(x) = 0 or (∀n) o(σ_n) < o(τ)]`. -/
theorem succ_case {x τ : Set (List ℕ)} (hx : IsTree x) (ht : IsTree τ)
    (fx : FinitePath x) (fτ : FinitePath τ) :
    treeOrd x < treeOrd τ + 1 ↔ (treeOrd x = 0 ∨ ∀ n, treeOrd (sprout n x) < treeOrd τ) := by
  have wτ := wf_of_finitePath ht fτ
  have fs : FinitePath (succTree τ) :=
    finitePath_of_wf (wf_of_sprouts fun n => by rw [sprout_succTree]; exact wτ)
  have := basic_tree_lemma_two hx (succTree_isTree ht) fx fs
  rw [succTree_ord wτ] at this
  rw [this]
  simp only [sprout_succTree, exists_const, ne_eq, add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, true_and]

end RogersRecursive.Ch15_16.Trees

#print axioms RogersRecursive.Ch15_16.Trees.finitePath_iff_wf
#print axioms RogersRecursive.Ch15_16.Trees.finitePath_iff_functions
#print axioms RogersRecursive.Ch15_16.Trees.ordAt_sprout
#print axioms RogersRecursive.Ch15_16.Trees.treeOrd_eq
#print axioms RogersRecursive.Ch15_16.Trees.ord_lemma
#print axioms RogersRecursive.Ch15_16.Trees.ord_lemma_two
#print axioms RogersRecursive.Ch15_16.Trees.basic_tree_lemma
#print axioms RogersRecursive.Ch15_16.Trees.basic_tree_lemma_two
#print axioms RogersRecursive.Ch15_16.Trees.chain_ord
#print axioms RogersRecursive.Ch15_16.Trees.A3_eq
#print axioms RogersRecursive.Ch15_16.Trees.A3_ord
#print axioms RogersRecursive.Ch15_16.Trees.A5_ord
#print axioms RogersRecursive.Ch15_16.Trees.succTree_ord
#print axioms RogersRecursive.Ch15_16.Trees.succ_case
