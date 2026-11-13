import Mathlib.Data.Set.Finite.Basic

/-!
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная вычислимость»
(Мир, 1972), ch. 5–7: the diagonal and set-theoretic steps of theorems
5-VI, 5-XIV, 7-II (b), 7-V (b), 7-VII (lemma), 7-XII (c), the basic lemma
of § 7.8, and exercises 5-22, 6-8, 7-4, 7-22, 7-26, 7-49.

Notation.  `W : ℕ → Set ℕ` is an arbitrary sequence of sets standing for
W₀, W₁, … (§ 5.2); nothing about it is assumed beyond what each statement
lists, so every statement holds for the r. e. sets and their indices in
particular.  `Kset W` is K = {x | x ∈ Wₓ} (p. 88).  A partial function is
`ℕ → Option ℕ` (`none`: diverges); `ProductiveFn W A ψ` is the definition
of p. 115: W_x ⊂ A ⇒ [ψ(x) is defined & ψ(x) ∈ A − W_x].  A reduction of A
to B via f is `∀ x, x ∈ A ↔ f x ∈ B` (p. 110), without the requirement that
f be general recursive: where the book needs it, the statement says which
function is used and why it is recursive.

What is proved.  5-VI: no W_m is the complement of K (`compl_K_ne`; with
theorem 5-II this is the book's proof that K is not recursive).  5-XIV:
the printed «⇔» and «⇒» give the same condition, because «⇐» holds for
every ψ by theorem 5-II (`uniform_iff_imp`).  Examples of § 7.3 and p. 125:
K̄ is productive and completely productive with λx[x].  7-V (b): fψg is a
productive function for B.  The lemma of theorem 7-VII: the function g of
the proof has both properties.  7-XII (c): f(u, v) ∉ W_u ∪ W_v.  The basic
lemma of § 7.8 (exercise 7-55).  7-II (b): A ⊕ B and the function h of the
proof.  Exercise 7-4: the printed statement fails for A = N, B = N − {0}
(no function at all reduces B to N); for infinite A, B with finite
(A − B) ∪ (B − A), A is reducible to B by a function that differs from the
identity on a finite set exactly when B = N ⇒ A = N, so A ≡m B iff
[A = N ⇔ B = N] (the corrected statement assumes A, B ≠ N).  Exercises 7-22,
7-49: the productive functions λx[x] and f; 7-26: a productive function for
B̄.  Exercise 5-22: {1} ⨯ N and N ⨯ {1} are not isomorphic as relations
(no one-one f maps one onto the other componentwise).  Exercise 6-8.

Not covered: recursiveness and recursive enumerability (Church's thesis,
the s-m-n theorem: the index functions g, h, e, the sets A₀, A₁ are given
as hypotheses with the properties the book derives for them), the
infinity of f(K) in theorem 7-VII (sublemma (b)), the construction of f'.
-/

namespace RogersRecursive.Ch05_07

variable (W : ℕ → Set ℕ)

/-- K = {x | x ∈ Wₓ} (p. 88). -/
def Kset : Set ℕ := {x | x ∈ W x}

/-- Theorem 5-VI (p. 88): K̄ ≠ W_m for every m. -/
theorem compl_K_ne (m : ℕ) : W m ≠ (Kset W)ᶜ := by
  intro h
  have h1 : m ∈ W m ↔ m ∈ (Kset W)ᶜ := by rw [h]
  simp only [Kset, Set.mem_compl_iff, Set.mem_ofPred_eq] at h1
  exact iff_not_self h1

/-- Theorem 5-XIV (p. 95): with R x = "Wₓ is recursive" and C x = "ψ(x) is
defined and W_ψ(x) = W̄ₓ", C x ⇒ R x holds by theorem 5-II, so
∀x [R x ⇔ C x] and ∀x [R x ⇒ C x] are the same condition. -/
theorem uniform_iff_imp (R C : ℕ → Prop) (hCR : ∀ x, C x → R x) :
    (∀ x, R x ↔ C x) ↔ (∀ x, R x → C x) :=
  ⟨fun h x => (h x).1, fun h x => ⟨h x, hCR x⟩⟩

/-- ψ is a productive function for A (p. 115). -/
def ProductiveFn (A : Set ℕ) (ψ : ℕ → Option ℕ) : Prop :=
  ∀ x, W x ⊆ A → ∃ v, ψ x = some v ∧ v ∈ A ∧ v ∉ W x

/-- Example 1 of § 7.3 (p. 115): K̄ is productive with λx[x]. -/
theorem K_compl_productive : ProductiveFn W (Kset W)ᶜ some := by
  intro x hx
  refine ⟨x, rfl, ?_, ?_⟩
  · intro hK
    exact hx hK hK
  · intro hW
    exact hx hW hW

/-- P. 125: K̄ is completely productive with λx[x]. -/
theorem K_compl_completely_productive (x : ℕ) :
    (x ∈ W x ∧ x ∉ (Kset W)ᶜ) ∨ (x ∈ (Kset W)ᶜ ∧ x ∉ W x) := by
  by_cases h : x ∈ W x
  · exact Or.inl ⟨h, fun hc => hc h⟩
  · exact Or.inr ⟨h, h⟩

/-- Theorem 7-V (b) (p. 116): ψ productive for A, A = f⁻¹(B),
W_g(x) = f⁻¹(Wₓ) ⇒ fψg is a productive function for B. -/
theorem productive_transfer (A B : Set ℕ) (ψ : ℕ → Option ℕ) (f g : ℕ → ℕ)
    (hψ : ProductiveFn W A ψ) (hf : ∀ x, x ∈ A ↔ f x ∈ B)
    (hg : ∀ x, W (g x) = f ⁻¹' W x) :
    ProductiveFn W B (fun x => (ψ (g x)).map f) := by
  intro x hx
  have hsub : W (g x) ⊆ A := by
    intro y hy
    rw [hg] at hy
    exact (hf y).2 (hx hy)
  obtain ⟨v, hv, hvA, hvW⟩ := hψ (g x) hsub
  refine ⟨f v, by simp [hv], (hf v).1 hvA, ?_⟩
  intro hfv
  apply hvW
  rw [hg]
  exact hfv

/-- The basic lemma of § 7.8 (p. 131) and exercise 7-55: A ∩ B productive with
ψ and W_g(x) = Wₓ ∩ B ⇒ A productive with ψg. -/
theorem basic_lemma (A B : Set ℕ) (ψ : ℕ → Option ℕ) (g : ℕ → ℕ)
    (hψ : ProductiveFn W (A ∩ B) ψ) (hg : ∀ x, W (g x) = W x ∩ B) :
    ProductiveFn W A (fun x => ψ (g x)) := by
  intro x hx
  have hsub : W (g x) ⊆ A ∩ B := by
    rw [hg]
    exact fun y hy => ⟨hx hy.1, hy.2⟩
  obtain ⟨v, hv, ⟨hvA, hvB⟩, hvW⟩ := hψ (g x) hsub
  refine ⟨v, hv, hvA, fun h => hvW ?_⟩
  rw [hg]
  exact ⟨h, hvB⟩

open Classical in
/-- The lemma of theorem 7-VII (pp. 119–120).  f reduces K to A; for the
finite set D, the index i = h(x) has Wᵢ = N if D ∩ A ≠ ∅ and Wᵢ = f⁻¹(D)
otherwise; e is an element of f(K) outside D ("the first element of the
enumeration of f(K) not in D", which exists since f(K) is infinite);
g(x) = f(i) if f(i) ∉ D, e otherwise. -/
theorem cylinder_lemma (A D : Set ℕ) (f : ℕ → ℕ) (hf : ∀ x, x ∈ Kset W ↔ f x ∈ A)
    (i : ℕ) (hW : W i = if (D ∩ A).Nonempty then Set.univ else f ⁻¹' D)
    (e : ℕ) (heK : e ∈ f '' Kset W) (heD : e ∉ D) :
    ((D.Nonempty ∧ D ⊆ A) →
        (if f i ∈ D then e else f i) ∈ A ∧ (if f i ∈ D then e else f i) ∉ D) ∧
      ((D.Nonempty ∧ D ⊆ Aᶜ) →
        (if f i ∈ D then e else f i) ∈ Aᶜ ∧ (if f i ∈ D then e else f i) ∉ D) := by
  classical
  constructor
  · rintro ⟨⟨d, hd⟩, hDA⟩
    have hne : (D ∩ A).Nonempty := ⟨d, hd, hDA hd⟩
    rw [ite_eq_left hne] at hW
    have hK : i ∈ Kset W := by
      show i ∈ W i
      rw [hW]
      trivial
    by_cases h : f i ∈ D
    · rw [ite_eq_left h]
      obtain ⟨k, hk, rfl⟩ := heK
      exact ⟨(hf k).1 hk, heD⟩
    · rw [ite_eq_right h]
      exact ⟨(hf i).1 hK, h⟩
  · rintro ⟨_, hDA⟩
    have hne : ¬ (D ∩ A).Nonempty := by
      rintro ⟨y, hyD, hyA⟩
      exact hDA hyD hyA
    rw [ite_eq_right hne] at hW
    have hnD : f i ∉ D := by
      intro h
      have hK : i ∈ Kset W := by
        show i ∈ W i
        rw [hW]
        exact h
      exact hDA h ((hf i).1 hK)
    have hnK : i ∉ Kset W := by
      intro hK
      apply hnD
      have : i ∈ W i := hK
      rw [hW] at this
      exact this
    rw [ite_eq_right hnD]
    exact ⟨fun h => hnK ((hf i).2 h), hnD⟩

/-- Theorem 7-XII (c) (p. 127): d x = φₓ(x); c = f(u, v) is an index of η, so
c ∈ W_u ⇒ φ_c(c) = η(c) = 1 and c ∈ W_v ⇒ φ_c(c) = 0 (W_u ∩ W_v = ∅).
With A₀ ⊂ W_u, A₁ ⊂ W_v disjoint, c ∉ W_u ∪ W_v. -/
theorem inseparable_step (d : ℕ → Option ℕ) (Wu Wv : Set ℕ) (c : ℕ)
    (hc1 : c ∈ Wu → d c = some 1) (hc0 : c ∈ Wv → d c = some 0)
    (h0 : {x | d x = some 0} ⊆ Wu) (h1 : {x | d x = some 1} ⊆ Wv)
    (hdisj : Disjoint Wu Wv) : c ∉ Wu ∪ Wv := by
  rintro (hu | hv)
  · exact Set.disjoint_left.1 hdisj hu (h1 (hc1 hu))
  · exact Set.disjoint_left.1 hdisj (h0 (hc0 hv)) hv

/-- Exercise 7-22 (p. 135): {x | (∃y)[x ∈ W_y & y ∈ Wₓ]} has a productive
complement with λx[x]. -/
theorem mutual_productive :
    ProductiveFn W {x | ∃ y, x ∈ W y ∧ y ∈ W x}ᶜ some := by
  intro x hx
  refine ⟨x, rfl, ?_, ?_⟩
  · rintro ⟨y, hxy, hyx⟩
    exact hx hyx ⟨x, hyx, hxy⟩
  · intro hxx
    exact hx hxx ⟨x, hxx, hxx⟩

/-- Exercise 7-49 (p. 137): for one-one f, the complement of
{f(x) | f(x) ∈ Wₓ} is productive with f. -/
theorem one_one_productive (f : ℕ → ℕ) (hf : Function.Injective f) :
    ProductiveFn W {z | ∃ x, z = f x ∧ f x ∈ W x}ᶜ (fun x => some (f x)) := by
  intro x hx
  refine ⟨f x, rfl, ?_, ?_⟩
  · rintro ⟨x', hx', hmem⟩
    have hxx : x = x' := hf hx'
    subst hxx
    exact hx hmem ⟨x, rfl, hmem⟩
  · intro hmem
    exact hx hmem ⟨x, rfl, hmem⟩

/-- Exercise 7-26 (p. 135, as corrected: A ≤m B × B̄): f = ⟨f₁, f₂⟩ reduces A
to B × B̄; ψ is productive for Ā; W_e(z) = {x | f₂(x) ∈ B or f₁(x) ∈ W_z}
(r. e. uniformly in z since B is r. e.).  Then λz[f₁ψe(z)] is productive
for B̄, so B is creative. -/
theorem creative_product (A B : Set ℕ) (ψ : ℕ → Option ℕ) (f₁ f₂ e : ℕ → ℕ)
    (hψ : ProductiveFn W Aᶜ ψ) (hA : ∀ x, x ∈ A ↔ f₁ x ∈ B ∧ f₂ x ∉ B)
    (he : ∀ z, W (e z) = {x | f₂ x ∈ B ∨ f₁ x ∈ W z}) :
    ProductiveFn W Bᶜ (fun z => (ψ (e z)).map f₁) := by
  intro z hz
  have hsub : W (e z) ⊆ Aᶜ := by
    intro x hx hxA
    rw [he] at hx
    rw [hA] at hxA
    rcases hx with h | h
    · exact hxA.2 h
    · exact hz h hxA.1
  obtain ⟨y, hy, hyA, hyW⟩ := hψ (e z) hsub
  rw [he] at hyW
  simp only [Set.mem_ofPred_eq, not_or] at hyW
  refine ⟨f₁ y, by simp [hy], ?_, hyW.2⟩
  intro hB
  exact hyA ((hA y).2 ⟨hB, hyW.1⟩)

/-! ### Theorem 7-II (b): the join -/

/-- A ⊕ B = {y | [y = 2x & x ∈ A] or [y = 2x + 1 & x ∈ B]} (p. 112). -/
def joinSet (A B : Set ℕ) : Set ℕ :=
  {y | (∃ x, y = 2 * x ∧ x ∈ A) ∨ (∃ x, y = 2 * x + 1 ∧ x ∈ B)}

theorem join_left (A B : Set ℕ) (x : ℕ) : x ∈ A ↔ 2 * x ∈ joinSet A B := by
  constructor
  · intro h
    exact Or.inl ⟨x, rfl, h⟩
  · rintro (⟨x', hx', h⟩ | ⟨x', hx', _⟩)
    · rw [show x = x' by omega]
      exact h
    · omega

theorem join_right (A B : Set ℕ) (x : ℕ) : x ∈ B ↔ 2 * x + 1 ∈ joinSet A B := by
  constructor
  · intro h
    exact Or.inr ⟨x, rfl, h⟩
  · rintro (⟨x', hx', _⟩ | ⟨x', hx', h⟩)
    · omega
    · rw [show x = x' by omega]
      exact h

/-- h(2x) = f(x), h(2x + 1) = g(x) reduces A ⊕ B to C. -/
theorem join_lub (A B C : Set ℕ) (f g : ℕ → ℕ) (hf : ∀ x, x ∈ A ↔ f x ∈ C)
    (hg : ∀ x, x ∈ B ↔ g x ∈ C) :
    (∀ x, (if 2 * x % 2 = 0 then f (2 * x / 2) else g (2 * x / 2)) = f x) ∧
      (∀ x, (if (2 * x + 1) % 2 = 0 then f ((2 * x + 1) / 2) else g ((2 * x + 1) / 2)) = g x) ∧
      ∀ y, y ∈ joinSet A B ↔ (if y % 2 = 0 then f (y / 2) else g (y / 2)) ∈ C := by
  refine ⟨fun x => ?_, fun x => ?_, fun y => ?_⟩
  · rw [ite_eq_left (by omega), show 2 * x / 2 = x by omega]
  · rw [ite_eq_right (by omega), show (2 * x + 1) / 2 = x by omega]
  · rcases Nat.mod_two_eq_zero_or_one y with h | h
    · obtain ⟨x, rfl⟩ : ∃ x, y = 2 * x := ⟨y / 2, by omega⟩
      rw [ite_eq_left h, show 2 * x / 2 = x by omega, ← hf]
      exact (join_left A B x).symm
    · obtain ⟨x, rfl⟩ : ∃ x, y = 2 * x + 1 := ⟨y / 2, by omega⟩
      rw [ite_eq_right (by omega), show (2 * x + 1) / 2 = x by omega, ← hg]
      exact (join_right A B x).symm

/-! ### Exercise 7-4 -/

/-- A is reducible to B via f (the set-theoretic part of ≤m). -/
def ReducesVia (f : ℕ → ℕ) (A B : Set ℕ) : Prop := ∀ x, x ∈ A ↔ f x ∈ B

/-- The printed exercise 7-4 fails: A = N and B = N − {0} are infinite with
(A − B) ∪ (B − A) = {0} finite, but no function reduces B to A. -/
theorem ex7_4_printed_fails :
    (Set.univ : Set ℕ).Infinite ∧ ({x | x ≠ 0} : Set ℕ).Infinite ∧
      ((Set.univ \ {x : ℕ | x ≠ 0}) ∪ ({x | x ≠ 0} \ Set.univ)).Finite ∧
      ¬ ∃ f : ℕ → ℕ, ReducesVia f {x | x ≠ 0} Set.univ := by
  refine ⟨Set.infinite_univ, ?_, ?_, ?_⟩
  · have h : ({x | x ≠ 0} : Set ℕ) = Set.univ \ {0} := by
      ext x
      simp
    rw [h]
    exact Set.infinite_univ.sdiff (Set.finite_singleton 0)
  · apply (Set.finite_singleton (0 : ℕ)).subset
    intro x hx
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_univ, Set.mem_ofPred_eq, true_and,
      not_not, not_true_eq_false, and_false, or_false] at hx
    simp [hx]
  · rintro ⟨f, hf⟩
    have h := (hf 0).2 (Set.mem_univ _)
    simp at h

/-- If B ≠ ∅ and B ≠ N and (A − B) ∪ (B − A) is finite, A is reducible to B
by a function that differs from the identity on a finite set (hence is
general recursive: a finite table). -/
theorem ex7_4_reduction (A B : Set ℕ) (hB : B.Nonempty) (hB' : B ≠ Set.univ)
    (hfin : ((A \ B) ∪ (B \ A)).Finite) :
    ∃ f : ℕ → ℕ, ReducesVia f A B ∧ {x | f x ≠ x}.Finite := by
  classical
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ : ∃ c, c ∉ B := by
    by_contra h
    exact hB' (Set.eq_univ_of_forall fun x => by_contra fun hx => h ⟨x, hx⟩)
  refine ⟨fun x => if x ∈ A \ B then b else if x ∈ B \ A then c else x, ?_, ?_⟩
  · intro x
    by_cases h1 : x ∈ A \ B
    · simp only [ite_eq_left h1]
      exact ⟨fun _ => hb, fun _ => h1.1⟩
    · by_cases h2 : x ∈ B \ A
      · simp only [ite_eq_right h1, ite_eq_left h2]
        exact ⟨fun h => absurd h h2.2, fun h => absurd h hc⟩
      · simp only [ite_eq_right h1, ite_eq_right h2]
        simp only [Set.mem_sdiff, not_and, not_not] at h1 h2
        exact ⟨fun h => h1 h, fun h => h2 h⟩
  · apply hfin.subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    by_contra h
    simp only [Set.mem_union, not_or] at h
    simp only [ite_eq_right h.1, ite_eq_right h.2] at hx
    exact hx rfl

/-- Exercise 7-4 as corrected: A, B infinite, different from N, with finite
(A − B) ∪ (B − A) are reducible to each other by finite modifications of
the identity. -/
theorem ex7_4_corrected (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (hA' : A ≠ Set.univ) (hB' : B ≠ Set.univ) (hfin : ((A \ B) ∪ (B \ A)).Finite) :
    (∃ f : ℕ → ℕ, ReducesVia f A B ∧ {x | f x ≠ x}.Finite) ∧
      (∃ f : ℕ → ℕ, ReducesVia f B A ∧ {x | f x ≠ x}.Finite) :=
  ⟨ex7_4_reduction A B hB.nonempty hB' hfin,
    ex7_4_reduction B A hA.nonempty hA' (by rw [Set.union_comm]; exact hfin)⟩

/-- The exact condition: for infinite A, B with finite (A − B) ∪ (B − A),
A is reducible to B (by some function) iff B = N ⇒ A = N. -/
theorem ex7_4_iff (A B : Set ℕ) (hB : B.Infinite) (hfin : ((A \ B) ∪ (B \ A)).Finite) :
    (∃ f : ℕ → ℕ, ReducesVia f A B) ↔ (B = Set.univ → A = Set.univ) := by
  constructor
  · rintro ⟨f, hf⟩ hBu
    apply Set.eq_univ_of_forall
    intro x
    rw [hf x, hBu]
    trivial
  · intro h
    by_cases hBu : B = Set.univ
    · refine ⟨id, fun x => ?_⟩
      rw [h hBu, hBu]
      rfl
    · obtain ⟨f, hf, _⟩ := ex7_4_reduction A B hB.nonempty hBu hfin
      exact ⟨f, hf⟩

/-! ### Exercises 5-22 and 6-8 -/

/-- Exercise 5-22 (p. 103): no one-one f maps R = {1} ⨯ N onto Q = N ⨯ {1}
componentwise; so R ≢ Q, although τ²(R) ≡ τ²(Q). -/
theorem coding_not_invariant (f : ℕ → ℕ) (hf : Function.Injective f) :
    (fun p : ℕ × ℕ => (f p.1, f p.2)) '' {p | p.1 = 1} ≠ {p | p.2 = 1} := by
  intro h
  have h0 : (f 1, f 0) ∈ {p : ℕ × ℕ | p.2 = 1} := by
    rw [← h]
    exact ⟨(1, 0), rfl, rfl⟩
  have h2 : (f 1, f 2) ∈ {p : ℕ × ℕ | p.2 = 1} := by
    rw [← h]
    exact ⟨(1, 2), rfl, rfl⟩
  simp only [Set.mem_ofPred_eq] at h0 h2
  have := hf (h0.trans h2.symm)
  omega

/-- Exercise 6-8 (p. 109): for a reflexive and transitive ≤ and a reflexive ≡,
≤ is recursively invariant iff A ≡ B ⇒ [A ≤ B & B ≤ A]. -/
theorem reducibility_invariance {α : Type*} (iso red : α → α → Prop)
    (iso_refl : ∀ a, iso a a) (red_refl : ∀ a, red a a)
    (red_trans : ∀ a b c, red a b → red b c → red a c) :
    (∀ a₁ b₁ a₂ b₂, iso a₁ b₁ → iso a₂ b₂ → red a₁ a₂ → red b₁ b₂) ↔
      (∀ a b, iso a b → red a b ∧ red b a) := by
  constructor
  · intro h a b hab
    exact ⟨h a a a b (iso_refl a) hab (red_refl a), h a b a a hab (iso_refl a) (red_refl a)⟩
  · intro h a₁ b₁ a₂ b₂ h1 h2 hr
    exact red_trans _ _ _ (h a₁ b₁ h1).2 (red_trans _ _ _ hr (h a₂ b₂ h2).1)

end RogersRecursive.Ch05_07

#print axioms RogersRecursive.Ch05_07.compl_K_ne
#print axioms RogersRecursive.Ch05_07.uniform_iff_imp
#print axioms RogersRecursive.Ch05_07.K_compl_productive
#print axioms RogersRecursive.Ch05_07.K_compl_completely_productive
#print axioms RogersRecursive.Ch05_07.productive_transfer
#print axioms RogersRecursive.Ch05_07.basic_lemma
#print axioms RogersRecursive.Ch05_07.cylinder_lemma
#print axioms RogersRecursive.Ch05_07.inseparable_step
#print axioms RogersRecursive.Ch05_07.mutual_productive
#print axioms RogersRecursive.Ch05_07.one_one_productive
#print axioms RogersRecursive.Ch05_07.creative_product
#print axioms RogersRecursive.Ch05_07.join_left
#print axioms RogersRecursive.Ch05_07.join_right
#print axioms RogersRecursive.Ch05_07.join_lub
#print axioms RogersRecursive.Ch05_07.ex7_4_printed_fails
#print axioms RogersRecursive.Ch05_07.ex7_4_reduction
#print axioms RogersRecursive.Ch05_07.ex7_4_corrected
#print axioms RogersRecursive.Ch05_07.ex7_4_iff
#print axioms RogersRecursive.Ch05_07.coding_not_invariant
#print axioms RogersRecursive.Ch05_07.reducibility_invariance
