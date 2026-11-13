/-
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная
вычислимость» (Мир, 1972): the diagonal arguments of chapters 1-2.
§ 1.4 (p. 27) and § 1.5 (p. 29), the diagonal function over total and
over partial functions; § 1.9, theorem VII (both proofs, pp. 43-44),
corollary VII and theorem VIII (pp. 44-46); § 2.1, Rice's theorem
(p. 56; exercise 2-39); § 2.3, theorem II, the remark after it, and
theorem III (pp. 58-60).

Notation.  A partial function of one variable is `Nat → Option Nat`
(`none`: diverges); `φ x` is φ_x of the fixed numbering of § 1.8, `φ x y`
its value at y.  The book's proofs use Church's thesis (the functions
they describe are partial recursive) and the s-m-n theorem; here every
such use is an explicit hypothesis, and the classes are arbitrary sets:
`PR` the partial recursive functions of one variable, `Rec1`, `Rec2` the
general recursive functions of one and two variables.  So each theorem
proves the diagonal (or reduction) step of the book from exactly the
facts the book takes from Church's thesis, which are listed in the
hypotheses:
* `hind`: every partial recursive function has an index (§ 1.8);
* `hct` (theorem VII, corollary VII): from a recursive g the function
  ψ(x) = 1 if g(x, x) = 0, divergent if g(x, x) /= 0, is partial recursive;
* theorem VIII: theorem I (infinitely many indices of total functions)
  and that h = λx[φ_(g(x))(x) + 1] has an index, g the μ-enumeration
  g(0) = μy[f(y) = 1], g(x + 1) = μy[y > g(x) & f(y) = 1] (`enum`, built
  and proved to list exactly the y with f(y) = 1 here);
* the more formal proof of theorem VII: the s-m-n function h with
  φ_(h(z)) = λx[ψ(z, x)];
* Rice: the s-m-n step, "φ_(h(x)) = θ if φ_x(x) converges, divergent
  otherwise", with h recursive, and closure of `Rec1` under composition and
  under 1 - (·), and the constants.
μ (introduction, p. 14) is "the least y such that ...": `IsMu`.

What is proved: the conclusions as stated in the book (with "recursive"
read as membership in these classes): no g decides the halting relation;
for every index z of a two-place function, the input ⟨h(z), h(z)⟩ is a
place where φ_z^(2) is undefined or wrong; corollary VII; theorem VIII;
Rice's theorem (both directions); theorem 2-II and the remark that
ψ(x₁) diverges at an index x₁ of ψ (also the § 1.5 remark on ψ_(x₀));
theorem 2-III.

Not covered: Church's thesis and the s-m-n theorem themselves; Turing
machines and the numbering are not formalized (the hypotheses stand for
them).  Mathlib's `Mathlib.Computability` (Nat.Partrec.Code, the halting
problem, `ComputablePred.rice`) is not used: those modules are not built
in the pinned local mathlib checkout.
-/
import Mathlib.Data.Nat.Find

namespace RogersRecursive.Ch01_04.Diagonal

/-- A partial function of one variable; `none` means divergence. -/
abbrev PFn := Nat → Option Nat

/-! § 1.4, p. 27: h(x) = g_x(x) + 1 is no g_x. -/

theorem total_diagonal (g : Nat → Nat → Nat) (x₀ : Nat) :
    g x₀ ≠ fun x => g x x + 1 := by
  intro h
  have := congrFun h x₀
  omega

/-! § 1.5, p. 29, and the remark after theorem 2-II: at its own index the
partial diagonal function φ_x(x) + 1 diverges. -/

theorem diagonal_diverges (φ : Nat → PFn) (x₀ : Nat)
    (h : φ x₀ = fun x => (φ x x).map (· + 1)) : φ x₀ x₀ = none := by
  have e := congrFun h x₀
  cases hv : φ x₀ x₀ with
  | none => rfl
  | some v =>
    rw [hv] at e
    simp at e

/-! Theorem VII, the informal proof. -/

theorem halting (φ : Nat → PFn) (PR : Set PFn) (Rec2 : Set (Nat → Nat → Nat))
    (hind : ∀ ψ ∈ PR, ∃ y, φ y = ψ)
    (hct : ∀ g ∈ Rec2, (fun x => if g x x = 0 then some 1 else none) ∈ PR) :
    ¬ ∃ g ∈ Rec2, ∀ x y, (g x y = 1 ↔ φ x y ≠ none) ∧ (g x y = 0 ↔ φ x y = none) := by
  rintro ⟨g, hg, hspec⟩
  obtain ⟨y₀, hy₀⟩ := hind _ (hct g hg)
  have e := congrFun hy₀ y₀
  by_cases h0 : g y₀ y₀ = 0
  · simp only [h0, ite_true] at e
    have := (hspec y₀ y₀).1.2 (by rw [e]; simp)
    omega
  · simp only [h0, ite_false] at e
    exact h0 ((hspec y₀ y₀).2.2 e)

/-- Theorem VII, the more formal proof: h(z) is an index of
λx[ψ(z, x)], ψ(z, x) = 1 if φ_z^(2)(x, x) = 0 and divergent otherwise; then
at ⟨h(z), h(z)⟩ the function φ_z^(2) is undefined or gives wrong
information. -/
theorem halting_counterexample (φ : Nat → PFn) (φ₂ : Nat → Nat → Nat → Option Nat)
    (h : Nat → Nat) (hh : ∀ z x, φ (h z) x = if φ₂ z x x = some 0 then some 1 else none)
    (z : Nat) :
    ¬ ((φ₂ z (h z) (h z) = some 1 ↔ φ (h z) (h z) ≠ none) ∧
       (φ₂ z (h z) (h z) = some 0 ↔ φ (h z) (h z) = none)) := by
  rintro ⟨h1, h0⟩
  have e := hh z (h z)
  by_cases c : φ₂ z (h z) (h z) = some 0
  · simp only [c, ite_true] at e
    have := h1.2 (by rw [e]; simp)
    rw [c] at this
    simp at this
  · simp only [c, ite_false] at e
    exact c (h0.2 e)

/-- Corollary VII: the diagonal set {x | φ_x(x) converges}. -/
theorem self_halting (φ : Nat → PFn) (PR : Set PFn) (Rec1 : Set (Nat → Nat))
    (hind : ∀ ψ ∈ PR, ∃ y, φ y = ψ)
    (hct : ∀ f ∈ Rec1, (fun x => if f x = 0 then some 1 else none) ∈ PR) :
    ¬ ∃ f ∈ Rec1, ∀ x, (f x = 1 ↔ φ x x ≠ none) ∧ (f x = 0 ↔ φ x x = none) := by
  rintro ⟨f, hf, hspec⟩
  obtain ⟨y₀, hy₀⟩ := hind _ (hct f hf)
  have e := congrFun hy₀ y₀
  by_cases h0 : f y₀ = 0
  · simp only [h0, ite_true] at e
    have := (hspec y₀).1.2 (by rw [e]; simp)
    omega
  · simp only [h0, ite_false] at e
    exact h0 ((hspec y₀).2.2 e)

/-! Theorem VIII. -/

section Enum

open Classical

theorem exists_p (p : Nat → Prop) (hinf : ∀ n, ∃ y, n < y ∧ p y) : ∃ y, p y :=
  let ⟨y, _, hy⟩ := hinf 0
  ⟨y, hy⟩

variable (p : Nat → Prop) (hinf : ∀ n, ∃ y, n < y ∧ p y)

/-- g(0) = μy[p(y)], g(x + 1) = μy[y > g(x) & p(y)] (p. 46, p(y): f(y) = 1). -/
noncomputable def enum : Nat → Nat
  | 0 => Nat.find (exists_p p hinf)
  | x + 1 => Nat.find (hinf (enum x))

theorem enum_zero : enum p hinf 0 = Nat.find (exists_p p hinf) := by
  rw [enum]

theorem enum_succ (n : Nat) : enum p hinf (n + 1) = Nat.find (hinf (enum p hinf n)) := by
  rw [enum]

theorem enum_mem (n : Nat) : p (enum p hinf n) := by
  cases n with
  | zero => rw [enum_zero]; exact Nat.find_spec (exists_p p hinf)
  | succ n => rw [enum_succ]; exact (Nat.find_spec (hinf (enum p hinf n))).2

theorem enum_lt (n : Nat) : enum p hinf n < enum p hinf (n + 1) := by
  rw [enum_succ]
  exact (Nat.find_spec (hinf (enum p hinf n))).1

theorem le_enum (n : Nat) : n ≤ enum p hinf n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => have := enum_lt p hinf n; omega

/-- Every y with p(y) is a value of g: g lists exactly these y. -/
theorem enum_onto (t : Nat) (ht : p t) : ∃ n, enum p hinf n = t := by
  have hex : ∃ n, t ≤ enum p hinf n := ⟨t, le_enum p hinf t⟩
  refine ⟨Nat.find hex, ?_⟩
  have hle := Nat.find_spec hex
  cases hn : Nat.find hex with
  | zero =>
    rw [hn] at hle
    have : enum p hinf 0 ≤ t := by
      rw [enum_zero]
      exact Nat.find_min' (exists_p p hinf) ht
    omega
  | succ m =>
    rw [hn] at hle
    have hm : ¬ t ≤ enum p hinf m := Nat.find_min hex (by omega)
    have : enum p hinf (m + 1) ≤ t := by
      rw [enum_succ]
      exact Nat.find_min' (hinf (enum p hinf m)) ⟨by omega, ht⟩
    omega

end Enum

/-- The diagonal step of theorem VIII: e lists the indices of total
functions, and h = λx[φ_(e(x))(x) + 1] cannot have an index. -/
theorem totality_diagonal (φ : Nat → PFn) (e : Nat → Nat)
    (he_mem : ∀ n x, φ (e n) x ≠ none)
    (he_onto : ∀ y, (∀ x, φ y x ≠ none) → ∃ n, e n = y)
    (z₀ : Nat) (hz₀ : φ z₀ = fun x => (φ (e x) x).map (· + 1)) : False := by
  have total : ∀ x, φ z₀ x ≠ none := by
    intro x
    rw [hz₀]
    simpa using he_mem x x
  obtain ⟨y₀, hy₀⟩ := he_onto z₀ total
  have e₀ := congrFun hz₀ y₀
  simp only [hy₀] at e₀
  cases hv : φ z₀ y₀ with
  | none => exact total y₀ hv
  | some v => rw [hv] at e₀; simp at e₀

/-- Theorem VIII: no recursive f with f(y) = 1 iff φ_y is total. -/
theorem totality_undecidable (φ : Nat → PFn) (Rec1 : Set (Nat → Nat))
    (hinf : ∀ n, ∃ y, n < y ∧ ∀ x, φ y x ≠ none)
    (hct : ∀ f ∈ Rec1, ∀ hT : ∀ n, ∃ y, n < y ∧ f y = 1,
      ∃ z₀, φ z₀ = fun x => (φ (enum (fun y => f y = 1) hT x) x).map (· + 1)) :
    ¬ ∃ f ∈ Rec1, ∀ y, (f y = 1 ↔ ∀ x, φ y x ≠ none) ∧
      (f y = 0 ↔ ¬ ∀ x, φ y x ≠ none) := by
  rintro ⟨f, hf, hspec⟩
  have hT : ∀ n, ∃ y, n < y ∧ f y = 1 := by
    intro n
    obtain ⟨y, hy, ht⟩ := hinf n
    exact ⟨y, hy, (hspec y).1.2 ht⟩
  obtain ⟨z₀, hz₀⟩ := hct f hf hT
  refine totality_diagonal φ (enum (fun y => f y = 1) hT) ?_ ?_ z₀ hz₀
  · intro n
    exact (hspec _).1.1 (enum_mem (fun y => f y = 1) hT n)
  · intro y hy
    exact enum_onto (fun y => f y = 1) hT y ((hspec y).1.2 hy)

/-! Rice's theorem (p. 56, exercise 2-39). -/

theorem rice (φ : Nat → PFn) (PR : Set PFn) (Rec1 : Set (Nat → Nat))
    (hφ : ∀ x, φ x ∈ PR)
    (hind : ∀ ψ ∈ PR, ∃ y, φ y = ψ)
    (hct : ∀ f ∈ Rec1, (fun x => if f x = 0 then some 1 else none) ∈ PR)
    (hsmn : ∀ θ ∈ PR, ∃ h ∈ Rec1, ∀ x,
      φ (h x) = if φ x x ≠ none then θ else fun _ => none)
    (hcomp : ∀ c ∈ Rec1, ∀ h ∈ Rec1, (fun x => c (h x)) ∈ Rec1)
    (hneg : ∀ c ∈ Rec1, (fun x => 1 - c x) ∈ Rec1)
    (hconst : (fun _ => 0) ∈ Rec1 ∧ (fun _ => 1) ∈ Rec1)
    (C : Set PFn) (hC : C ⊆ PR) :
    (∃ c ∈ Rec1, ∀ x, (c x = 1 ↔ φ x ∈ C) ∧ (c x = 0 ↔ φ x ∉ C)) ↔
      (C = ∅ ∨ C = PR) := by
  constructor
  · rintro ⟨c, hc, hspec⟩
    by_contra hne
    have h₁ : ∃ θ₁, θ₁ ∈ C := by
      by_contra hn
      refine hne (Or.inl (Set.ext fun θ => ⟨fun hθ => hn ⟨θ, hθ⟩, fun hθ => hθ.elim⟩))
    have h₂ : ∃ θ₂, θ₂ ∈ PR ∧ θ₂ ∉ C := by
      by_contra hn
      refine hne (Or.inr (Set.ext fun θ => ⟨fun hθ => hC hθ, fun hθ => ?_⟩))
      by_contra hθC
      exact hn ⟨θ, hθ, hθC⟩
    obtain ⟨θ₁, hθ₁⟩ := h₁
    obtain ⟨θ₂, hθ₂, hθ₂C⟩ := h₂
    apply self_halting φ PR Rec1 hind hct
    by_cases hb : (fun _ => none : PFn) ∈ C
    · obtain ⟨h, hh, hspec_h⟩ := hsmn θ₂ hθ₂
      refine ⟨fun x => 1 - c (h x), hneg _ (hcomp c hc h hh), fun x => ?_⟩
      by_cases k : φ x x ≠ none
      · have : φ (h x) ∉ C := by rw [hspec_h x]; simpa [k] using hθ₂C
        have c0 := (hspec (h x)).2.2 this
        simp only [c0]
        exact ⟨by simp [k], by simp [k]⟩
      · have : φ (h x) ∈ C := by rw [hspec_h x]; simpa [k] using hb
        have c1 := (hspec (h x)).1.2 this
        simp only [c1]
        replace k : φ x x = none := not_not.mp k
        exact ⟨by simp [k], by simp [k]⟩
    · obtain ⟨h, hh, hspec_h⟩ := hsmn θ₁ (hC hθ₁)
      refine ⟨fun x => c (h x), hcomp c hc h hh, fun x => ?_⟩
      by_cases k : φ x x ≠ none
      · have : φ (h x) ∈ C := by rw [hspec_h x]; simpa [k] using hθ₁
        have c1 := (hspec (h x)).1.2 this
        simp only [c1]
        exact ⟨by simp [k], by simp [k]⟩
      · have : φ (h x) ∉ C := by rw [hspec_h x]; simpa [k] using hb
        have c0 := (hspec (h x)).2.2 this
        simp only [c0]
        replace k : φ x x = none := not_not.mp k
        exact ⟨by simp [k], by simp [k]⟩
  · rintro (h | h)
    · refine ⟨fun _ => 0, hconst.1, fun x => ?_⟩
      subst h
      exact ⟨⟨fun h0 => absurd h0 (by simp), fun hm => absurd hm (fun hm' => hm')⟩,
        ⟨fun _ hm => hm, fun _ => rfl⟩⟩
    · refine ⟨fun _ => 1, hconst.2, fun x => ?_⟩
      subst h
      exact ⟨⟨fun _ => hφ x, fun _ => rfl⟩,
        ⟨fun h0 => absurd h0 (by simp), fun hn => absurd (hφ x) hn⟩⟩

/-! § 2.3, theorem II and the remark after it. -/

/-- ψ(x) = φ_x(x) + 1 has no recursive extension: at an index y of a
recursive f, ψ(y) = f(y) + 1. -/
theorem no_recursive_extension (φ : Nat → PFn) (Rec1 : Set (Nat → Nat))
    (hidx : ∀ f ∈ Rec1, ∃ y, φ y = fun x => some (f x)) (f : Nat → Nat) (hf : f ∈ Rec1) :
    ∃ x, (φ x x).map (· + 1) = some (f x + 1) := by
  obtain ⟨y, hy⟩ := hidx f hf
  exact ⟨y, by rw [hy]; rfl⟩

/-! § 2.3, theorem III. -/

/-- ψ = λx[μy[f(x, y) = 1]] in the sense of the introduction. -/
def IsMu (f : Nat → Nat → Nat) (ψ : PFn) : Prop :=
  ∀ x v, ψ x = some v ↔ (f x v = 1 ∧ ∀ y < v, f x y ≠ 1)

/-- The key step: with ψ(x) = x if φ_x(x) converges (divergent otherwise),
ψ = μf gives "φ_x(x) converges iff f(x, x) = 1". -/
theorem mu_decides (φ : Nat → PFn) (f : Nat → Nat → Nat)
    (hψ : IsMu f (fun x => if φ x x ≠ none then some x else none)) (x : Nat) :
    φ x x ≠ none ↔ f x x = 1 := by
  constructor
  · intro k
    exact ((hψ x x).1 (by simp [k])).1
  · intro hf k
    classical
    have hex : ∃ v, f x v = 1 := ⟨x, hf⟩
    have := (hψ x (Nat.find hex)).2
      ⟨Nat.find_spec hex, fun y hy => Nat.find_min hex hy⟩
    simp [k] at this

theorem not_mu_of_total (φ : Nat → PFn) (PR : Set PFn) (Rec1 : Set (Nat → Nat))
    (Rec2 : Set (Nat → Nat → Nat))
    (hind : ∀ ψ ∈ PR, ∃ y, φ y = ψ)
    (hct : ∀ f ∈ Rec1, (fun x => if f x = 0 then some 1 else none) ∈ PR)
    (hdiag : ∀ f ∈ Rec2, (fun x => if f x x = 1 then 1 else 0) ∈ Rec1) :
    ¬ ∃ f ∈ Rec2, IsMu f (fun x => if φ x x ≠ none then some x else none) := by
  rintro ⟨f, hf, hψ⟩
  apply self_halting φ PR Rec1 hind hct
  refine ⟨_, hdiag f hf, fun x => ?_⟩
  have key := mu_decides φ f hψ x
  by_cases h1 : f x x = 1
  · simp [h1, key.2 h1]
  · have : φ x x = none := by
      by_contra hn
      exact h1 (key.1 hn)
    simp [h1, this]

end RogersRecursive.Ch01_04.Diagonal

#print axioms RogersRecursive.Ch01_04.Diagonal.total_diagonal
#print axioms RogersRecursive.Ch01_04.Diagonal.diagonal_diverges
#print axioms RogersRecursive.Ch01_04.Diagonal.halting
#print axioms RogersRecursive.Ch01_04.Diagonal.halting_counterexample
#print axioms RogersRecursive.Ch01_04.Diagonal.self_halting
#print axioms RogersRecursive.Ch01_04.Diagonal.enum_mem
#print axioms RogersRecursive.Ch01_04.Diagonal.enum_lt
#print axioms RogersRecursive.Ch01_04.Diagonal.le_enum
#print axioms RogersRecursive.Ch01_04.Diagonal.enum_onto
#print axioms RogersRecursive.Ch01_04.Diagonal.totality_diagonal
#print axioms RogersRecursive.Ch01_04.Diagonal.totality_undecidable
#print axioms RogersRecursive.Ch01_04.Diagonal.rice
#print axioms RogersRecursive.Ch01_04.Diagonal.no_recursive_extension
#print axioms RogersRecursive.Ch01_04.Diagonal.mu_decides
#print axioms RogersRecursive.Ch01_04.Diagonal.not_mu_of_total
