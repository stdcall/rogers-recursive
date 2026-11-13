import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# Prefix rules of theorems 16-III and 16-VII

Places in the book (§ 16.1, pp. 480-485):

* Theorem 16-III (Kleene, `th:kleene-prefix-rules`, p. 480) and its proof:
  (i) two number quantifiers of the same kind contract into one
  (`rule_i_exists`, `rule_i_forall`, by the pairing function);
  (ii) two function quantifiers of the same kind contract into one, the
  new function `h` coding `f` and `g` as `π₁ h`, `π₂ h`
  (`rule_ii_exists`, `rule_ii_forall`); (iii) a number quantifier
  becomes a function quantifier on `f(0)` (`rule_iii_exists`,
  `rule_iii_forall`); (iv) `∀x ∃f` becomes `∃f ∀x` with
  `λy [f(⟨x, y⟩)]` (`rule_iv`, the axiom of choice as the book says in
  exercise 16-2), and `∃x ∀f` becomes `∀f ∃x` (`rule_iv_dual`).
* Theorem 16-VII (Addison and Kleene, `th:addison-kleene-prefix-rules`,
  p. 484): (i) the step of the proof: a function quantifier over a
  relation of the code `f̄(w)` alone becomes a quantifier over finite
  tuples (`ak_i_exists`, `ak_i_forall`); (ii) `∀f ∃x ∃g` becomes
  `∃g ∀f ∃x` with `λy [g(⟨f̄(x), y⟩)]` when the relation depends on `f`
  only through `f̄(x)` (`ak_ii`), and the dual `∃f ∀x ∀g` → `∀g ∃f ∀x`
  (`ak_ii_dual`).

Notation: `Nat.pair`, `Nat.unpair` stand for the pairing function `τ` of
§ 5.3 and its inverses `π₁`, `π₂` (both are bijections ℕ × ℕ → ℕ; the proofs
use only that `unpair (pair a b) = (a, b)`); `pre f x` is the tuple
`⟨f(0), ..., f(x - 1)⟩` and `c` any one-one coding of tuples (the book's
`τ*`, so `f̄(x) = c (pre f x)`).  The relations are arbitrary: the proofs
show the equivalence of the forms, not that the new relations are
recursive (that is the other half of exercises 16-2, 16-4).

Not covered: the normal form theorems used in the proof of 16-VII (i) (that
a recursive relation of `f` has the form `∃w T*(f̄(w), ...)`); the
uniformity of the transformations.
-/

namespace RogersRecursive.Ch15_16.Prefix

/-! ### Theorem 16-III -/

theorem rule_i_exists (R : ℕ → ℕ → Prop) :
    (∃ x y, R x y) ↔ ∃ z, R (Nat.unpair z).1 (Nat.unpair z).2 := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨Nat.pair x y, by simpa [Nat.unpair_pair] using h⟩
  · rintro ⟨z, h⟩
    exact ⟨_, _, h⟩

theorem rule_i_forall (R : ℕ → ℕ → Prop) :
    (∀ x y, R x y) ↔ ∀ z, R (Nat.unpair z).1 (Nat.unpair z).2 := by
  constructor
  · intro h z
    exact h _ _
  · intro h x y
    simpa [Nat.unpair_pair] using h (Nat.pair x y)

/-- The two functions coded by `h`. -/
def p₁ (h : ℕ → ℕ) : ℕ → ℕ := fun x => (Nat.unpair (h x)).1
def p₂ (h : ℕ → ℕ) : ℕ → ℕ := fun x => (Nat.unpair (h x)).2

theorem p_pair (f g : ℕ → ℕ) :
    p₁ (fun x => Nat.pair (f x) (g x)) = f ∧ p₂ (fun x => Nat.pair (f x) (g x)) = g := by
  constructor <;> funext x <;> simp [p₁, p₂, Nat.unpair_pair]

theorem rule_ii_exists (R : (ℕ → ℕ) → (ℕ → ℕ) → Prop) :
    (∃ f g, R f g) ↔ ∃ h, R (p₁ h) (p₂ h) := by
  constructor
  · rintro ⟨f, g, hfg⟩
    refine ⟨fun x => Nat.pair (f x) (g x), ?_⟩
    rw [(p_pair f g).1, (p_pair f g).2]
    exact hfg
  · rintro ⟨h, hh⟩
    exact ⟨_, _, hh⟩

theorem rule_ii_forall (R : (ℕ → ℕ) → (ℕ → ℕ) → Prop) :
    (∀ f g, R f g) ↔ ∀ h, R (p₁ h) (p₂ h) := by
  constructor
  · intro hfg h
    exact hfg _ _
  · intro hh f g
    have := hh (fun x => Nat.pair (f x) (g x))
    rwa [(p_pair f g).1, (p_pair f g).2] at this

theorem rule_iii_forall (R : ℕ → Prop) : (∀ x, R x) ↔ ∀ f : ℕ → ℕ, R (f 0) :=
  ⟨fun h f => h (f 0), fun h x => h (fun _ => x)⟩

theorem rule_iii_exists (R : ℕ → Prop) : (∃ x, R x) ↔ ∃ f : ℕ → ℕ, R (f 0) :=
  ⟨fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩, fun ⟨f, hf⟩ => ⟨f 0, hf⟩⟩

/-- Rule (iv): `(∀x)(∃f) R(f, x) ↔ (∃f)(∀x) R(λy [f(⟨x, y⟩)], x)`. -/
theorem rule_iv (R : (ℕ → ℕ) → ℕ → Prop) :
    (∀ x, ∃ f, R f x) ↔ ∃ f : ℕ → ℕ, ∀ x, R (fun y => f (Nat.pair x y)) x := by
  constructor
  · intro h
    choose g hg using h
    refine ⟨fun z => g (Nat.unpair z).1 (Nat.unpair z).2, fun x => ?_⟩
    simpa [Nat.unpair_pair] using hg x
  · rintro ⟨f, hf⟩ x
    exact ⟨_, hf x⟩

/-- The dual of rule (iv): `(∃x)(∀f) ↔ (∀f)(∃x)`. -/
theorem rule_iv_dual (R : (ℕ → ℕ) → ℕ → Prop) :
    (∃ x, ∀ f, R f x) ↔ ∀ f : ℕ → ℕ, ∃ x, R (fun y => f (Nat.pair x y)) x := by
  have h := rule_iv (fun f x => ¬ R f x)
  constructor
  · intro hx f
    by_contra hne
    simp only [not_exists] at hne
    obtain ⟨x, hx⟩ := hx
    exact (h.2 ⟨f, hne⟩ x).elim fun g hg => hg (hx g)
  · intro hf
    by_contra hne
    simp only [not_forall, not_exists] at hne
    obtain ⟨f, hf'⟩ := h.1 hne
    obtain ⟨x, hx⟩ := hf f
    exact hf' x hx

/-! ### Theorem 16-VII -/

/-- `⟨f(0), ..., f(x - 1)⟩`. -/
def pre (f : ℕ → ℕ) (x : ℕ) : List ℕ := List.ofFn fun i : Fin x => f i

theorem pre_length (f : ℕ → ℕ) (x : ℕ) : (pre f x).length = x := by
  simp [pre]

/-- Every tuple is an initial segment of some function. -/
theorem pre_ext (l : List ℕ) : pre (fun i => l.getD i 0) l.length = l := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h₁ h₂
    simp [pre, List.getD_eq_getElem?_getD]

/-- 16-VII (i), the step of the proof:
`(∃f)(∃w) T(f̄(w)) ↔ (∃y)(∃w)[y codes a tuple of length w & T(y)]`. -/
theorem ak_i_exists (T : List ℕ → Prop) : (∃ f w, T (pre f w)) ↔ ∃ l, T l := by
  constructor
  · rintro ⟨f, w, h⟩
    exact ⟨_, h⟩
  · rintro ⟨l, h⟩
    exact ⟨_, l.length, by rwa [pre_ext]⟩

theorem ak_i_forall (T : List ℕ → Prop) : (∀ f w, T (pre f w)) ↔ ∀ l, T l := by
  constructor
  · intro h l
    have := h (fun i => l.getD i 0) l.length
    rwa [pre_ext] at this
  · intro h f w
    exact h _

/-- 16-VII (ii): `(∀f)(∃x)(∃g) R(f̄(x), x, g) ↔
(∃g)(∀f)(∃x) R(f̄(x), x, λy [g(⟨f̄(x), y⟩)])`, `f̄(x) = c (pre f x)` with a
one-one coding `c`. -/
theorem ak_ii (c : List ℕ → ℕ) (hc : Function.Injective c) (R : ℕ → ℕ → (ℕ → ℕ) → Prop) :
    (∀ f : ℕ → ℕ, ∃ x g, R (c (pre f x)) x g) ↔
      ∃ g : ℕ → ℕ, ∀ f, ∃ x, R (c (pre f x)) x (fun y => g (Nat.pair (c (pre f x)) y)) := by
  classical
  constructor
  · intro h
    -- for every code u, a function good for the tuple coded by u
    let Q : ℕ → (ℕ → ℕ) → Prop := fun u g => ∃ l, c l = u ∧ R u l.length g
    let G : ℕ → ℕ → ℕ := fun u => if hu : ∃ g, Q u g then Classical.choose hu else fun _ => 0
    refine ⟨fun z => G (Nat.unpair z).1 (Nat.unpair z).2, fun f => ?_⟩
    obtain ⟨x, g, hg⟩ := h f
    have hQ : ∃ g, Q (c (pre f x)) g := ⟨g, pre f x, rfl, by rw [pre_length]; exact hg⟩
    refine ⟨x, ?_⟩
    have hG : Q (c (pre f x)) (G (c (pre f x))) := by
      simp only [G]; rw [dite_eq_left hQ]
      exact Classical.choose_spec hQ
    obtain ⟨l, hl, hR⟩ := hG
    have : l = pre f x := hc hl
    subst this
    rw [pre_length] at hR
    simpa [Nat.unpair_pair] using hR
  · rintro ⟨g, hg⟩ f
    obtain ⟨x, hx⟩ := hg f
    exact ⟨x, _, hx⟩

/-- The dual of 16-VII (ii): `(∃f)(∀x)(∀g) ↔ (∀g)(∃f)(∀x)`. -/
theorem ak_ii_dual (c : List ℕ → ℕ) (hc : Function.Injective c) (R : ℕ → ℕ → (ℕ → ℕ) → Prop) :
    (∃ f : ℕ → ℕ, ∀ x g, R (c (pre f x)) x g) ↔
      ∀ g : ℕ → ℕ, ∃ f, ∀ x, R (c (pre f x)) x (fun y => g (Nat.pair (c (pre f x)) y)) := by
  have h := ak_ii c hc (fun u x g => ¬ R u x g)
  constructor
  · rintro ⟨f, hf⟩ g
    by_contra hne
    simp only [not_forall, not_exists] at hne
    obtain ⟨x, g', hg'⟩ := h.2 ⟨g, hne⟩ f
    exact hg' (hf x g')
  · intro hg
    by_contra hne
    simp only [not_forall, not_exists] at hne
    obtain ⟨g, hg'⟩ := h.1 hne
    obtain ⟨f, hf⟩ := hg g
    obtain ⟨x, hx⟩ := hg' f
    exact hx (hf x)

end RogersRecursive.Ch15_16.Prefix

#print axioms RogersRecursive.Ch15_16.Prefix.rule_i_exists
#print axioms RogersRecursive.Ch15_16.Prefix.rule_i_forall
#print axioms RogersRecursive.Ch15_16.Prefix.rule_ii_exists
#print axioms RogersRecursive.Ch15_16.Prefix.rule_ii_forall
#print axioms RogersRecursive.Ch15_16.Prefix.rule_iii_exists
#print axioms RogersRecursive.Ch15_16.Prefix.rule_iii_forall
#print axioms RogersRecursive.Ch15_16.Prefix.rule_iv
#print axioms RogersRecursive.Ch15_16.Prefix.rule_iv_dual
#print axioms RogersRecursive.Ch15_16.Prefix.ak_i_exists
#print axioms RogersRecursive.Ch15_16.Prefix.ak_i_forall
#print axioms RogersRecursive.Ch15_16.Prefix.ak_ii
#print axioms RogersRecursive.Ch15_16.Prefix.ak_ii_dual
