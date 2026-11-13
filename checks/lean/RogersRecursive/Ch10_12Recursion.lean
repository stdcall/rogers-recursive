/-
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная
вычислимость» (Мир, 1972): the recursion theorem of chapter 11 — theorems
I–IV (§ 11.2, pp. 233-236), theorem VII (descending chain, pp. 240-241),
theorem X (a) (Smullyan, p. 246) and theorem XIII (p. 253).

Notation.  A partial function of one variable is `Nat → Option Nat`
(`none`: diverges); `φ x` is φ_x, `φ₂ x u y` is φ_x^(2)(u, y).  The book
obtains the functions g~, v, v~, t, ... from Church's thesis and the s-m-n
theorem; here each such function is an explicit hypothesis stating
exactly the property the book uses:
* `hgt` (theorem I): φ_(g~(u))(x) = φ_(φ_u(u))(x) if φ_u(u) converges,
  divergent otherwise (p. 233);
* `hv`: v is a Gödel number of f g~ (f total);
* `hvt` (theorem II): φ_(v~(z)) = φ_z g~;
* `hgt₂` (theorem III): φ_(g~(u, x))(y) = φ_(φ_u^(2)(u, x))(y);
* theorem IV: the padding function t of theorem 7-IV (φ_(t(a, b)) = φ_a,
  also for two variables, and t one-one), a one-one pairing ⟨u, x⟩, and
  v~~ with φ_(v~~(z))^(2)(u, x) = φ_z^(2)(g~~(u, x), x).

What is proved.  Theorems I, II, III and the fixed-point property of
theorem IV (one parameter x) as stated; for theorem IV the function
n = λzxy[g~~(t(v~~(z), y), x)] of the proof is one-one if and only if
v~~ is one-one (so the printed proof needs a one-one v~~), and
z ↦ t(v~~(z), z) is a one-one choice of v~~ with the same functions.
Theorem X (a) from theorems I and III (with the closure step of the
proof as a hypothesis).  Theorem VII: with f' as in the proof, the fixed
point n of h gives g = φ_n total, g(y) > y and W_(g(y)) = {g(g(y))}, so
m_0 < m_1 < ... is a descending chain of distinct numbers.  Theorem XIII
from the property of theorem II.

Not covered: Church's thesis and the s-m-n theorem (the hypotheses stand
for them); Turing machines and the numbering.  Mathlib.Computability is
not used (not built in the pinned local mathlib checkout).
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

namespace RogersRecursive.Ch10_12.Recursion

/-- A partial function of one variable; `none` means divergence. -/
abbrev PFn := Nat → Option Nat

/-- Theorem I: n = g~(v) is a fixed point of f. -/
theorem fixed_point (φ : Nat → PFn) (gt : Nat → Nat)
    (hgt : ∀ u x, φ (gt u) x = (φ u u).bind (fun w => φ w x))
    (f : Nat → Nat) (v : Nat) (hv : ∀ u, φ v u = some (f (gt u))) :
    φ (gt v) = φ (f (gt v)) := by
  funext x
  rw [hgt, hv]
  rfl

/-- Theorem II: n(z) = g~ v~(z) is a fixed point of φ_z whenever φ_z is
total. -/
theorem fixed_point_uniform (φ : Nat → PFn) (gt vt : Nat → Nat)
    (hgt : ∀ u x, φ (gt u) x = (φ u u).bind (fun w => φ w x))
    (hvt : ∀ z u, φ (vt z) u = φ z (gt u))
    (z : Nat) (f : Nat → Nat) (hz : ∀ u, φ z u = some (f u)) :
    φ (gt (vt z)) = φ (f (gt (vt z))) := by
  funext x
  rw [hgt, hvt, hz]
  rfl

/-- Theorem III (one parameter): n_f(x) = g~(v, x). -/
theorem fixed_point_parameters (φ : Nat → PFn) (φ₂ : Nat → Nat → Nat → Option Nat)
    (gt₂ : Nat → Nat → Nat)
    (hgt₂ : ∀ u x y, φ (gt₂ u x) y = (φ₂ u u x).bind (fun w => φ w y))
    (f : Nat → Nat → Nat) (v : Nat) (hv : ∀ u x, φ₂ v u x = some (f (gt₂ u x) x))
    (x : Nat) : φ (gt₂ v x) = φ (f (gt₂ v x) x) := by
  funext y
  rw [hgt₂, hv]
  rfl

section Kleene

variable (φ : Nat → PFn) (φ₂ : Nat → Nat → Nat → Option Nat)
  (gt₂ : Nat → Nat → Nat) (t pr : Nat → Nat → Nat) (vv : Nat → Nat)

/-- g~~(u, x) = t(g~(u, x), ⟨u, x⟩). -/
def ggt (u x : Nat) : Nat := t (gt₂ u x) (pr u x)

/-- n(z, x, y) = g~~(t(v~~(z), y), x). -/
def kleeneN (z x y : Nat) : Nat := ggt gt₂ t pr (t (vv z) y) x

/-- Theorem IV, the fixed-point property: if φ_z^(2) is total, then
φ_(n(z, x, y)) = φ_(φ_z^(2)(n(z, x, y), x)). -/
theorem kleene_fixed
    (hgt₂ : ∀ u x y, φ (gt₂ u x) y = (φ₂ u u x).bind (fun w => φ w y))
    (ht : ∀ a b, φ (t a b) = φ a) (ht₂ : ∀ a b, φ₂ (t a b) = φ₂ a)
    (hvv : ∀ z u x, φ₂ (vv z) u x = φ₂ z (ggt gt₂ t pr u x) x)
    (z : Nat) (F : Nat → Nat → Nat) (hz : ∀ a x, φ₂ z a x = some (F a x)) (x y : Nat) :
    φ (kleeneN gt₂ t pr vv z x y) = φ (F (kleeneN gt₂ t pr vv z x y) x) := by
  funext w
  simp only [kleeneN, ggt]
  rw [ht, hgt₂, ht₂, hvv, hz]
  rfl

/-- Theorem IV: with t and the pairing one-one, n is one-one exactly when
v~~ is one-one. -/
theorem kleene_injective_iff
    (ht : ∀ a b a' b', t a b = t a' b' → a = a' ∧ b = b')
    (hpr : ∀ a b a' b', pr a b = pr a' b' → a = a' ∧ b = b') :
    (∀ z x y z' x' y', kleeneN gt₂ t pr vv z x y = kleeneN gt₂ t pr vv z' x' y' →
        z = z' ∧ x = x' ∧ y = y') ↔ Function.Injective vv := by
  constructor
  · intro h z z' hzz
    have e : kleeneN gt₂ t pr vv z 0 0 = kleeneN gt₂ t pr vv z' 0 0 := by
      simp only [kleeneN, hzz]
    exact (h z 0 0 z' 0 0 e).1
  · intro hinj z x y z' x' y' e
    simp only [kleeneN, ggt] at e
    obtain ⟨_, e₂⟩ := ht _ _ _ _ e
    obtain ⟨e₃, e₄⟩ := hpr _ _ _ _ e₂
    obtain ⟨e₅, e₆⟩ := ht _ _ _ _ e₃
    exact ⟨hinj e₅, e₄, e₆⟩

/-- A one-one choice of v~~: z ↦ t(v~~(z), z) computes the same functions
and is one-one. -/
theorem padded_choice (ht : ∀ a b a' b', t a b = t a' b' → a = a' ∧ b = b')
    (ht₂ : ∀ a b, φ₂ (t a b) = φ₂ a) :
    Function.Injective (fun z => t (vv z) z) ∧ ∀ z, φ₂ (t (vv z) z) = φ₂ (vv z) :=
  ⟨fun _ _ e => (ht _ _ _ _ e).2, fun _ => ht₂ _ _⟩

end Kleene

/-- Theorem X (a) (Smullyan): from theorem III (for f(x, y) = g(⟨x, y⟩))
and theorem I (for k(y) = h(⟨m^(y), y⟩)) there are m, n with
φ_m = φ_(g(⟨m, n⟩)) and φ_n = φ_(h(⟨m, n⟩)).  `Rec1`, `Rec2` are the
general recursive functions of one and two variables; `hk` is the step
"k is general recursive". -/
theorem double_recursion (φ : Nat → PFn) (Rec1 : Set (Nat → Nat))
    (Rec2 : Set (Nat → Nat → Nat)) (pr : Nat → Nat → Nat) (g h : Nat → Nat)
    (hI : ∀ k ∈ Rec1, ∃ n, φ n = φ (k n))
    (hIII : ∀ f ∈ Rec2, ∃ nf ∈ Rec1, ∀ y, φ (nf y) = φ (f (nf y) y))
    (hg : (fun x y => g (pr x y)) ∈ Rec2)
    (hk : ∀ m ∈ Rec1, (fun y => h (pr (m y) y)) ∈ Rec1) :
    ∃ m n, φ m = φ (g (pr m n)) ∧ φ n = φ (h (pr m n)) := by
  obtain ⟨mh, hmh, hm⟩ := hIII _ hg
  obtain ⟨n, hn⟩ := hI _ (hk mh hmh)
  exact ⟨mh n, n, hm n, hn⟩

/-- Theorem VII: W_e = {w | (e, w) ∈ W}; f'(x, y) > y and
W_(f'(x, y)) = {φ_x φ_x(y)} (empty if divergent); φ_(h(x))(y) = f'(x, y);
n a fixed point of h.  Then g = λy[f'(n, y)] = φ_n, g(y) > y and
W_(g(y)) = {g(g(y))}. -/
theorem descending_chain (φ : Nat → PFn) (W : Nat → Nat → Prop) (f' : Nat → Nat → Nat)
    (h : Nat → Nat)
    (hf' : ∀ x y w, W (f' x y) w ↔ (φ x y).bind (φ x) = some w)
    (hgt : ∀ x y, y < f' x y)
    (hh : ∀ x y, φ (h x) y = some (f' x y))
    (n : Nat) (hn : φ n = φ (h n)) :
    (∀ y, φ n y = some (f' n y)) ∧ (∀ y, y < f' n y) ∧
      ∀ y w, W (f' n y) w ↔ w = f' n (f' n y) := by
  have hφ : ∀ y, φ n y = some (f' n y) := fun y => by rw [hn, hh]
  refine ⟨hφ, fun y => hgt n y, fun y w => ?_⟩
  rw [hf', hφ y]
  show φ n (f' n y) = some w ↔ w = f' n (f' n y)
  rw [hφ (f' n y), Option.some.injEq]
  exact eq_comm

/-- Theorem VII, the chain: m_(i + 1) = g(m_i) is strictly increasing,
so its terms are distinct. -/
theorem chain_distinct (g : Nat → Nat) (hg : ∀ y, y < g y) (m₀ : Nat) :
    StrictMono (fun i => g^[i] m₀) := by
  apply strictMono_nat_of_lt_succ
  intro i
  show g^[i] m₀ < g^[i + 1] m₀
  rw [Function.iterate_succ_apply']
  exact hg _

/-- Theorem XIII: n has the property of theorem II; t₀ is an index of
λy[0]; φ_(h(z))(x) = t₀ if x = n(z), x otherwise; m is a fixed point of
h.  Then f = φ_m is the identity off n(m), f(n(m)) = t₀, and
φ_(n(m)) = λy[0], not the nowhere-defined function. -/
theorem fixed_point_not_minimal (φ : Nat → PFn) (n h : Nat → Nat) (t₀ : Nat)
    (hn : ∀ z (f : Nat → Nat), (∀ u, φ z u = some (f u)) → φ (n z) = φ (f (n z)))
    (ht₀ : φ t₀ = fun _ => some 0)
    (hh : ∀ z x, φ (h z) x = some (if x = n z then t₀ else x))
    (m : Nat) (hm : φ m = φ (h m)) :
    (∀ x, x ≠ n m → φ m x = some x) ∧ φ m (n m) = some t₀ ∧
      φ (n m) = (fun _ => some 0) := by
  have hφ : ∀ x, φ m x = some (if x = n m then t₀ else x) := fun x => by rw [hm, hh]
  refine ⟨fun x hx => by simp [hφ, hx], by simp [hφ], ?_⟩
  have e := hn m (fun x => if x = n m then t₀ else x) hφ
  rw [e]
  simp [ht₀]

end RogersRecursive.Ch10_12.Recursion

#print axioms RogersRecursive.Ch10_12.Recursion.fixed_point
#print axioms RogersRecursive.Ch10_12.Recursion.fixed_point_uniform
#print axioms RogersRecursive.Ch10_12.Recursion.fixed_point_parameters
#print axioms RogersRecursive.Ch10_12.Recursion.kleene_fixed
#print axioms RogersRecursive.Ch10_12.Recursion.kleene_injective_iff
#print axioms RogersRecursive.Ch10_12.Recursion.padded_choice
#print axioms RogersRecursive.Ch10_12.Recursion.double_recursion
#print axioms RogersRecursive.Ch10_12.Recursion.descending_chain
#print axioms RogersRecursive.Ch10_12.Recursion.chain_distinct
#print axioms RogersRecursive.Ch10_12.Recursion.fixed_point_not_minimal
