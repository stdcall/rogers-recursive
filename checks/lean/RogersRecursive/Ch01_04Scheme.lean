/-
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная
вычислимость» (Мир, 1972), § 1.2, pp. 22-23: the derivation of λx[2x];
§ 1.3, p. 26, the step functions g; exercise 2-1 (p. 62) and its hint.

Notation.  Clause (v) of the definition is `rec2 g h` (k = 2: f(0, x) =
g(x), f(y + 1, x) = h(y, f(y, x), x)) and `rec1 m h` (k = 1, g "a function
of zero variables", the number m).  The derivation of p. 23 is written
line by line: f₁ = λx[x] by (iii), f₂ = λx[x + 1] by (ii),
f₃ = λx₁x₂x₃[x₂] by (iii), f₄ = f₂f₃ by (iv), f₅ by (v) from f₁, f₄, and
f₆ = f₅(f₁, f₁), the substitution of f₁, f₁ into f₅, i.e. clause (iv).
The hint of exercise 2-1: ĥ = λx[max(0, x - 1)], h = λxy[max(0, x - y)],
f = λx[min(x, 1)] (`hHat`, `h`, `fmin`; ĥ and f by (v) with k = 1, h from
ĥ by (v) with k = 2 and a substitution), and g = λx[h(1, f(h(x, k)))].
On Nat, `x - y` is max(0, x - y).

What is proved, for all arguments: f₅ = λyx[x + y] (the book: f₅ is
λxy[x + y]), f₆ = λx[2x]; f₆ is not the only selection function of one
variable λx[x], so the printed "f₆ = f₅(f₁, f₁) by (iii)" is refuted and
the line is an instance of (iv); the functions of the hint are as stated
and g(x) = 1 for x ≤ k, g(x) = 0 for k < x, the step function of p. 26
(the other case of p. 26, λx[1], is clause (i)).

Not covered: the definition of the class (the least class closed under
(i)-(v)); the clauses are used as explicit definitions.
-/
namespace RogersRecursive.Ch01_04.Scheme

/-- Clause (v), k = 2. -/
def rec2 (g : Nat → Nat) (h : Nat → Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, x => g x
  | y + 1, x => h y (rec2 g h y x) x

/-- Clause (v), k = 1: g is a number. -/
def rec1 (m : Nat) (h : Nat → Nat → Nat) : Nat → Nat
  | 0 => m
  | y + 1 => h y (rec1 m h y)

def f₁ (x : Nat) : Nat := x
def f₂ (x : Nat) : Nat := x + 1
def f₃ (_ x₂ _ : Nat) : Nat := x₂
def f₄ (x₁ x₂ x₃ : Nat) : Nat := f₂ (f₃ x₁ x₂ x₃)
def f₅ : Nat → Nat → Nat := rec2 f₁ f₄
def f₆ (x : Nat) : Nat := f₅ (f₁ x) (f₁ x)

theorem f₅_eq (y x : Nat) : f₅ y x = x + y := by
  induction y with
  | zero => rfl
  | succ y ih =>
    show f₄ y (f₅ y x) x = x + (y + 1)
    simp only [f₄, f₂, f₃, ih]
    omega

theorem f₆_eq (x : Nat) : f₆ x = 2 * x := by
  simp only [f₆, f₁, f₅_eq]
  omega

/-- The printed rule (iii) gives only λx[x] in one variable; f₆ differs. -/
theorem f₆_not_selection : f₆ ≠ fun x => x := by
  intro h
  have := congrFun h 1
  rw [f₆_eq] at this
  omega

/-- The corrected rule (iv): f₆ is f₅ with f₁, f₁ substituted. -/
theorem f₆_by_substitution : f₆ = fun x => f₅ (f₁ x) (f₁ x) := rfl

def hHat : Nat → Nat := rec1 0 (fun y _ => y)
def H : Nat → Nat → Nat := rec2 (fun x => x) (fun _ acc _ => hHat acc)
def h (x y : Nat) : Nat := H y x
def fmin : Nat → Nat := rec1 0 (fun _ _ => 1)
def g (k x : Nat) : Nat := h 1 (fmin (h x k))

theorem hHat_eq (x : Nat) : hHat x = x - 1 := by
  cases x <;> rfl

theorem H_eq (y x : Nat) : H y x = x - y := by
  induction y with
  | zero => rfl
  | succ y ih =>
    show hHat (H y x) = x - (y + 1)
    rw [ih, hHat_eq]
    omega

theorem h_eq (x y : Nat) : h x y = x - y := H_eq y x

theorem fmin_eq (x : Nat) : fmin x = min x 1 := by
  cases x with
  | zero => rfl
  | succ x => show 1 = min (x + 1) 1; omega

theorem g_eq (k x : Nat) : g k x = if x ≤ k then 1 else 0 := by
  simp only [g, h_eq, fmin_eq]
  split <;> omega

end RogersRecursive.Ch01_04.Scheme

#print axioms RogersRecursive.Ch01_04.Scheme.f₅_eq
#print axioms RogersRecursive.Ch01_04.Scheme.f₆_eq
#print axioms RogersRecursive.Ch01_04.Scheme.f₆_not_selection
#print axioms RogersRecursive.Ch01_04.Scheme.f₆_by_substitution
#print axioms RogersRecursive.Ch01_04.Scheme.hHat_eq
#print axioms RogersRecursive.Ch01_04.Scheme.H_eq
#print axioms RogersRecursive.Ch01_04.Scheme.h_eq
#print axioms RogersRecursive.Ch01_04.Scheme.fmin_eq
#print axioms RogersRecursive.Ch01_04.Scheme.g_eq
