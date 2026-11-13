/-
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная
вычислимость» (Мир, 1972), § 1.2, p. 25: Ackermann's function.

Notation.  `f z x y` is the book's f(z, x, y), defined by the printed
"more formal" equations
  f(0, 0, y) = y,  f(0, x + 1, y) = f(0, x, y) + 1,  f(1, 0, y) = 0,
  f(z + 2, 0, y) = 1,  f(z + 1, x + 1, y) = f(z, f(z + 1, x, y), y).
`g^[n]` is the n-fold iterate (Mathlib.Logic.Function.Iterate).

What is proved: the first three lines of the informal description,
f(0, x, y) = y + x, f(1, x, y) = y x, f(2, x, y) = y^x, for all x, y; the
informal line "f(z + 1, x, y) is the result of applying to y, x - 1 times,
the operation of level z, λuv[f(z, u, v)]" for every z, y and every x >= 1
(as f(z + 1, x + 1, y) = (λu[f(z, u, y)])^[x] y; the order of the
arguments u, y is fixed by the formal equations); and that at x = 0 the
informal line, read with x - 1 = 0, would give y, while f(1, 0, y) = 0 and
f(z + 2, 0, y) = 1 (for example f(1, 0, 2) = 0 and f(2, 0, 2) = 1).  So
the informal description covers x >= 1 only, and the formal equations that
follow it in the book fix the values at x = 0.

Not covered: that λx[f(x, x, x)] is not primitive recursive (footnote,
p. 25); the primitive recursive functions are not formalized here.
-/
import Mathlib.Logic.Function.Iterate

namespace RogersRecursive.Ch01_04.Ackermann

/-- The formal definition of p. 25. -/
def f : Nat → Nat → Nat → Nat
  | 0, 0, y => y
  | 0, x + 1, y => f 0 x y + 1
  | 1, 0, _ => 0
  | _ + 2, 0, _ => 1
  | z + 1, x + 1, y => f z (f (z + 1) x y) y

theorem level0 (x y : Nat) : f 0 x y = y + x := by
  induction x with
  | zero => simp [f]
  | succ x ih => simp [f, ih]; omega

theorem level1 (x y : Nat) : f 1 x y = y * x := by
  induction x with
  | zero => simp [f]
  | succ x ih => rw [f, ih, level0, Nat.mul_succ]; omega

theorem level2 (x y : Nat) : f 2 x y = y ^ x := by
  induction x with
  | zero => simp [f]
  | succ x ih => rw [f, ih, level1, Nat.pow_succ, Nat.mul_comm]

/-- f(z + 1, 1, y) = y: one copy of y. -/
theorem at_one (z y : Nat) : f (z + 1) 1 y = y := by
  induction z with
  | zero => simp [f]
  | succ z ih => rw [f, show f (z + 2) 0 y = 1 by simp [f], ih]

/-- The informal line for x + 1 >= 1: x applications of λu[f(z, u, y)] to y. -/
theorem informal (z x y : Nat) :
    f (z + 1) (x + 1) y = (fun u => f z u y)^[x] y := by
  induction x with
  | zero => simp [at_one]
  | succ x ih => rw [f, ih, Function.iterate_succ_apply']

/-- At x = 0 the informal line (with x - 1 = 0 applications) would give y. -/
theorem informal_fails_at_zero :
    f 1 0 2 ≠ (fun u => f 0 u 2)^[0 - 1] 2 ∧ f 2 0 2 ≠ (fun u => f 1 u 2)^[0 - 1] 2 := by
  simp [f]

theorem level_succ_zero (y : Nat) : f 1 0 y = 0 ∧ ∀ z, f (z + 2) 0 y = 1 := by
  simp [f]

end RogersRecursive.Ch01_04.Ackermann

#print axioms RogersRecursive.Ch01_04.Ackermann.level0
#print axioms RogersRecursive.Ch01_04.Ackermann.level1
#print axioms RogersRecursive.Ch01_04.Ackermann.level2
#print axioms RogersRecursive.Ch01_04.Ackermann.at_one
#print axioms RogersRecursive.Ch01_04.Ackermann.informal
#print axioms RogersRecursive.Ch01_04.Ackermann.informal_fails_at_zero
#print axioms RogersRecursive.Ch01_04.Ackermann.level_succ_zero
