import Mathlib.Order.Basic

/-!
# Friedberg's jump inversion: the construction of `th:jump-inversion`

Place in the book: § 13.3, `th:jump-inversion` (pp. 341-342) and its
proof; the notation `φ_z^[f]` of § 13.1 (`pg:segment-notation`, p. 332).

The oracle computations are an arbitrary family `Φ n σ x` (the value
`φ_n^[σ](x)` on the initial segment `σ`, a list of values
`f(0), …, f(len - 1)`) with the property of p. 333: a value on `σ` stays
on every extension of `σ` (`Persistent`).  For a total `F`, `φ_n^F(x)` is
defined when some initial segment of `F` gives a value, and the jump is
`(τ(F))' = {n | φ_n^F(n) is defined}` (`jump`).

The construction (stage `n + 1`): if some initial segment extending `f_n`
gives `φ_n^[·](n)` a value, `f*` is a chosen one, otherwise `f* = f_n`;
`f_(n+1) = f* ∪ {⟨x_n, g(n)⟩}`, `x_n` the length of `f*` (`seg`).  For an
arbitrary `g` (in the book `g = c_A`) and the union `f` of the segments
(`limit`):

* `seg_mono`, `length_seg`, `prefixOf_limit_seg`: the segments form a chain
  of initial segments of `f`;
* `jump_eq` (part (i)): `n ∈ (τ(f))'` exactly when the extension was found
  at stage `n + 1` — the set `{n | существование сегмента f̃ установлено
  на этапе n + 1}` of p. 341 is the jump of `f`;
* `limit_decode` (part (ii)): `g(n)` is the last value of `f_(n+1)`:
  `f(x_n) = g(n)`.

Not covered: the recursiveness of the procedures relative to `A` and `K`
(parts (i), (ii) as reducibilities), the choice of the first extension in
an effective enumeration (any choice works for these identities).
-/

namespace RogersRecursive.Ch13_14.JumpInversion

/-- A segment `f(0), …, f(len - 1)`. -/
abbrev Seg := List Bool

variable (Φ : ℕ → Seg → ℕ → Option ℕ)

/-- A value on `σ` stays on every extension of `σ` (p. 333). -/
def Persistent : Prop := ∀ n σ τ x y, σ <+: τ → Φ n σ x = some y → Φ n τ x = some y

/-- The initial segment of length `k` of a total `F`. -/
def prefixOf (F : ℕ → Bool) (k : ℕ) : Seg := List.ofFn fun i : Fin k => F i

/-- `φ_n^F(x)` is defined. -/
def Defined (n : ℕ) (F : ℕ → Bool) (x : ℕ) : Prop := ∃ k y, Φ n (prefixOf F k) x = some y

/-- `(τ(F))' = {n | φ_n^F(n) is defined}`. -/
def jump (F : ℕ → Bool) : Set ℕ := {n | Defined Φ n F n}

/-- The question of stage `n + 1`: an initial segment extending `σ` on
which `φ_n^[·](n)` is defined. -/
def Found (n : ℕ) (σ : Seg) : Prop := ∃ τ, σ <+: τ ∧ ∃ y, Φ n τ n = some y

open Classical in
/-- `f*` of stage `n + 1`. -/
noncomputable def star (n : ℕ) (σ : Seg) : Seg :=
  if h : Found Φ n σ then Classical.choose h else σ

/-- The segments `f_0 = ∅`, `f_(n+1) = f* ∪ {⟨x_n, g(n)⟩}`. -/
noncomputable def seg (g : ℕ → Bool) : ℕ → Seg
  | 0 => []
  | n + 1 => star Φ n (seg g n) ++ [g n]

/-- The union `f` of the segments. -/
noncomputable def limit (g : ℕ → Bool) (x : ℕ) : Bool := ((seg Φ g (x + 1))[x]?).getD false

theorem star_prefix (n : ℕ) (σ : Seg) : σ <+: star Φ n σ := by
  unfold star
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · exact List.prefix_refl σ

theorem star_found (n : ℕ) (σ : Seg) (h : Found Φ n σ) : ∃ y, Φ n (star Φ n σ) n = some y := by
  unfold star
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec h).2

variable (g : ℕ → Bool)

theorem seg_succ (n : ℕ) : seg Φ g (n + 1) = star Φ n (seg Φ g n) ++ [g n] := rfl

theorem seg_prefix_succ (n : ℕ) : seg Φ g n <+: seg Φ g (n + 1) :=
  (star_prefix Φ n _).trans (List.prefix_append _ _)

theorem seg_mono {m n : ℕ} (h : m ≤ n) : seg Φ g m <+: seg Φ g n := by
  induction n with
  | zero =>
    rw [Nat.le_zero.mp h]
    exact List.prefix_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact (ih (Nat.le_of_lt_succ h')).trans (seg_prefix_succ Φ g n)
    · rw [h']
      exact List.prefix_refl _

theorem length_seg (n : ℕ) : n ≤ (seg Φ g n).length := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [seg_succ, List.length_append]
    have := (star_prefix Φ n (seg Φ g n)).length_le
    simp only [List.length_singleton]
    omega

theorem limit_eq_getElem (n i : ℕ) (hi : i < (seg Φ g n).length) :
    limit Φ g i = (seg Φ g n)[i] := by
  have hi' : i < (seg Φ g (i + 1)).length := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (length_seg Φ g _)
  unfold limit
  rw [List.getElem?_eq_getElem hi', Option.getD_some]
  rcases Nat.le_total n (i + 1) with h | h
  · exact ((seg_mono Φ g h).getElem hi).symm
  · exact (seg_mono Φ g h).getElem hi'

theorem prefixOf_limit_seg (n : ℕ) :
    prefixOf (limit Φ g) (seg Φ g n).length = seg Φ g n := by
  apply List.ext_getElem
  · simp only [prefixOf, List.length_ofFn]
  · intro i h₁ h₂
    simp only [prefixOf, List.getElem_ofFn]
    exact limit_eq_getElem Φ g n i h₂

theorem prefixOf_mono (F : ℕ → Bool) {k k' : ℕ} (h : k ≤ k') : prefixOf F k <+: prefixOf F k' := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp only [prefixOf, List.length_ofFn, List.length_take]
    omega
  · intro i h₁ h₂
    simp only [prefixOf, List.getElem_ofFn, List.getElem_take]

/-- Part (i): the jump of `f` is the set of stages where an extension was
found. -/
theorem jump_eq (hP : Persistent Φ) (n : ℕ) :
    n ∈ jump Φ (limit Φ g) ↔ Found Φ n (seg Φ g n) := by
  constructor
  · rintro ⟨k, y, hk⟩
    let K := max k (seg Φ g n).length
    refine ⟨prefixOf (limit Φ g) K, ?_, y, ?_⟩
    · have h := prefixOf_mono (limit Φ g) (Nat.le_max_right k (seg Φ g n).length)
      rwa [prefixOf_limit_seg] at h
    · exact hP n _ _ n y (prefixOf_mono (limit Φ g) (Nat.le_max_left _ _)) hk
  · intro h
    obtain ⟨y, hy⟩ := star_found Φ n _ h
    refine ⟨(seg Φ g (n + 1)).length, y, ?_⟩
    rw [prefixOf_limit_seg]
    exact hP n _ _ n y (List.prefix_append _ _) hy

/-- Part (ii): `g(n)` is the last value of `f_(n+1)`, at `x_n`, the length
of `f*`. -/
theorem limit_decode (n : ℕ) : limit Φ g (star Φ n (seg Φ g n)).length = g n := by
  have hlen : (star Φ n (seg Φ g n)).length < (seg Φ g (n + 1)).length := by
    rw [seg_succ, List.length_append, List.length_singleton]
    omega
  rw [limit_eq_getElem Φ g (n + 1) _ hlen]
  simp only [seg_succ]
  exact List.getElem_concat_length rfl _

end RogersRecursive.Ch13_14.JumpInversion

#print axioms RogersRecursive.Ch13_14.JumpInversion.star_prefix
#print axioms RogersRecursive.Ch13_14.JumpInversion.star_found
#print axioms RogersRecursive.Ch13_14.JumpInversion.seg_mono
#print axioms RogersRecursive.Ch13_14.JumpInversion.length_seg
#print axioms RogersRecursive.Ch13_14.JumpInversion.prefixOf_limit_seg
#print axioms RogersRecursive.Ch13_14.JumpInversion.prefixOf_mono
#print axioms RogersRecursive.Ch13_14.JumpInversion.jump_eq
#print axioms RogersRecursive.Ch13_14.JumpInversion.limit_decode
