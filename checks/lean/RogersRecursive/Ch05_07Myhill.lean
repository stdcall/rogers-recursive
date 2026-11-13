import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
Book: Х. Роджерс, «Теория рекурсивных функций и эффективная вычислимость»
(Мир, 1972), § 7.4, theorem VI (Майхилл), pp. 116–118, and § 7.5, the proof
of theorem VII, p. 119.

Notation.  A finite correspondence between C and D (p. 116–117) is a list
of pairs ⟨⟨x₁, y₁⟩, …, ⟨xₙ, yₙ⟩⟩ with distinct first components, distinct
second components and xᵢ ∈ C ⇔ yᵢ ∈ D (`IsCorr`).  `back ps y` is the first
component paired with y (none if y is no second component).  For the lemma
of theorem VI, with C ≤₁ D via f, `orbit f ps x' k` is the k-th element of
the chain of the printed procedure: x', then x_(i₁) with f(x') = y_(i₁),
then x_(i₂) with f(x_(i₁)) = y_(i₂), … (none once it has stopped); the
procedure stops at the first element u with f(u) not a second component and
puts y' = f(u).  A reduction is `∀ x, x ∈ C ↔ f x ∈ D` without the
requirement that f be recursive; the procedures are evidently effective
(each step is a computation of f and a look-up in a finite list).

What is proved.  The lemma of theorem VI for every one-one f and every
finite correspondence: the chain stops after at most n + 1 computations of
f (n the length of the correspondence: the elements x_(i₁), x_(i₂), … are
distinct first components), and adding ⟨x', y'⟩ gives a finite
correspondence (`myhill_lemma`).  The back-and-forth construction of the
theorem, stages 2k and 2k + 1 as printed, for one-one g, h with A ≤₁ B via g
and B ≤₁ A via h: every stage keeps a finite correspondence, after stage
2k + 1 the number k is a first and a second component, and the limit map σ
is a permutation of N with x ∈ A ⇔ σ(x) ∈ B (`myhill_iso`): the
combinatorial content of A ≡₁ B ⇒ A ≡ B.  The search for f'(n + 1) in the
proof of theorem VII (p. 119): with g as in the lemma there, the sets
D_(x₀) = {f'(m₀)}, D_(x₁) = {f'(m₀), f'(m₁)}, … stay in {f'(0), …, f'(n)},
grow by one element at each step and keep the side of f(n + 1), so the
search ends in fewer than n + 2 steps with a new value on the same side
(`fprime_search`).

Not covered: that σ is recursive (the stages are effective procedures, by
Church's thesis), the lemma of theorem VII itself (its logical step is
`cylinder_lemma` in Ch05_07Numbering.lean).
-/

namespace RogersRecursive.Ch05_07

/-- A finite correspondence between C and D. -/
def IsCorr (C D : Set ℕ) (ps : List (ℕ × ℕ)) : Prop :=
  (ps.map Prod.fst).Nodup ∧ (ps.map Prod.snd).Nodup ∧ ∀ p ∈ ps, (p.1 ∈ C ↔ p.2 ∈ D)

/-- The first component paired with y. -/
def back (ps : List (ℕ × ℕ)) (y : ℕ) : Option ℕ :=
  (ps.find? (fun p => p.2 == y)).map Prod.fst

theorem back_some {ps : List (ℕ × ℕ)} {y a : ℕ} (h : back ps y = some a) : (a, y) ∈ ps := by
  unfold back at h
  cases hf : ps.find? (fun p => p.2 == y) with
  | none =>
    rw [hf] at h
    simp at h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    obtain ⟨p1, p2⟩ := p
    simp only at h hp
    subst h hp
    exact hmem

theorem back_none {ps : List (ℕ × ℕ)} {y : ℕ} (h : back ps y = none) : y ∉ ps.map Prod.snd := by
  unfold back at h
  cases hf : ps.find? (fun p => p.2 == y) with
  | some p =>
    rw [hf] at h
    simp at h
  | none =>
    rw [List.find?_eq_none] at hf
    intro hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    exact hf p hp (by simp)

theorem back_inj {ps : List (ℕ × ℕ)} (hn : (ps.map Prod.fst).Nodup) {y y' a : ℕ}
    (h : back ps y = some a) (h' : back ps y' = some a) : y = y' := by
  have e := List.inj_on_of_nodup_map hn (back_some h) (back_some h') rfl
  simp only [Prod.mk.injEq] at e
  exact e.2

/-- The chain of the lemma: x', x_(i₁), x_(i₂), … -/
def orbit (f : ℕ → ℕ) (ps : List (ℕ × ℕ)) (x' : ℕ) : ℕ → Option ℕ
  | 0 => some x'
  | k + 1 => (orbit f ps x' k).bind (fun u => back ps (f u))

theorem orbit_succ_some {f : ℕ → ℕ} {ps : List (ℕ × ℕ)} {x' k a : ℕ}
    (h : orbit f ps x' (k + 1) = some a) :
    ∃ u, orbit f ps x' k = some u ∧ back ps (f u) = some a := by
  simp only [orbit] at h
  exact Option.bind_eq_some_iff.1 h

theorem orbit_mem_fst {f : ℕ → ℕ} {ps : List (ℕ × ℕ)} {x' k a : ℕ}
    (h : orbit f ps x' (k + 1) = some a) : a ∈ ps.map Prod.fst := by
  obtain ⟨u, _, hb⟩ := orbit_succ_some h
  exact List.mem_map.2 ⟨(a, f u), back_some hb, rfl⟩

/-- Every element of the chain is on the side of x'. -/
theorem orbit_side (C D : Set ℕ) (f : ℕ → ℕ) (hCD : ∀ x, x ∈ C ↔ f x ∈ D)
    (ps : List (ℕ × ℕ)) (hag : ∀ p ∈ ps, (p.1 ∈ C ↔ p.2 ∈ D)) (x' : ℕ) :
    ∀ k u, orbit f ps x' k = some u → (u ∈ C ↔ x' ∈ C)
  | 0, u, h => by
    simp only [orbit, Option.some.injEq] at h
    rw [h]
  | k + 1, a, h => by
    obtain ⟨u, hu, hb⟩ := orbit_succ_some h
    have hp := hag _ (back_some hb)
    simp only at hp
    rw [hp, ← hCD]
    exact orbit_side C D f hCD ps hag x' k u hu

/-- The elements of the chain are distinct. -/
theorem orbit_distinct (f : ℕ → ℕ) (hf : Function.Injective f) (ps : List (ℕ × ℕ))
    (hn : (ps.map Prod.fst).Nodup) (x' : ℕ) (hx' : x' ∉ ps.map Prod.fst) :
    ∀ i j v, i < j → orbit f ps x' j = some v → orbit f ps x' i ≠ some v
  | 0, j, v, hij, hj => by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    intro h0
    simp only [orbit, Option.some.injEq] at h0
    subst h0
    exact hx' (orbit_mem_fst hj)
  | i + 1, j, v, hij, hj => by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    intro hi
    obtain ⟨a, ha, hba⟩ := orbit_succ_some hi
    obtain ⟨b, hb, hbb⟩ := orbit_succ_some hj
    have hab : a = b := hf (back_inj hn hba hbb)
    subst hab
    exact orbit_distinct f hf ps hn x' hx' i j' a (by omega) hb ha

/-- The chain stops within n + 1 computations of f. -/
theorem orbit_terminates (f : ℕ → ℕ) (hf : Function.Injective f) (ps : List (ℕ × ℕ))
    (hn : (ps.map Prod.fst).Nodup) (x' : ℕ) (hx' : x' ∉ ps.map Prod.fst) :
    ∃ k ≤ ps.length, ∃ u, orbit f ps x' k = some u ∧ back ps (f u) = none := by
  classical
  by_contra H
  have hall : ∀ k ≤ ps.length + 1, ∃ u, orbit f ps x' k = some u := by
    intro k hk
    induction k with
    | zero => exact ⟨x', rfl⟩
    | succ k ih =>
      obtain ⟨u, hu⟩ := ih (by omega)
      cases hb : back ps (f u) with
      | none => exact absurd ⟨k, by omega, u, hu, hb⟩ H
      | some a => exact ⟨a, by simp [orbit, hu, hb]⟩
  let val : ℕ → ℕ := fun k => (orbit f ps x' (k + 1)).getD 0
  have hval : ∀ k < ps.length + 1, orbit f ps x' (k + 1) = some (val k) := by
    intro k hk
    obtain ⟨u, hu⟩ := hall (k + 1) (by omega)
    simp [val, hu]
  have hsub : (Finset.range (ps.length + 1)).image val ⊆ (ps.map Prod.fst).toFinset := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    exact List.mem_toFinset.2 (orbit_mem_fst (hval k (Finset.mem_range.1 hk)))
  have hinj : Set.InjOn val ↑(Finset.range (ps.length + 1)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact orbit_distinct f hf ps hn x' hx' (i + 1) (j + 1) (val j) (by omega) (hval j hj)
        (by rw [hval i hi, hij])
    · exact orbit_distinct f hf ps hn x' hx' (j + 1) (i + 1) (val i) (by omega) (hval i hi)
        (by rw [hval j hj, hij])
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h1
  have h2 := List.toFinset_card_le (ps.map Prod.fst)
  rw [List.length_map] at h2
  omega

/-- Adding ⟨x', f(u)⟩ for the stopping element u keeps a finite correspondence. -/
theorem extend_corr (C D : Set ℕ) (f : ℕ → ℕ) (hCD : ∀ x, x ∈ C ↔ f x ∈ D)
    (ps : List (ℕ × ℕ)) (hps : IsCorr C D ps) (x' : ℕ) (hx' : x' ∉ ps.map Prod.fst)
    (k u : ℕ) (hu : orbit f ps x' k = some u) (hb : back ps (f u) = none) :
    IsCorr C D (ps ++ [(x', f u)]) := by
  obtain ⟨hn1, hn2, hag⟩ := hps
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
      List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
      List.mem_cons, or_false, true_and]
    refine ⟨hn1, ?_⟩
    rintro a ha b rfl rfl
    exact hx' ha
  · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
      List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
      List.mem_cons, or_false, true_and]
    refine ⟨hn2, ?_⟩
    rintro a ha b rfl rfl
    exact back_none hb ha
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hag p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      simp only
      rw [← hCD]
      exact (orbit_side C D f hCD ps hag x' k u hu).symm

/-- The lemma of theorem VI (p. 117). -/
theorem myhill_lemma (C D : Set ℕ) (f : ℕ → ℕ) (hf : Function.Injective f)
    (hCD : ∀ x, x ∈ C ↔ f x ∈ D) (ps : List (ℕ × ℕ)) (hps : IsCorr C D ps)
    (x' : ℕ) (hx' : x' ∉ ps.map Prod.fst) :
    ∃ k ≤ ps.length, ∃ u, orbit f ps x' k = some u ∧ back ps (f u) = none ∧
      IsCorr C D (ps ++ [(x', f u)]) := by
  obtain ⟨k, hk, u, hu, hb⟩ := orbit_terminates f hf ps hps.1 x' hx'
  exact ⟨k, hk, u, hu, hb, extend_corr C D f hCD ps hps x' hx' k u hu hb⟩

/-! ### The stages of the proof of theorem VI -/

open Classical in
/-- The index at which the chain stops (the least one). -/
noncomputable def stopIdx (f : ℕ → ℕ) (ps : List (ℕ × ℕ)) (x' : ℕ) : ℕ :=
  if h : ∃ k, ∃ u, orbit f ps x' k = some u ∧ back ps (f u) = none then Nat.find h else 0

/-- The result y' of the procedure of the lemma. -/
noncomputable def extendBy (f : ℕ → ℕ) (ps : List (ℕ × ℕ)) (x' : ℕ) : ℕ :=
  f ((orbit f ps x' (stopIdx f ps x')).getD 0)

theorem ext_spec (C D : Set ℕ) (f : ℕ → ℕ) (hf : Function.Injective f)
    (hCD : ∀ x, x ∈ C ↔ f x ∈ D) (ps : List (ℕ × ℕ)) (hps : IsCorr C D ps)
    (x' : ℕ) (hx' : x' ∉ ps.map Prod.fst) :
    IsCorr C D (ps ++ [(x', extendBy f ps x')]) := by
  classical
  obtain ⟨k, _, u, hu, hb⟩ := orbit_terminates f hf ps hps.1 x' hx'
  have h : ∃ k, ∃ u, orbit f ps x' k = some u ∧ back ps (f u) = none := ⟨k, u, hu, hb⟩
  obtain ⟨u', hu', hb'⟩ := Nat.find_spec h
  have hidx : stopIdx f ps x' = Nat.find h := by
    unfold stopIdx
    rw [dite_eq_left h]
  have hext : extendBy f ps x' = f u' := by
    unfold extendBy
    rw [hidx, hu']
    rfl
  rw [hext]
  exact extend_corr C D f hCD ps hps x' hx' _ u' hu' hb'

/-- The pairs with exchanged components. -/
def swapList (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) := ps.map Prod.swap

theorem swap_corr {C D : Set ℕ} {ps : List (ℕ × ℕ)} (h : IsCorr C D ps) :
    IsCorr D C (swapList ps) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [swapList, List.map_map]
    exact h2
  · simp only [swapList, List.map_map]
    exact h1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact (h3 q hq).symm

theorem swapList_swap (ps : List (ℕ × ℕ)) : swapList (swapList ps) = ps := by
  simp [swapList, List.map_map]

theorem swapList_append (ps : List (ℕ × ℕ)) (a b : ℕ) :
    swapList (ps ++ [(a, b)]) = swapList ps ++ [(b, a)] := by
  simp [swapList]

/-- The list of pairs after stages 0, …, s − 1 (stage 2k: a pair with first
component k by the lemma with g; stage 2k + 1: a pair with second component
k by the lemma with h and the roles of A and B exchanged). -/
noncomputable def stageList (g h : ℕ → ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | s + 1 =>
    if s % 2 = 0 then
      (if s / 2 ∈ (stageList g h s).map Prod.fst then stageList g h s
        else stageList g h s ++ [(s / 2, extendBy g (stageList g h s) (s / 2))])
    else
      (if s / 2 ∈ (stageList g h s).map Prod.snd then stageList g h s
        else stageList g h s ++ [(extendBy h (swapList (stageList g h s)) (s / 2), s / 2)])

/-- Stage 0 as printed: the first pair is ⟨0, g(0)⟩. -/
theorem stage_zero (g h : ℕ → ℕ) : stageList g h 1 = [(0, g 0)] := by
  have hstop : extendBy g [] 0 = g 0 := by
    have hb : back [] (g 0) = none := rfl
    have h0 : ∃ k, ∃ u, orbit g [] 0 k = some u ∧ back [] (g u) = none := ⟨0, 0, rfl, hb⟩
    have hfind : Nat.find h0 = 0 := by
      rw [Nat.find_eq_zero]
      exact ⟨0, rfl, hb⟩
    unfold extendBy stopIdx
    rw [dite_eq_left h0, hfind]
    rfl
  simp [stageList, hstop]

theorem stage_mono (g h : ℕ → ℕ) {p : ℕ × ℕ} {s t : ℕ} (hst : s ≤ t)
    (hp : p ∈ stageList g h s) : p ∈ stageList g h t := by
  induction hst with
  | refl => exact hp
  | step _ ih =>
    simp only [stageList]
    split_ifs <;> simp [ih]

theorem stage_corr (A B : Set ℕ) (g h : ℕ → ℕ) (hgi : Function.Injective g)
    (hhi : Function.Injective h) (hg : ∀ x, x ∈ A ↔ g x ∈ B) (hh : ∀ y, y ∈ B ↔ h y ∈ A) :
    ∀ s, IsCorr A B (stageList g h s)
  | 0 => ⟨List.nodup_nil, List.nodup_nil, fun _ hp => absurd hp List.not_mem_nil⟩
  | s + 1 => by
    have ih := stage_corr A B g h hgi hhi hg hh s
    simp only [stageList]
    split_ifs with h1 h2 h3
    · exact ih
    · exact ext_spec A B g hgi hg _ ih _ h2
    · exact ih
    · have hs := ext_spec B A h hhi hh _ (swap_corr ih) (s / 2)
        (by simp only [swapList, List.map_map]; exact h3)
      have := swap_corr hs
      rw [swapList_append, swapList_swap] at this
      exact this

/-- After stage 2k the number k is a first component; after stage 2k + 1 a
second one. -/
theorem stage_cover (g h : ℕ → ℕ) (k : ℕ) :
    k ∈ (stageList g h (2 * k + 1)).map Prod.fst ∧
      k ∈ (stageList g h (2 * k + 2)).map Prod.snd := by
  constructor
  · rw [stageList.eq_2, ite_eq_left (show 2 * k % 2 = 0 by omega), show 2 * k / 2 = k by omega]
    split_ifs with h1
    · exact h1
    · simp
  · rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, stageList.eq_2,
      ite_eq_right (show ¬ (2 * k + 1) % 2 = 0 by omega), show (2 * k + 1) / 2 = k by omega]
    split_ifs with h1
    · exact h1
    · simp

open Classical in
/-- The limit map: σ(x) is the second component paired with x. -/
noncomputable def myhillSigma (g h : ℕ → ℕ) (x : ℕ) : ℕ :=
  if hx : ∃ y, (x, y) ∈ stageList g h (2 * x + 1) then Classical.choose hx else 0

theorem sigma_mem (g h : ℕ → ℕ) (x : ℕ) : (x, myhillSigma g h x) ∈ stageList g h (2 * x + 1) := by
  have hx : ∃ y, (x, y) ∈ stageList g h (2 * x + 1) := by
    obtain ⟨⟨a, b⟩, hp, hpx⟩ := List.mem_map.1 (stage_cover g h x).1
    simp only at hpx
    subst hpx
    exact ⟨b, hp⟩
  unfold myhillSigma
  rw [dite_eq_left hx]
  exact Classical.choose_spec hx

/-- Theorem VI (Myhill), the combinatorial content: σ is a permutation of N
with x ∈ A ⇔ σ(x) ∈ B. -/
theorem myhill_iso (A B : Set ℕ) (g h : ℕ → ℕ) (hgi : Function.Injective g)
    (hhi : Function.Injective h) (hg : ∀ x, x ∈ A ↔ g x ∈ B) (hh : ∀ y, y ∈ B ↔ h y ∈ A) :
    Function.Bijective (myhillSigma g h) ∧ ∀ x, x ∈ A ↔ myhillSigma g h x ∈ B := by
  have corr := stage_corr A B g h hgi hhi hg hh
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x x' hxx
    have m1 := stage_mono g h (le_max_left (2 * x + 1) (2 * x' + 1)) (sigma_mem g h x)
    have m2 := stage_mono g h (le_max_right (2 * x + 1) (2 * x' + 1)) (sigma_mem g h x')
    have e := List.inj_on_of_nodup_map (corr _).2.1 m1 m2 hxx
    simp only [Prod.mk.injEq] at e
    exact e.1
  · intro y
    obtain ⟨p, hp, hpy⟩ := List.mem_map.1 (stage_cover g h y).2
    refine ⟨p.1, ?_⟩
    have m1 := stage_mono g h (le_max_left (2 * p.1 + 1) (2 * y + 2)) (sigma_mem g h p.1)
    have m2 := stage_mono g h (le_max_right (2 * p.1 + 1) (2 * y + 2)) hp
    have e := List.inj_on_of_nodup_map (corr _).1 m1 m2 rfl
    rw [← e] at hpy
    exact hpy
  · intro x
    exact (corr _).2.2 _ (sigma_mem g h x)

/-! ### The search for f'(n + 1) in the proof of theorem VII -/

/-- D_(x₀) = {y₀}, D_(x_(k+1)) = D_(x_k) ∪ {g(x_k)}, with y₀ = f(n + 1) = f'(m₀). -/
def searchSeq (g : Finset ℕ → ℕ) (y₀ : ℕ) : ℕ → Finset ℕ
  | 0 => {y₀}
  | k + 1 => insert (g (searchSeq g y₀ k)) (searchSeq g y₀ k)

theorem fprime_search (A : Set ℕ) (g : Finset ℕ → ℕ)
    (hg : ∀ D : Finset ℕ, D.Nonempty → (∀ d ∈ D, d ∈ A) → g D ∈ A ∧ g D ∉ D)
    (hg' : ∀ D : Finset ℕ, D.Nonempty → (∀ d ∈ D, d ∉ A) → g D ∉ A ∧ g D ∉ D)
    (F : Finset ℕ) (y₀ : ℕ) (hy₀ : y₀ ∈ F) :
    ∃ k < F.card, g (searchSeq g y₀ k) ∉ F ∧ searchSeq g y₀ k ⊆ F ∧
      (g (searchSeq g y₀ k) ∈ A ↔ y₀ ∈ A) := by
  classical
  have mem0 : ∀ k, y₀ ∈ searchSeq g y₀ k := by
    intro k
    induction k with
    | zero => simp [searchSeq]
    | succ k ih => exact Finset.mem_insert_of_mem ih
  have side : ∀ k, ∀ d ∈ searchSeq g y₀ k, (d ∈ A ↔ y₀ ∈ A) := by
    intro k
    induction k with
    | zero =>
      intro d hd
      simp only [searchSeq, Finset.mem_singleton] at hd
      rw [hd]
    | succ k ih =>
      intro d hd
      simp only [searchSeq, Finset.mem_insert] at hd
      rcases hd with rfl | hd
      · by_cases hy : y₀ ∈ A
        · exact iff_of_true (hg _ ⟨y₀, mem0 k⟩ (fun d hd => (ih d hd).2 hy)).1 hy
        · exact iff_of_false (hg' _ ⟨y₀, mem0 k⟩ (fun d hd h => hy ((ih d hd).1 h))).1 hy
      · exact ih d hd
  have fresh : ∀ k, g (searchSeq g y₀ k) ∉ searchSeq g y₀ k ∧
      (g (searchSeq g y₀ k) ∈ A ↔ y₀ ∈ A) := by
    intro k
    by_cases hy : y₀ ∈ A
    · have := hg _ ⟨y₀, mem0 k⟩ (fun d hd => (side k d hd).2 hy)
      exact ⟨this.2, iff_of_true this.1 hy⟩
    · have := hg' _ ⟨y₀, mem0 k⟩ (fun d hd h => hy ((side k d hd).1 h))
      exact ⟨this.2, iff_of_false this.1 hy⟩
  have card : ∀ k, (searchSeq g y₀ k).card = k + 1 := by
    intro k
    induction k with
    | zero => simp [searchSeq]
    | succ k ih =>
      simp only [searchSeq]
      rw [Finset.card_insert_of_notMem (fresh k).1, ih]
  have sub : ∀ k, (∀ j < k, g (searchSeq g y₀ j) ∈ F) → searchSeq g y₀ k ⊆ F := by
    intro k
    induction k with
    | zero =>
      intro _ d hd
      simp only [searchSeq, Finset.mem_singleton] at hd
      rw [hd]
      exact hy₀
    | succ k ih =>
      intro hj d hd
      simp only [searchSeq, Finset.mem_insert] at hd
      rcases hd with rfl | hd
      · exact hj k (by omega)
      · exact ih (fun j hjk => hj j (by omega)) hd
  have hex : ∃ k, k < F.card ∧ g (searchSeq g y₀ k) ∉ F := by
    by_contra H
    have hall : ∀ j < F.card, g (searchSeq g y₀ j) ∈ F := by
      intro j hj
      by_contra hn
      exact H ⟨j, hj, hn⟩
    have := Finset.card_le_card (sub F.card hall)
    rw [card] at this
    omega
  have hk := Nat.find_spec hex
  refine ⟨Nat.find hex, hk.1, hk.2, ?_, (fresh _).2⟩
  apply sub
  intro j hj
  by_contra hn
  exact Nat.find_min hex hj ⟨by have := hk.1; omega, hn⟩

end RogersRecursive.Ch05_07

#print axioms RogersRecursive.Ch05_07.back_some
#print axioms RogersRecursive.Ch05_07.back_none
#print axioms RogersRecursive.Ch05_07.orbit_side
#print axioms RogersRecursive.Ch05_07.orbit_distinct
#print axioms RogersRecursive.Ch05_07.orbit_terminates
#print axioms RogersRecursive.Ch05_07.extend_corr
#print axioms RogersRecursive.Ch05_07.myhill_lemma
#print axioms RogersRecursive.Ch05_07.ext_spec
#print axioms RogersRecursive.Ch05_07.swap_corr
#print axioms RogersRecursive.Ch05_07.stage_zero
#print axioms RogersRecursive.Ch05_07.stage_mono
#print axioms RogersRecursive.Ch05_07.stage_corr
#print axioms RogersRecursive.Ch05_07.stage_cover
#print axioms RogersRecursive.Ch05_07.sigma_mem
#print axioms RogersRecursive.Ch05_07.myhill_iso
#print axioms RogersRecursive.Ch05_07.fprime_search
