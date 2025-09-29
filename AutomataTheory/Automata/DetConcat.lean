  /-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Det

/-!
This file defines and prove properties about the concatenation construction
for deterministic automata under the Muller acceptance condition, based on
the "flag construction" due to Choueka (see README for the reference).
-/

open Function Set Prod Option Filter
open Classical

namespace Automata

section AutomataDetConcat

variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)

/-- The concatenation automaton runs M1 in parallel with at most n2 + 2 copies
of M2, where n2 is the number of states of M2.  (So this construction only
makes sense when M2 is finite-state.)  An new M2 copy is activated whenever M1
reaches an accepting state and for any M2 copies in the same state, only the one
with the lowest index is kept and all other copies are deactivated in the next step.
The reason to have n2 + 2 copies is to ensure that an empty slot can always be found
for a new copy of M2, because it is possible to have two M2 copies to be in the same
state at the same time.  (The maximum possible number of active copies is n2 + 1.)
Note that we never need to activate and deactivate the same copy at the same time.
-/
noncomputable def DA.Concat : DA A where
  State := M1.State × (Fin (Nat.card M2.State + 2) → Option M2.State)
  init := (M1.init, fun _ ↦ none)
  next := fun s a ↦ (M1.next s.1 a, fun i ↦
    match (s.2 i) with
    | some s2 =>
      if ∀ j < i, (h : (s.2 j).isSome) → (s.2 j).get h ≠ s2
      then some (M2.next s2 a)
      else none
    | none =>
      if s.1 ∈ acc1 ∧ ∀ j < i, (s.2 j).isSome
      then some (M2.next M2.init a)
      else none
    )

/-- A helper lemma to make the definition of DA.Concat easier to use.
-/
lemma da_concat_next_2 (s : (M1.Concat acc1 M2).State) (a : A) (i : Fin (Nat.card M2.State + 2)) :
    ((M1.Concat acc1 M2).next s a).2 i =
    match (s.2 i) with
    | some s2 =>
      if ∀ j < i, (h : (s.2 j).isSome) → (s.2 j).get h ≠ s2
      then some (M2.next s2 a)
      else none
    | none =>
      if s.1 ∈ acc1 ∧ ∀ j < i, (s.2 j).isSome
      then some (M2.next M2.init a)
      else none
  := by rfl

/-- The first state component of `M1.Concat acc1 M2` is the same as M1 running alone.
-/
theorem da_concat_det_run_1 (as : ℕ → A) (k : ℕ) :
    ((M1.Concat acc1 M2).DetRun as k).1 = M1.DetRun as k := by
  induction' k with k h_ind <;> simp [DA.DetRun]
  · rfl
  simp [← h_ind] ; rfl

/-- If any `M2` copy in the second state component of `M1.Concat acc1 M2` ever
stabilizes (in the sense of never being deactivated from some point on), then
it contains an infinite run of `M2` starting from its activation.
-/
theorem da_concat_det_run_2 (as : ℕ → A) (n : ℕ) (i : Fin (Nat.card M2.State + 2))
    (h : ∀ k ≥ n, (((M1.Concat acc1 M2).DetRun as k).2 i).isSome) :
    ∃ m < n, M1.DetRun as m ∈ acc1 ∧
      ∀ k > m, ((M1.Concat acc1 M2).DetRun as k).2 i = some (M2.DetRun (as <<< m) (k - m)) := by
  let P := (fun k ↦ ((M1.Concat acc1 M2).DetRun as k).2 i = none)
  let m := Nat.findGreatest P n
  have h_m : P m := by
    unfold m
    apply Nat.findGreatest_spec (P := P) (show 0 ≤ n by omega)
    simp [P, DA.DetRun, DA.Concat]
  have h_n : m < n := by
    have : m ≤ n := by apply Nat.findGreatest_le
    suffices h_eq : m ≠ n by omega
    by_contra h_contra
    simp [h_contra, P] at h_m
    specialize h n (by omega)
    simp [h_m] at h
  have h_gt_m : ∀ k > m, ∃ s2, ((M1.Concat acc1 M2).DetRun as k).2 i = some s2 := by
    intro k h_k
    rcases (show k ≤ n ∨ k ≥ n by omega) with h_k' | h_k'
    · exact ne_none_iff_exists'.mp <| Nat.findGreatest_is_greatest (P := P) (n := n) (k := k) h_k h_k'
    · exact isSome_iff_exists.mp <| h k h_k'
  obtain ⟨s2, h_s2⟩ := h_gt_m (m + 1) (by omega)
  unfold P at h_m
  obtain ⟨h_acc1, rfl⟩ : M1.DetRun as m ∈ acc1 ∧ DA.next DA.init (as m) = s2 := by
    have h_next := da_concat_next_2 M1 acc1 M2 ((M1.Concat acc1 M2).DetRun as m) (as m) i
    simp [DA.DetRun, h_next, h_m, da_concat_det_run_1] at h_s2
    tauto
  use m ; simp [h_n, h_acc1]
  intro k h_k
  obtain ⟨j, rfl⟩ := show ∃ j, k = m + 1 + j by use k - m - 1 ; omega
  induction' j with j h_ind
  · simp [DA.DetRun] at h_s2 ⊢
    simp [h_s2, get_drop']
  specialize h_ind (by omega)
  have h_next := da_concat_next_2 M1 acc1 M2 ((M1.Concat acc1 M2).DetRun as (m + 1 + j)) (as (m + 1 + j)) i
  simp [h_ind, eq_ite_iff] at h_next
  rcases h_next with ⟨_, h_some⟩ | ⟨_, h_none⟩
  · simp [DA.DetRun, h_some, get_drop',
      (show m + (1 + j) = m + 1 + j by omega), (show m + 1 + j - m = 1 + j by omega),
      (show m + 1 + (j + 1) - m = 1 + j + 1 by omega)]
  · obtain ⟨s2', h_s2'⟩ := h_gt_m (m + 1 + j + 1) (by omega)
    simp [DA.DetRun, h_none] at h_s2'

variable [Finite M2.State]

/-- The second state component of `M1.Concat acc1 M2` always has at least
one inactive copy of `M2` available.
-/
theorem da_concat_det_run_cnt2 (as : ℕ → A) (n : ℕ) :
    ∃ i, ((M1.Concat acc1 M2).DetRun as n).2 i = none := by
  induction' n with n h_ind
  · use 0 ; simp [DA.DetRun, DA.Concat]
  let s_n := (M1.Concat acc1 M2).DetRun as n
  obtain ⟨i, h_i⟩ := h_ind
  rcases Classical.em (∃ j, j ≠ i ∧ s_n.2 j = none) with h_none | h_some
  · obtain ⟨j, h_ne, h_j⟩ := h_none
    simp [s_n] at h_j
    wlog h : i < j generalizing i j with h'
    · exact h' j h_j i (Ne.symm h_ne) h_i (by fin_omega)
    use j ; simp [DA.DetRun, da_concat_next_2, h_j]
    intro _ ; use i
  · simp [ne_none_iff_isSome] at h_some
    have h1 : {j | (s_n.2 j).isSome} = {i}ᶜ := by ext j ; simp ; grind
    have h2 : {j | (s_n.2 j).isSome}.ncard = Nat.card M2.State + 1 := by
      have h_sum := ncard_add_ncard_compl {i} ; simp at h_sum
      rw [h1] ; omega
    obtain ⟨j1, j2, h_ne, s2, h_j1, h_j2⟩ := option_some_pigeonhole s_n.2 (by omega)
    wlog h : j1 < j2 generalizing j1 j2 with h'
    · exact h' j2 j1 (Ne.symm h_ne) h_j2 h_j1 (by fin_omega)
    simp [s_n] at h_j1 h_j2
    use j2 ; simp [DA.DetRun, da_concat_next_2, h_j2]
    use j1 ; simp [h, h_j1]

/-- The copy `i` of `M2` being asserted to exist by this theorem is activated at
step `n` and persists ever after.  But `i` may not stay constant over time.
-/
theorem da_concat_ptr2_exists (as : ℕ → A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1) (k : ℕ) :
    ∃ i, ((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 i = some (M2.DetRun (as <<< n) (k + 1)) ∧
      if k = 0 then
        ((M1.Concat acc1 M2).DetRun as (n + k)).2 i = none ∧
        ∀ j < i, (((M1.Concat acc1 M2).DetRun as (n + k)).2 j).isSome
      else
        ((M1.Concat acc1 M2).DetRun as (n + k)).2 i = some (M2.DetRun (as <<< n) k) ∧
        ∀ j < i, ((M1.Concat acc1 M2).DetRun as (n + k)).2 j ≠ ((M1.Concat acc1 M2).DetRun as (n + k)).2 i := by
  induction' k with k h_ind
  . let I := {i | ((M1.Concat acc1 M2).DetRun as n).2 i = none}
    have h_fin : I.Finite := by exact toFinite I
    have h_ne : I.Nonempty := by exact da_concat_det_run_cnt2 M1 acc1 M2 as n
    obtain ⟨i, h_i, h_min⟩ := Finite.exists_minimal h_fin h_ne
    simp [I] at h_i h_min
    use i
    simp [h_i, DA.DetRun, da_concat_next_2, da_concat_det_run_1, h_n, get_drop', ← ne_none_iff_isSome]
    intro j h_j h_contra ; have := h_min h_contra ; fin_omega
  obtain ⟨i, h_i, _⟩ := h_ind
  let I := {j | ((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 j = some (M2.DetRun (as <<< n) (k + 1))}
  have h_fin : I.Finite := by exact toFinite I
  have h_ne : I.Nonempty := by use i ; simp [I, h_i]
  obtain ⟨j, h_j, h_min⟩ := Finite.exists_minimal h_fin h_ne
  simp [I] at h_j h_min
  use j
  simp [h_j, ← add_assoc]
  rw [DA.DetRun]
  simp [da_concat_next_2, h_j]
  have h_min' : ∀ j' < j, ¬((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 j' = some (M2.DetRun (as <<< n) (k + 1)) := by
    intro j' h_j' h_contra ; have := h_min h_contra ; fin_omega
  constructorm* _ ∧ _
  · grind
  · simp [DA.DetRun, get_drop', (show n + (k + 1) = n + k + 1 by omega)]
  · grind

/-- Use the `choose` function to pick out the `i` that is asserted to exist
in the previous theorem.
-/
noncomputable def DA.ConcatPtr2 (as : ℕ → A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1) (k : ℕ) : Fin (Nat.card M2.State + 2) :=
  choose (da_concat_ptr2_exists M1 acc1 M2 as n h_n k)

/-- `DA.ConcatPtr2` always point to an active `M2` copy whose state is consistent with
its being activated at step `n`.
-/
theorem da_concat_ptr2_det_run (as : ℕ → A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1) (k : ℕ) :
    ((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 (DA.ConcatPtr2 M1 acc1 M2 as n h_n k) =
    some (M2.DetRun (as <<< n) (k + 1)) := by
  exact (choose_spec (da_concat_ptr2_exists M1 acc1 M2 as n h_n k)).1

/-- The value of `DA.ConcatPtr2` is a non-increasing over time.
-/
theorem da_concat_ptr2_antitone (as : ℕ → A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1):
    Antitone (DA.ConcatPtr2 M1 acc1 M2 as n h_n) := by
  apply antitone_nat_of_succ_le ; intro k
  have h_spec_k1 := choose_spec (da_concat_ptr2_exists M1 acc1 M2 as n h_n (k + 1))
  have h_def_k1 : M1.ConcatPtr2 acc1 M2 as n h_n (k + 1) = choose (da_concat_ptr2_exists M1 acc1 M2 as n h_n (k + 1)) := rfl
  simp [← h_def_k1, ← add_assoc] at h_spec_k1
  obtain ⟨_, h_eq1, h_min⟩ := h_spec_k1
  by_contra! h_contra
  have h_eq2 := h_min (M1.ConcatPtr2 acc1 M2 as n h_n k) (by fin_omega)
  simp [da_concat_ptr2_det_run, h_eq1] at h_eq2

/-- Thus `DA.ConcatPtr2` must stabilize at some value `i` from some time `m` onward.
-/
theorem da_concat_ptr2_eventually (as : ℕ → A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1):
    ∃ i : Fin (Nat.card M2.State + 2), ∃ m > n, ∀ k ≥ m, DA.ConcatPtr2 M1 acc1 M2 as n h_n (k - n - 1) = i := by
  obtain ⟨i, m, h_i⟩ := antitone_fin_eventually <| da_concat_ptr2_antitone M1 acc1 M2 as n h_n
  use i, (m + n + 1) ; simp [show m + n + 1 > n by omega]
  intro k h_k ; exact h_i (k - n - 1) (by omega)

variable [Finite M1.State]

/-- The results that follow depend on both `M1` and `M2` and hence `M1.Concat acc1 M2` being finite-state.
-/
instance : Finite ((M1.Concat acc1 M2).State) := by apply Finite.instProd

variable (accSet2 : Set (Set M2.State))

/-- The Muller accepting condition of `M1.Concat acc1 M2`.
-/
def DA.MullerAcc_Concat : Set (Set (M1.Concat acc1 M2).State) :=
  { acc | ∃ i, {s2 | ∃ s ∈ acc, s.2 i = some s2} ∈ accSet2 ∧ (∀ s ∈ acc, (s.2 i).isSome) }

/-- Any infinite word consisting of a finite word accepted by `M1` followed by
an infinite word accepted by `M2` under the Muller condition is accepted by
`M1.Concat acc1 M2` under the Muller condition
-/
theorem da_concat_to_muller_accept (as : ℕ → A) (n : ℕ)
    (h1 : M1.toNA.FinAccept acc1 n as) (h2 : M2.MullerAccept accSet2 (as <<< n)) :
    (M1.Concat acc1 M2).MullerAccept (DA.MullerAcc_Concat M1 acc1 M2 accSet2) as := by
  obtain ⟨ss, h_run1, h_acc1⟩ := h1
  rw [da_fin_run_unique h_run1 n (by omega)] at h_acc1
  obtain ⟨i, m, h_m, h_i⟩ := da_concat_ptr2_eventually M1 acc1 M2 as n h_acc1
  have h_suffix : ∀ k ≥ m, ((M1.Concat acc1 M2).DetRun as k).2 i = some (M2.DetRun (as <<< n) (k - n)) := by
    intro k h_k
    have h_p := da_concat_ptr2_det_run M1 acc1 M2 as n h_acc1 (k - n - 1)
    simp [h_i k h_k, (show n + (k - n - 1) + 1 = k by omega), (show k - n - 1 + 1 = k - n by omega)] at h_p
    exact h_p
  use i ; constructor
  · suffices h_inf : {s2 | ∃ s ∈ InfOcc ((M1.Concat acc1 M2).DetRun as), s.2 i = some s2} = InfOcc (M2.DetRun (as <<< n)) by
      simpa [h_inf]
    ext s2 ; constructor
    · rintro ⟨s, h_inf, h_s⟩
      apply frequently_atTop.mpr ; intro l
      obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (m + l)
      simp [h_suffix k (by omega)] at h_s
      use (k - n) ; simp [h_s] ; omega
    · intro h_inf
      obtain ⟨l, h_l⟩ := eventually_atTop.mp <| inf_occ_eventually ((M1.Concat acc1 M2).DetRun as)
      obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (l + m - n)
      use ((M1.Concat acc1 M2).DetRun as (k + n)) ; constructor
      · exact h_l (k + n) (by omega)
      · simp [h_suffix (k + n) (by omega)]
  · intro s h_s
    obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_s m
    simp [h_suffix k h_k]

/-- Any infinite word accepted by `M1.Concat acc1 M2` under the Muller condition
consists of a finite word accepted by `M1` followed by an infinite word accepted
by `M2` under the Muller condition.
-/
theorem da_concat_of_muller_accept (as : ℕ → A)
    (h : (M1.Concat acc1 M2).MullerAccept (DA.MullerAcc_Concat M1 acc1 M2 accSet2) as) :
    ∃ n, M1.toNA.FinAccept acc1 n as ∧ M2.MullerAccept accSet2 (as <<< n) := by
  obtain ⟨i, h_acc2, h_some⟩ := h
  obtain ⟨n, h_n⟩ := eventually_atTop.mp <| inf_occ_eventually ((M1.Concat acc1 M2).DetRun as)
  have h_eventl : ∀ k ≥ n, (((M1.Concat acc1 M2).DetRun as k).2 i).isSome := by
    intro k h_k ; exact h_some ((M1.Concat acc1 M2).DetRun as k) <| h_n k h_k
  obtain ⟨m, h_m, h_acc1, h_suffix⟩ := da_concat_det_run_2 M1 acc1 M2 as n i h_eventl
  suffices h_inf : {s2 | ∃ s ∈ InfOcc ((M1.Concat acc1 M2).DetRun as), s.2 i = some s2} = InfOcc (M2.DetRun (as <<< m)) by
    use m ; constructor
    · use M1.DetRun as ; simp [h_acc1]
      exact da_fin_run_exists m as
    · rw [h_inf] at h_acc2
      exact h_acc2
  ext s2 ; constructor
  · rintro ⟨s, h_inf, h_s⟩
    apply frequently_atTop.mpr ; intro l
    obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (m + l + 1)
    simp [h_suffix k (by omega)] at h_s
    use (k - m) ; simp [h_s] ; omega
  · intro h_inf
    obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (n - m)
    use ((M1.Concat acc1 M2).DetRun as (k + m)) ; constructor
    · exact h_n (k + m) (by omega)
    · simp [h_suffix (k + m) (by omega)]

end AutomataDetConcat
