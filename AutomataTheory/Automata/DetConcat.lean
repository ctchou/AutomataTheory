/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Det
import AutomataTheory.Languages.Basic

/-!
This file defines a concatenation construction for deterministic automata
based on the "flag construction" described in the following paper:

Choueka, Yaacov, "Theories of automata on ω-tapes: a simplified approach",
J. Comput. System Sci. 8 (1974) 117-141.
-/

open Function Set Filter
open Classical

section AutomataDetConcat

variable {A : Type} (M1 : DetAutomaton A) (acc1 : Set M1.State) (M2 : DetAutomaton A)

/-- The concatenation automaton runs M1 in parallel with at most n2 + 2 copies
of M2, where n2 is the number of states of M2.  (So this construction only
makes sense when M2 is finite-state.)  An new M2 copy is activated whenever M1
reaches an accepting state and for any M2 copies in the same state, only the one
with the lowest index is kept and all other copies are deactivated in the next step.
The reason is have n2 + 2 copies is to ensure that an empty slot can always be found
for a new copy of M2, because it is possible to have two M2 copies to be in the same
state at the same time.  (The maximum possible number of active copies is n2 + 1.)
Note that we never need to activate and deactivate the same copy at the same time.
-/
noncomputable def DetAutomaton.Concat : DetAutomaton A where
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

theorem det_automata_concat_next_2 (s : (M1.Concat acc1 M2).State) (a : A) (i : Fin (Nat.card M2.State + 2)) :
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

/-- The first component of the state of `M1.Concat acc1 M2` is the same
as M1 running alone.
-/
theorem det_automata_concat_inf_run_1 (as : ℕ → A) (k : ℕ) :
    ((M1.Concat acc1 M2).DetRun as k).1 = M1.DetRun as k := by
  induction' k with k h_ind <;> simp [DetAutomaton.DetRun]
  · rfl
  simp [← h_ind] ; rfl

/-- The second component of the state of `M1.Concat acc1 M2` is a set
of `M2` copies which have been started by M1 reaching an accepting state.
-/
theorem det_automata_concat_inf_run_2 (as : ℕ → A) (k : ℕ) (i : Fin (Nat.card M2.State + 2)) :
    ∀ s2 : M2.State, ((M1.Concat acc1 M2).DetRun as k).2 i = some s2 →
    ∃ j < k, M1.DetRun as j ∈ acc1 ∧ M2.DetRun (as <<< j) (k - j) = s2 := by
  induction' k with k h_ind <;> intro s2 h
  · contradiction
  have h_next := det_automata_concat_next_2 M1 acc1 M2 ((M1.Concat acc1 M2).DetRun as k) (as k) i
  rcases Option.eq_none_or_eq_some <| ((M1.Concat acc1 M2).DetRun as k).2 i with h_k | ⟨s2', h_k⟩
  · simp [DetAutomaton.DetRun, h_next, h_k, det_automata_concat_inf_run_1] at h
    use k ; simp [h.1.1, ← h.2, DetAutomaton.DetRun, instSuffixFrom, SuffixFrom]
  · obtain ⟨j, h_j, h_acc, h_run⟩ := h_ind s2' h_k
    simp [DetAutomaton.DetRun, h_next, h_k] at h
    use j ; simp [h_acc, ← h.2, DetAutomaton.DetRun, h_run,
      (show j < k + 1 by omega), (show k + 1 - j = k - j + 1 by omega)]
    congr ; simp [instSuffixFrom, SuffixFrom, (show k - j + j = k by omega)]

variable (accSet2 : Set (Set M2.State))

def DetAutomaton.MullerAcc_Concat : Set (Set (M1.Concat acc1 M2).State) :=
  { acc | ∃ i, {s2 | ∃ s ∈ acc, s.2 i = some s2} ∈ accSet2 ∧ (∀ s ∈ acc, (s.2 i).isSome) }

theorem det_automata_concat_muller_accept (as : ℕ → A)
    (h : (M1.Concat acc1 M2).MullerAccept (DetAutomaton.MullerAcc_Concat M1 acc1 M2 accSet2) as) :
    ∃ k, M1.toNA.FinAccept acc1 k as ∧ M2.MullerAccept accSet2 (as <<< k) := by
  sorry

end AutomataDetConcat
