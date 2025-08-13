/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Det
import AutomataTheory.Languages.Basic

/-!
This file defines the concatenation construction for deterministic automata
and proves some properties about it.  This construction is inspired by
Choueka's "flag construction" in the following paper:

Choueka, Yaacov, "Theories of automata on ω-tapes: a simplified approach",
J. Comput. System Sci. 8 (1974) 117-141.

It can also be viewed as (not surprisingly) the combination of a
nondeterministic concatenation construction and a powerset construction.
-/

open Function Set Filter
open Classical

section AutomataDetConcat

variable {A : Type*}

/-- The concatenation automaton runs M0 in parallel with copies of M1, where
an M1 copy is started whenever M0 is in an accepting state.  The M1 copies
are distinguishable only by their states, so their combined state is just
a subset of M1.State.
-/
def DetAutomaton.Concat (M0 : DetAutomaton A) (acc0 : Set M0.State) (M1 : DetAutomaton A) : DetAutomaton A where
  State := M0.State × Set M1.State
  init := (M0.init, if M0.init ∈ acc0 then {M1.init} else ∅)
  next := fun s a ↦ (M0.next s.1 a, ((M1.next · a) '' s.2) ∪ if M0.next s.1 a ∈ acc0 then {M1.init} else ∅)

variable {M0 : DetAutomaton A} {acc0 : Set M0.State} {M1 : DetAutomaton A}

/-- The first component of the state of `M0.Concat acc0 M1` is the same
as M0 running alone.
-/
theorem det_automata_concat_inf_run_fst (as : ℕ → A) (k : ℕ) :
    ((M0.Concat acc0 M1).DetRun as k).1 = M0.DetRun as k := by
  induction' k with k h_ind <;> simp [DetAutomaton.DetRun]
  · simp [DetAutomaton.Concat]
  simp [← h_ind] ; rfl

/-- The second component of the state of `M0.Concat acc0 M1` is a set
of `M1` copies which have been started by M0 reaching an accepting state.
-/
theorem det_automata_concat_inf_run_snd (as : ℕ → A) (k : ℕ) :
    ((M0.Concat acc0 M1).DetRun as k).2 =
    {s1 | ∃ j ≤ k, M0.DetRun as j ∈ acc0 ∧ s1 = M1.DetRun (as <<< j) (k - j)} := by
  induction' k with k h_ind <;> simp [DetAutomaton.DetRun]
  · simp [DetAutomaton.Concat] ; ext s1 ; simp
  have h_ind' : (M0.Concat acc0 M1).DetRun as k =
      (M0.DetRun as k, {s1 | ∃ j ≤ k, M0.DetRun as j ∈ acc0 ∧ s1 = M1.DetRun (as <<< j) (k - j)}) := by
    rw [Prod.ext_iff] ; simp [h_ind, det_automata_concat_inf_run_fst]
  simp [h_ind'] ; ext s1
  rcases Classical.em (M0.next (M0.DetRun as k) (as k) ∈ acc0) with h_acc | h_acc <;>
  simp [DetAutomaton.Concat, h_acc]
  · constructor
    · rintro (rfl | ⟨s1', ⟨j, h_j_k, h_j_acc, rfl⟩, rfl⟩)
      · use (k + 1) ; simp [DetAutomaton.DetRun, h_acc]
      · use j
        simp [h_j_acc, (show j ≤ k + 1 by omega), (show k + 1 - j = k - j + 1 by omega),
          DetAutomaton.DetRun, sub_base_of_SuffixFrom h_j_k]
    · rintro ⟨j, h_j_k, h_j_acc, rfl⟩
      rcases (show j ≤ k ∨ j = k + 1 by omega) with h_j_k' | rfl
      · right ; use (M1.DetRun (as <<< j) (k - j))
        simp [(show k + 1 - j = k - j + 1 by omega), DetAutomaton.DetRun, sub_base_of_SuffixFrom h_j_k']
        use j
      · left ; simp [DetAutomaton.DetRun]
  · constructor
    · rintro ⟨s1', ⟨j, h_j_k, h_j_acc, rfl⟩, rfl⟩ ; use j
      simp [h_j_acc, (show j ≤ k + 1 by omega), (show k + 1 - j = k - j + 1 by omega),
        DetAutomaton.DetRun, sub_base_of_SuffixFrom h_j_k]
    · rintro ⟨j, h_j_k, h_j_acc, rfl⟩
      rcases (show j ≤ k ∨ j = k + 1 by omega) with h_j_k' | rfl
      . use (M1.DetRun (as <<< j) (k - j))
        simp [(show k + 1 - j = k - j + 1 by omega), DetAutomaton.DetRun, sub_base_of_SuffixFrom h_j_k']
        use j
      · simp [DetAutomaton.DetRun] at h_j_acc
        contradiction

end AutomataDetConcat
