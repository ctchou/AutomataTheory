/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib
import AutomataTheory.Languages
import AutomataTheory.AutomataBasic

open Function Set Filter
open Classical

section AutomataLoop

variable {A : Type*}

def AutomataLoop (M : Automaton A) (acc : Set M.State) : Automaton A where
  State := M.State
  init := M.init
  next := fun s a ↦ M.next s a ∪ { s' | s ∈ acc ∧ ∃ s0 ∈ M.init, s' ∈ M.next s0 a }

variable {M : Automaton A} {acc : Set M.State}

theorem automata_loop_fin_run_1 {m : ℕ} {as : ℕ → A} {ss : ℕ → (AutomataLoop M acc).State}
    (h_pos : m > 0) (h_run : FinRun (AutomataLoop M acc) m as ss) : ∃ s0 ∈ M.init, ss 1 ∈ M.next s0 (as 0) := by
  rcases Classical.em (ss 1 ∈ M.next (ss 0) (as 0)) with h_case | h_case
  · use (ss 0)
    have h_init := h_run.1
    simp [AutomataLoop] at h_init
    simpa [h_case]
  · have h_next := h_run.2 0
    simp [AutomataLoop, h_pos, h_case] at h_next
    exact h_next.2

theorem automata_loop_fin_run {m : ℕ} {as : ℕ → A} {ss : ℕ → (AutomataLoop M acc).State} :
    FinRun (AutomataLoop M acc) m as ss ∧ ss m ∈ acc ↔
    ∃ φ : ℕ → ℕ, ∃ n : ℕ, Monotone φ ∧ φ 0 = 0 ∧ φ n = m ∧
      ∀ k < n, ∃ ss_k, FinRun M (φ (k + 1) - φ k) (SuffixFrom (φ k) as) ss_k ∧ ss_k (φ (k + 1) - φ k) ∈ acc := by
  constructor
  · rintro ⟨h_run, h_acc⟩
    induction' m using Nat.strong_induction_on with m h_ind
    rcases Classical.em (∃ k < m, k > 0 ∧ ss (k + 1) ∉ M.next (ss k) (as k)) with h_loop | h_loop
    · obtain ⟨h_n, h_n_pos, h_n_notM⟩ := Nat.find_spec h_loop
      -- have h_run' : FinRun M (Nat.find h_loop) as ss := by
      --   constructor
      --   · exact h_run.1
      --   intro k h_k
      --   have h_min := Nat.find_min h_loop h_k
      --   simp [(by omega : k < m)] at h_min
      --   exact h_min
      have h_next_n := h_run.2 (Nat.find h_loop) h_n
      simp [AutomataLoop, h_n_notM] at h_next_n
      obtain ⟨h_acc', s0, h_s0_init, h_s0_next⟩ := h_next_n
      sorry
    · simp at h_loop
      use (fun k ↦ if k = 0 then 0 else m), 1
      simp ; constructor
      · apply monotone_nat_of_le_succ ; intro k
        rcases Nat.eq_zero_or_eq_succ_pred k with h_k | h_k <;> rw [h_k] <;> simp
      · rcases Nat.eq_zero_or_pos m with h_m | h_m
        · use ss
          simp [FinRun, h_m]
          exact h_run.1
        · obtain ⟨s0, h_s0_init, h_s0_next⟩ := automata_loop_fin_run_1 h_m h_run
          use (fun k ↦ if k = 0 then s0 else ss k)
          constructor
          · simpa
          intro k h_k_m
          rcases Nat.eq_zero_or_pos k with h_k | h_k
          · simpa [h_k]
          · have h_k' : k ≠ 0 := by omega
            simp [h_k']
            exact h_loop k h_k_m h_k
  · sorry

end AutomataLoop
