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

theorem automata_loop_fin_accept {m : ℕ} {as : ℕ → A} :
    FinAccept (AutomataLoop M acc) acc m as ↔
    ∃ n : ℕ, ∃ φ : ℕ → ℕ, Monotone φ ∧ φ 0 = 0 ∧ φ n = m ∧
      ∀ k < n, FinAccept M acc (φ (k + 1) - φ k) (SuffixFrom (φ k) as) := by
  constructor
  · rintro ⟨ss, h_run, h_acc⟩
    induction' m using Nat.strong_induction_on with m h_ind
    let loop k := k < m ∧ ss (k + 1) ∉ M.next (ss k) (as k)
    rcases Classical.em (∃ k, loop k) with h_loop | h_loop
    · have h_m : 0 < m := by omega
      let m' := Nat.findGreatest loop (m - 1)
      obtain ⟨h_m', h_notM'⟩ : m' < m ∧ ss (m' + 1) ∉ M.next (ss m') (as m') := by
        obtain ⟨k, h_k⟩ := h_loop
        exact Nat.findGreatest_spec (by omega : k ≤ m - 1) h_k
      have h_next' := h_run.2 m' h_m'
      simp [AutomataLoop, h_notM'] at h_next'
      obtain ⟨h_acc', s0, h_s0_init, h_s0_next⟩ := h_next'
      have h_accept : FinAccept M acc (m - m') (SuffixFrom m' as) := by
        use (fun k ↦ if k = 0 then s0 else ss (k + m'))
        constructor <;> [constructor ; skip]
        · simpa
        · intro k h_k
          rcases Classical.em (k = 0) with h_k' | h_k'
          · have h0 : 1 + m' = m' + 1 := by omega
            simpa [SuffixFrom, h_k', h0]
          · have h_next : ss (k + m' + 1) ∈ M.next (ss (k + m')) (as (k + m')) := by
              have h0 := Nat.findGreatest_is_greatest (by omega : m' < k + m') (by omega)
              simp [loop, (by omega : k + m' < m)] at h0
              exact h0
            have h1 : k + 1 + m' = k + m' + 1 := by omega
            simpa [SuffixFrom, h_k', h1]
        · have h0 : m - m' ≠ 0 := by omega
          have h1 : m - m' + m' = m := by omega
          simpa [h0, h1]
      have h_run' : FinRun (AutomataLoop M acc) m' as ss := by
        sorry
      sorry
    · simp [loop] at h_loop
      sorry

    -- rcases Classical.em (∃ k < m, k > 0 ∧ ss (k + 1) ∉ M.next (ss k) (as k)) with h_loop | h_loop
    -- · obtain ⟨h_n, h_n_pos, h_n_notM⟩ := Nat.find_spec h_loop
    --   -- have h_run' : FinRun M (Nat.find h_loop) as ss := by
    --   --   constructor
    --   --   · exact h_run.1
    --   --   intro k h_k
    --   --   have h_min := Nat.find_min h_loop h_k
    --   --   simp [(by omega : k < m)] at h_min
    --   --   exact h_min
    --   have h_next_n := h_run.2 (Nat.find h_loop) h_n
    --   simp [AutomataLoop, h_n_notM] at h_next_n
    --   obtain ⟨h_acc', s0, h_s0_init, h_s0_next⟩ := h_next_n
    --   sorry
    -- · simp at h_loop
    --   use (fun k ↦ if k = 0 then 0 else m), 1
    --   simp ; constructor
    --   · apply monotone_nat_of_le_succ ; intro k
    --     rcases Nat.eq_zero_or_eq_succ_pred k with h_k | h_k <;> rw [h_k] <;> simp
    --   · rcases Nat.eq_zero_or_pos m with h_m | h_m
    --     · use ss
    --       simp [FinRun, h_m]
    --       exact h_run.1
    --     · obtain ⟨s0, h_s0_init, h_s0_next⟩ := automata_loop_fin_run_1 h_m h_run
    --       use (fun k ↦ if k = 0 then s0 else ss k)
    --       constructor
    --       · simpa
    --       intro k h_k_m
    --       rcases Nat.eq_zero_or_pos k with h_k | h_k
    --       · simpa [h_k]
    --       · have h_k' : k ≠ 0 := by omega
    --         simp [h_k']
    --         exact h_loop k h_k_m h_k

  · sorry

end AutomataLoop
