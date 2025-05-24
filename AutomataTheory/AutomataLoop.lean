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
    ∃ n > 0, ∃ φ : ℕ → ℕ, Monotone φ ∧ φ 0 = 0 ∧ φ n = m ∧
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
        exact Nat.findGreatest_spec (show k ≤ m - 1 by omega) h_k
      have h_next' := h_run.2 m' h_m'
      simp [AutomataLoop, h_notM'] at h_next'
      obtain ⟨h_acc', s0, h_s0_init, h_s0_next⟩ := h_next'
      have h_accept : FinAccept M acc (m - m') (SuffixFrom m' as) := by
        use (fun k ↦ if k = 0 then s0 else ss (k + m'))
        constructor <;> [constructor ; skip]
        · simpa
        · intro k h_k
          rcases Classical.em (k = 0) with h_k' | h_k'
          · simpa [SuffixFrom, h_k', (show 1 + m' = m' + 1 by omega)]
          · have h_next : ss (k + m' + 1) ∈ M.next (ss (k + m')) (as (k + m')) := by
              have h0 := Nat.findGreatest_is_greatest (show m' < k + m' by omega) (by omega)
              simp [loop, (show k + m' < m by omega)] at h0
              exact h0
            simpa [SuffixFrom, h_k', (show k + 1 + m' = k + m' + 1 by omega)]
        · simpa [(show m - m' ≠ 0 by omega), (show m - m' + m' = m by omega)]
      have h_run' : FinRun (AutomataLoop M acc) m' as ss := by
        constructor
        · exact h_run.1
        intro k h_k ; exact h_run.2 k (by omega)
      obtain ⟨n', h_n', φ', h_mono', h_φ'_0, h_φ'_n', h_accept'⟩ := h_ind m' h_m' h_run' h_acc'
      use (n' + 1) ; simp [(show n' + 1 > 0 by omega)]
      use (fun k ↦ if k ≤ n' then φ' k else m)
      simp [h_φ'_0] ; constructor
      · apply monotone_nat_of_le_succ ; intro k
        rcases (show k < n' ∨ k = n' ∨ k > n' by omega) with h_k | h_k | h_k
        · simp [(show k ≤ n' by omega), (show k + 1 ≤ n' by omega)]
          exact h_mono' (show k ≤ k + 1 by omega)
        · simp [h_k, h_φ'_n'] ; omega
        · simp [(show ¬ k ≤ n' by omega), (show ¬ k + 1 ≤ n' by omega)]
      · intro k h_k
        rcases (show k < n' ∨ k = n' by omega) with h_k' | h_k'
        · simp [(show k ≤ n' by omega), (show k + 1 ≤ n' by omega)]
          exact h_accept' k h_k'
        · simpa [h_k', h_φ'_n']
    · simp [loop] at h_loop
      use 1 ; simp
      use (fun k ↦ if k = 0 then 0 else m)
      constructor
      · apply monotone_nat_of_le_succ ; intro k
        rcases (show k = 0 ∨ k ≠ 0 by omega) with h_k | h_k <;> simp [h_k]
      rcases (show m = 0 ∨ m ≠ 0 by omega) with h_0 | h_1
      · simp [h_0]
        use ss ; simp [h_0] at h_acc ; simp [h_acc]
        constructor
        · have h_init := h_run.1
          simp [AutomataLoop] at h_init
          exact h_init
        · simp
      · simp [h_1]
        use ss ; simp [h_acc]
        constructor
        · have h_init := h_run.1
          simp [AutomataLoop] at h_init
          exact h_init
        · exact h_loop
  · rintro ⟨n, h_n, φ, h_mono, h_φ_0, h_φ_n, h_accept⟩
    choose ss h_run h_acc using h_accept
    let locate j k := φ k ≤ j ∧ j ≤ φ (k + 1)
    have h_locate : ∀ j ≤ m, ∃ k ≤ n, locate j k := by
      intro j h_j
      let lb k := k ≤ n ∧ φ k ≤ j
      let k := Nat.findGreatest lb n
      obtain ⟨h_k, h_φ_k⟩ : k ≤ n ∧ φ k ≤ j := by
        have h_lb_0 : lb 0 := by simp [lb, h_φ_0]
        exact Nat.findGreatest_spec (show 0 ≤ n by omega) (h_lb_0)
      use k ; simp [locate, h_k, h_φ_k]
      have h0 := Nat.findGreatest_is_greatest (show k < k + 1 by omega)
      simp [lb] at h0
      rcases (show k < n ∨ k = n by omega) with h_k' | h_k'
      · omega
      · simp [h_k', h_φ_n] at h_φ_k
        simp [show j = m by omega, ← h_φ_n, h_k']
        exact h_mono (show n ≤ n + 1 by omega)
    choose! loc h_loc_n h_loc_lo h_loc_hi using h_locate
--    let ss' j := if h1 : j ≤ m then (if h2 : loc j < n then ss (loc j) h2 (j - loc j) else ss 0 (by omega) 0) else
    sorry

end AutomataLoop
