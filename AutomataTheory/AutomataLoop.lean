/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib
-- import Mathlib.Algebra.Order.Ring.Nat
-- import Mathlib.Algebra.Order.Sub.Basic
import AutomataTheory.Languages
import AutomataTheory.AutomataBasic

open Function Set Sum Filter
open Classical

section AutomataLoop

variable {A : Type*}

def AutomataLoop (M : Automaton A) (acc : Set M.State) : Automaton A where
  State := Unit ⊕ M.State
  init := {inl ()}
  next := fun s a ↦ match (s) with
    | inl () => inr '' { s' | ∃ s0 ∈ M.init, s' ∈ M.next s0 a } ∪
                if ∃ s0 ∈ M.init, ∃ s' ∈ acc, s' ∈ M.next s0 a then {inl ()} else ∅
    | inr s  => inr '' (M.next s a) ∪
                if ∃ s' ∈ acc, s' ∈ M.next s a then {inl ()} else ∅

variable {M : Automaton A} {acc : Set M.State}

theorem automata_loop_fin_run_0 {as : ℕ → A} {ss : ℕ → (AutomataLoop M acc).State} :
    FinRun (AutomataLoop M acc) 0 as ss ∧ (∃ s0 ∈ M.init, s0 ∈ acc) ↔
    ∃ ss', FinRun M 0 as ss' ∧ ss' 0 ∈ acc ∧ ss 0 = inl () := by
  constructor
  · rintro ⟨⟨h_init, _⟩, s0, h_s0_init, h_s0_acc⟩
    simp [AutomataLoop] at h_init
    use (fun k ↦ s0)
    simp [FinRun, h_s0_init, h_s0_acc, h_init]
  · rintro ⟨ss', ⟨h_init, _⟩, h_acc, h_inl⟩
    simp [FinRun, AutomataLoop, h_inl]
    use (ss' 0)

theorem automata_loop_fin_run_1 {n : ℕ} {as : ℕ → A} {ss : ℕ → (AutomataLoop M acc).State} (h : n > 0) :
    FinRun (AutomataLoop M acc) n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k ∈ inr '' univ) ↔
    ∃ ss', FinRun M n as ss' ∧ ss' n ∈ acc ∧ ss 0 = inl () ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by
  constructor
  · rintro ⟨⟨h_init, h_next⟩, h_inl_n, h_inr⟩
    simp [AutomataLoop] at h_init
    rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
    · obtain ⟨rfl⟩ := h_n
      specialize h_next 0 (by omega)
      simp [h_init, h_inl_n, AutomataLoop] at h_next
      obtain ⟨s0, h_s0, s1, h_acc, h_next⟩ := h_next
      use (fun k ↦ if k = 0 then s0 else if k = 1 then s1 else s0)
      simp [h_init, h_acc, h_inl_n, FinRun, h_s0, h_next]
    · obtain ⟨s1, _, h_s1⟩ := h_inr 1 h_n (by omega)
      have h_next_0 := h_next 0 h
      simp [h_init, ← h_s1, AutomataLoop] at h_next_0
      obtain ⟨s0, h_s0, h_next_0⟩ := h_next_0
      obtain ⟨sn1, _, h_sn1⟩ := h_inr (n - 1) (by omega) (by omega)
      have h_next_n1 := h_next (n - 1) (by omega)
      have h_n1 : n - 1 + 1 = n := by omega
      simp [h_n1, h_inl_n, ← h_sn1, AutomataLoop] at h_next_n1
      obtain ⟨sn, h_sn, h_next_n1⟩ := h_next_n1
      have h_ss' : ∀ k, k > 0 → k < n → ∃ ss', ss k = inr ss' := by
        intro k h_k_0 h_k_n
        obtain ⟨s', _, h_s'⟩ := h_inr k h_k_n h_k_0
        use s' ; simp [h_s']
      choose ss' h_ss' using h_ss'
      use (fun k ↦ if h0 : k = 0 then s0 else if hn : k < n then ss' k (by omega) hn else if k = n then sn else s0)
      simp [(show n ≠ 0 by omega), h_init, h_inl_n, h_sn, FinRun, h_s0]
      constructor
      · intro k h_k_n
        rcases (show k = 0 ∨ k = n - 1 ∨ k > 0 ∧ k < n - 1 by omega) with h_k_0 | h_k_n' | ⟨h_k_0, h_k_n'⟩
        · obtain ⟨rfl⟩ := h_k_0
          have h_ss_1 := h_ss' 1 (by omega) (h_n)
          rw [← h_s1, inr.inj_iff] at h_ss_1
          simp [h_n, ← h_ss_1, h_next_0]
        · obtain ⟨rfl⟩ := h_k_n'
          have h_ss_n1 := h_ss' (n - 1) (by omega) h_k_n
          rw [← h_sn1, inr.inj_iff] at h_ss_n1
          simp [(show n - 1 + 1 = n by omega), (show n - 1 ≠ 0 by omega), h, ← h_ss_n1, h_next_n1]
        · have h_ss_k := h_ss' k h_k_0 h_k_n
          have h_ss_k1 := h_ss' (k + 1) (by omega) (by omega)
          have h_next_k := h_next k h_k_n
          simp [h_ss_k, h_ss_k1, AutomataLoop] at h_next_k
          simp [(show k + 1 < n by omega), (show k ≠ 0 by omega), h_k_n, h_next_k]
      · intro k h_k_n h_k_0
        simp [h_k_n, h_k_0, (show k ≠ 0 by omega), h_ss']
  · rintro ⟨ss', ⟨h_init, h_next⟩, h_acc, h_inl_0, h_inl_n, h_inr⟩
    constructor <;> [constructor ; constructor]
    · simp [h_inl_0, AutomataLoop]
    · intro k h_k_n
      rcases (show k = 0 ∨ k > 0 by omega) with h_k_0 | h_k_0
      · specialize h_next 0 h
        rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
        · obtain ⟨rfl⟩ := h_n
          simp [h_k_0, h_inl_0, AutomataLoop, h_inl_n]
          use (ss' 0) ; simp [h_init] ; use (ss' 1)
        · specialize h_inr 1 h_n (by omega)
          simp [h_k_0, h_inl_0, AutomataLoop, h_inr]
          use (ss' 0)
      · specialize h_next k (h_k_n)
        have h_ss_k := h_inr k h_k_n h_k_0
        rcases (show k + 1 < n ∨ k = n - 1 by omega) with h_k_n' | h_k_n'
        · have h_ss_k' := h_inr (k + 1) h_k_n' (by omega)
          simpa [h_ss_k, h_ss_k', AutomataLoop]
        · obtain ⟨rfl⟩ := h_k_n'
          have h_n1 : n - 1 + 1 = n := by omega
          simp [h_n1] at h_next
          simp [h_n1, h_ss_k, h_inl_n, AutomataLoop]
          use (ss' n)
    · exact h_inl_n
    · intro k h_k_n h_k_0
      simp [h_inr k h_k_n h_k_0]

end AutomataLoop

section AcceptedLangLoop

end AcceptedLangLoop

variable {A : Type*} {M : Automaton A} {acc : Set M.State}

theorem accepted_lang_loop :
    AcceptedLang (AutomataLoop M acc) {inl ()} = IterStar (AcceptedLang M acc) := by
  sorry

variable {X : Type*} {xs xs' : ℕ → X}

theorem ofFn_eq_ofFn {xs xs' : ℕ → X} {m n n' : ℕ}
    (h : List.ofFn (fun k : Fin n' ↦ xs' k) = List.ofFn (fun k : Fin (m - n) ↦ xs (k + n))) :
    n' = m - n ∧ ∀ k < m - n, xs' k = xs (k + m) := by
  sorry

theorem accepted_omega_lang_loop :
    AcceptedOmegaLang (AutomataLoop M acc) {inl ()} = IterOmega (AcceptedLang M acc) := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_acc⟩ ; simp at h_acc
    let φ m := Nat.nth (fun k ↦ ss k = inl ()) m
    have h_inf : {k | ss k = inl ()}.Infinite := by simpa [← Nat.frequently_atTop_iff_infinite]
    have h_mono : StrictMono φ := by exact Nat.nth_strictMono h_inf
    use φ ; simp [h_mono] ; constructor
    · have h_init := h_run.1
      simp [AutomataLoop] at h_init
      apply Nat.nth_zero_of_zero h_init
    · intro m
      use (φ (m + 1) - φ m), (SuffixFrom (φ m) as) ; constructor
      · have h_pos : φ (m + 1) - φ m > 0 := by have := h_mono (show m < m + 1 by omega) ; omega
        let ss1 := SuffixFrom (φ m) ss
        have h_run1 : FinRun (AutomataLoop M acc) (φ (m + 1) - φ m) (SuffixFrom (φ m) as) ss1 := by sorry
        have h_inl : ss1 (φ (m + 1) - φ m) = inl () := by
          simp [ss1, SuffixFrom, (show φ (m + 1) - φ m + φ m = φ (m + 1) by omega)]
          apply Nat.nth_mem_of_infinite (p := fun k ↦ ss k = inl ()) h_inf
        have h_inr : ∀ k < φ (m + 1) - φ m, k > 0 → ss1 k ∈ inr '' univ := by sorry
        obtain ⟨ss', h_run', h_acc', _⟩ := (automata_loop_fin_run_1 h_pos).mp ⟨h_run1, h_inl, h_inr⟩
        use ss'
      · rw [List.ofFn_inj] ; ext k
        simp [SuffixFrom]
  · rintro ⟨φ, h_mono, h_0, h_acc⟩
    choose len as' h_acc h_as' using h_acc
    choose ss' h_run h_acc using h_acc
    let ss k := if k ∈ φ '' univ then inl () else inr (ss' (Nat.count (φ '' univ) k) (k - φ (Nat.count (φ '' univ) k)))
    use ss

    -- have : ∀ m, len m = φ (m + 1) - φ m ∧ ∀ k < φ (m + 1) - φ m, as' m k = as (k + φ m) := by
    --   intro m
    --   have h_as' := List.ofFn_inj'.mp <| h_as' <| m
    --   simp at h_as'
    --   obtain ⟨h_len, h_as⟩ := h_as'
    --   rw [← h_len] at h_as ; simp at h_as
    --   simp [← h_len]
    --   intro k h_k
    --   obtain ⟨h1, h2⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp <| List.ofFn_inj'.mp <| h_as' m
    --   sorry

    sorry

section DeprecatedLoop

def AutomataLoop' (M : Automaton A) (acc : Set M.State) : Automaton A where
  State := M.State
  init := M.init
  next := fun s a ↦ M.next s a ∪ { s' | s ∈ acc ∧ ∃ s0 ∈ M.init, s' ∈ M.next s0 a }

variable {M : Automaton A} {acc : Set M.State}

theorem automata_loop_fin_accept {m : ℕ} {as : ℕ → A} :
    FinAccept (AutomataLoop' M acc) acc m as ↔
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
      simp [AutomataLoop', h_notM'] at h_next'
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
      have h_run' : FinRun (AutomataLoop' M acc) m' as ss := by
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
          simp [AutomataLoop'] at h_init
          exact h_init
        · simp
      · simp [h_1]
        use ss ; simp [h_acc]
        constructor
        · have h_init := h_run.1
          simp [AutomataLoop'] at h_init
          exact h_init
        · exact h_loop
  · rintro ⟨n, h_n, φ, h_mono, h_φ_0, h_φ_n, h_accept⟩
    revert m
    induction' n with n h_ind
    · omega
    rcases (show n = 0 ∨ n > 0 by omega) with h_n' | h_n'
    · simp [h_n', h_φ_0] at h_accept
      obtain ⟨ss, h_run, h_acc⟩ := h_accept
      simp [h_n'] ; use ss ; simp [h_acc] ; constructor
      · exact h_run.1
      intro k h_k
      have h_next := h_run.2 k h_k
      simp [SuffixFrom] at h_next
      simp [AutomataLoop', h_next]
    · have h_mono' : φ n ≤ φ (n + 1) := by apply h_mono ; omega
      have h_accept0 : (∀ k < n, FinAccept M acc (φ (k + 1) - φ k) (SuffixFrom (φ k) as)) := by
        intro k h_k ; exact h_accept k (by omega)
      obtain ⟨ss0, h_run0, h_acc0⟩ := h_ind h_n' h_accept0 (rfl)
      obtain ⟨ss1, h_run1, h_acc1⟩ := h_accept n (by omega)
      intro m h_m ; rw [← h_m]
      use (fun k ↦ if k ≤ φ n then ss0 k else ss1 (k - φ n)) ; constructor
      · constructor
        · have h_init := h_run0.1
          simp [h_init]
        intro k h_k
        rcases (show k < φ n ∨ k = φ n ∨ k > φ n by omega) with h_k' | h_k' | h_k'
        · have h_next := h_run0.2 k h_k'
          simpa [(show k ≤ φ n by omega), (show k + 1 ≤ φ n by omega)]
        · simp [AutomataLoop', h_k', h_acc0] ; right ; use (ss1 0)
          have h_init := h_run1.1
          have h_next := h_run1.2 0 (by omega)
          simp [SuffixFrom] at h_next
          simp [h_init, h_next]
        · have h_next := h_run1.2 (k - φ n) (by omega)
          simp [SuffixFrom, (show k - φ n + φ n = k by omega),
                (show k - φ n + 1 = k + 1 - φ n by omega)] at h_next
          simp [AutomataLoop', h_next,
                (show ¬ k ≤ φ n by omega), (show ¬ k + 1 ≤ φ n by omega)]
      · rcases Classical.em (φ (n + 1) ≤ φ n) with h_φ_n | h_φ_n
        · have h_eq : φ (n + 1) = φ n := by omega
          simpa [h_φ_n, h_eq]
        · simpa [h_φ_n]

end DeprecatedLoop
