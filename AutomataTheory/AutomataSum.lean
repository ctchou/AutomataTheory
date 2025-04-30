/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Sigma.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import AutomataTheory.AutomataBasic

open BigOperators Function Set Filter Sigma

section AutomataSum

variable {I A : Type*}

def AutomataSum (M : I → Automata A) : Automata A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a

variable (M : I → Automata A)

theorem automata_sum_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → (AutomataSum M).State) :
    FinRun (AutomataSum M) n as ss ↔ ∃ i ss_i, FinRun (M i) n as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [AutomataSum, Automata.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k : Fin (n + 1), ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k using Fin.induction with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp [AutomataSum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, Automata.init] at h_init
        simp [AutomataSum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomataSum] at h_next_k
        simpa
    · ext k ; rw [h_ss_i k] ; simp
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, AutomataSum]
    constructor
    · simp [Automata.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automata.next]
      have h_k := h_run.2 k
      simp at h_k
      exact h_k

theorem automata_sum_inf_run (as : ℕ → A) (ss : ℕ → (AutomataSum M).State) :
    InfRun (AutomataSum M) as ss ↔ ∃ i ss_i, InfRun (M i) as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [AutomataSum, Automata.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k, ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp [AutomataSum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, Automata.init] at h_init
        simp [AutomataSum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomataSum] at h_next_k
        assumption
    · ext k ; rw [h_ss_i k] ; simp
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, AutomataSum]
    constructor
    · simp [Automata.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automata.next]
      exact h_run.2 k

end AutomataSum

section AcceptedLangUnion

variable {I A : Type*} (M : I → Automata A) (acc : (i : I) → Set ((M i).State))

def AutomataSum_Acc : Set (AutomataSum M).State := ⋃ i : I, Sigma.mk i '' acc i

theorem accepted_lang_union :
    AcceptedLang (AutomataSum M) (AutomataSum_Acc M acc) = ⋃ i : I, AcceptedLang (M i) (acc i) := by
  ext al ; simp [AutomataSum_Acc, AcceptedLang, FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (automata_sum_fin_run M n as ss).mp h_run
    use i, n, as
    constructor
    · use ss_i
      constructor
      · assumption
      obtain ⟨i', si', h_si', h_last⟩ := h_acc
      simp [h_ss_i] at h_last
      rw [Sigma.mk.inj_iff] at h_last
      obtain ⟨rfl, h_si'_eq⟩ := h_last
      rw [heq_eq_eq] at h_si'_eq
      simpa [← h_si'_eq]
    · assumption
  · rintro ⟨i, n, as, ⟨ss_i, h_run, h_last⟩, h_al⟩
    use n, as
    constructor
    · use ((Sigma.mk i) ∘ ss_i)
      constructor
      · apply (automata_sum_fin_run M n as ((Sigma.mk i) ∘ ss_i)).mpr
        use i, ss_i
      · use i, ss_i (Fin.last n)
        simpa
    · assumption

theorem accepted_omega_lang_union :
    AcceptedOmegaLang (AutomataSum M) (AutomataSum_Acc M acc) = ⋃ i : I, AcceptedOmegaLang (M i) (acc i) := by
  ext as ; simp [AutomataSum_Acc, AcceptedOmegaLang, BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (automata_sum_inf_run M as ss).mp h_run
    use i, ss_i
    constructor
    · assumption
    · let p k := ∃ i', ∃ si' ∈ acc i', ⟨i', si'⟩ = ss k
      let q k := ss_i k ∈ acc i
      have h_p : ∃ᶠ k in atTop, p k := by assumption
      have h_pq : ∀ k, p k → q k := by
        rintro k ⟨i', si', h_si'_acc, h_si'_ss⟩
        simp [h_ss_i] at h_si'_ss
        rw [Sigma.mk.inj_iff] at h_si'_ss
        obtain ⟨rfl, h_si'_eq⟩ := h_si'_ss
        rw [heq_eq_eq] at h_si'_eq
        simpa [q, ← h_si'_eq]
      exact Frequently.mono h_p h_pq
  · rintro ⟨i, ss_i, h_run_i, h_inf_i⟩
    use ((Sigma.mk i) ∘ ss_i)
    constructor
    · apply (automata_sum_inf_run M as ((Sigma.mk i) ∘ ss_i)).mpr
      use i, ss_i
    · let p k := ss_i k ∈ acc i
      let q k := ∃ i', ∃ si' ∈ acc i', ⟨i', si'⟩ = ((Sigma.mk i ∘ ss_i) k : (AutomataSum M).State)
      have h_p : ∃ᶠ k in atTop, p k := by assumption
      have h_pq : ∀ k, p k → q k := by
        simp [p, q] ; intro k h
        use i, (ss_i k)
      exact Frequently.mono h_p h_pq

end  AcceptedLangUnion
