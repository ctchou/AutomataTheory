/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Basic

/-!
The indexed sum of automata, which is used to prove the closure of
both regular and ω-regular langauges under union.
Note that the theorems in this file are true even when the alphabet,
state, or index types are infinite.
-/

open Function Set Filter

section AutomataSum

variable {I A : Type*}

def Automaton.Sum (M : I → Automaton A) : Automaton A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a

variable {M : I → Automaton A}

theorem automata_sum_fin_run {n : ℕ} {as : ℕ → A} {ss : ℕ → (Automaton.Sum M).State} :
    (Automaton.Sum M).FinRun n as ss ↔ ∃ i ss_i, (M i).FinRun n as ss_i ∧ ∀ k < n + 1, ss k = ⟨i, ss_i k⟩ := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [Automaton.Sum, Automaton.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k < n + 1, ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k h_n ; induction' k with k h_k
      · use s0 ; simp [h_s0_ss]
      obtain ⟨sk, h_sk⟩ := h_k (by omega : k < n + 1)
      have h_next_k := h_next k
      simp [Automaton.Sum, h_sk] at h_next_k
      obtain ⟨sk', h_sk'⟩ := h_next_k (by omega : k < n)
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, (fun k ↦ if h : k < n + 1 then ss_i k h else ss_i 0 (by omega))
    constructor
    · constructor
      · simp [h_ss_i 0 (by omega : 0 < n + 1)] at h_init
        simp [Automaton.Sum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        simp [h_eq] at h_s'
        simpa
      · intro k h_k
        have h_next_k := h_next k h_k
        rw [h_ss_i k (by omega : k < n + 1), h_ss_i (k + 1) (by omega : k + 1 < n + 1)] at h_next_k
        simp [Automaton.Sum] at h_next_k
        simpa [h_k, (by omega : k < n + 1)]
    · intro k h_k
      simp [h_k, h_ss_i k h_k]
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    constructor
    · simp [Automaton.Sum, h_ss 0 (by omega : 0 < n + 1)]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k h_k
      have h_run_k := h_run.2 k h_k
      simpa [Automaton.Sum, h_ss k (by omega : k < n + 1), h_ss (k + 1) (by omega : k + 1 < n + 1)]

theorem automata_sum_inf_run {as : ℕ → A} {ss : ℕ → (Automaton.Sum M).State} :
    (Automaton.Sum M).InfRun as ss ↔ ∃ i ss_i, (M i).InfRun as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [Automaton.Sum, Automaton.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k, ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp [Automaton.Sum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, Automaton.init] at h_init
        simp [Automaton.Sum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [Automaton.Sum] at h_next_k
        assumption
    · ext k ; rw [h_ss_i k] ; simp
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, Automaton.Sum]
    constructor
    · simp [Automaton.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automaton.next]
      exact h_run.2 k

end AutomataSum

section AcceptedLangUnion

variable {I A : Type*} (M : I → Automaton A) (acc : (i : I) → Set ((M i).State))

def Automaton.Sum_Acc : Set (Automaton.Sum M).State := ⋃ i : I, Sigma.mk i '' acc i

/-- The language accepted by the sum automaton is the union of the languages
accepted by the component automata.
-/
theorem accepted_lang_union :
    (Automaton.Sum M).AcceptedLang (Automaton.Sum_Acc M acc) = ⋃ i : I, (M i).AcceptedLang (acc i) := by
  ext al ; simp [Automaton.Sum_Acc, Automaton.AcceptedLang, Automaton.FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := automata_sum_fin_run.mp h_run
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
      · apply automata_sum_fin_run.mpr
        use i, ss_i
        simp [h_run]
      · use i, ss_i (Fin.last n)
        simpa
    · assumption

/-- The ω-language accepted by the sum automaton is the union of the ω-languages
accepted by the component automata.
-/
theorem accepted_omega_lang_union :
    (Automaton.Sum M).AcceptedOmegaLang (Automaton.Sum_Acc M acc) = ⋃ i : I, (M i).AcceptedOmegaLang (acc i) := by
  ext as ; simp [Automaton.Sum_Acc, Automaton.AcceptedOmegaLang, Automaton.BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := automata_sum_inf_run.mp h_run
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
    · apply automata_sum_inf_run.mpr
      use i, ss_i
    · let p k := ss_i k ∈ acc i
      let q k := ∃ i', ∃ si' ∈ acc i', ⟨i', si'⟩ = ((Sigma.mk i ∘ ss_i) k : (Automaton.Sum M).State)
      have h_p : ∃ᶠ k in atTop, p k := by assumption
      have h_pq : ∀ k, p k → q k := by
        simp [p, q] ; intro k h
        use i, (ss_i k)
      exact Frequently.mono h_p h_pq

end  AcceptedLangUnion
