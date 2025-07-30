/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Basic

/-!
The deterministic automaton class DetAutomaton is identical to the Automaton class,
except that its initial and next states are unique.
-/

open Function Set Filter

section DetAutomata

class DetAutomaton (A : Type*) where
  State : Type*
  init : State
  next : State → A → State

variable {A : Type*}

def DetAutomaton.toND (M : DetAutomaton A) : Automaton A where
  State := M.State
  init := {M.init}
  next := fun s a ↦ {M.next s a}

def MakeDetRun (M : DetAutomaton A) (as : ℕ → A) : ℕ → M.State
  | 0 => M.init
  | k + 1 => M.next (MakeDetRun M as k) (as k)

variable {M : DetAutomaton A}

theorem det_automata_inf_run_exists (as : ℕ → A) :
    M.toND.InfRun as (MakeDetRun M as) := by
  constructor <;> simp [DetAutomaton.toND, MakeDetRun]

theorem det_automata_inf_run_unique {as : ℕ → A} {ss : ℕ → M.State}
    (h : M.toND.InfRun as ss) : ss = MakeDetRun M as := by
  ext k ; induction' k with k h_ind
  · have h_init := h.1
    simp [DetAutomaton.toND] at h_init
    assumption
  · rw [MakeDetRun, ← h_ind]
    have h_next := h.2 k
    simp [DetAutomaton.toND] at h_next
    assumption

theorem det_automata_fin_run_exists (n : ℕ) (as : ℕ → A) :
    M.toND.FinRun n as (MakeDetRun M as) := by
  exact automata_InfRun_iff_FinRun.mp (det_automata_inf_run_exists as) n

theorem det_automata_fin_run_unique {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : M.toND.FinRun n as ss) : ∀ k < n + 1, ss k = MakeDetRun M as k := by
  rcases h with ⟨h_init, h_next⟩
  intro k h_k ; induction' k with k h_ind
  · simp [DetAutomaton.toND] at h_init
    simpa [MakeDetRun]
  · have h_next' := h_next k (by omega)
    simp [DetAutomaton.toND] at h_next'
    have h_ss_k := h_ind (by omega)
    simpa [MakeDetRun, ← h_ss_k]

end DetAutomata

section AcceptedLangCompl

variable {A : Type*} {M : DetAutomaton A} {acc : Set M.State}

theorem accepted_lang_compl [Inhabited A] :
    M.toND.AcceptedLang accᶜ = (M.toND.AcceptedLang acc)ᶜ := by
  ext al
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    rintro ⟨n', as', ⟨ss', h_run', h_acc'⟩, h_al'⟩
    have h_len : al.length = n := by rw [h_al, List.length_ofFn (f := (fun k : Fin n ↦ as k))]
    have h_len' : al.length = n' := by rw [h_al', List.length_ofFn (f := (fun k : Fin n' ↦ as' k))]
    have h_n_eq : n' = n := by rw [← h_len, ← h_len']
    obtain ⟨rfl⟩ := h_n_eq
    have h_run_n := automata_FinRun_FixSuffix h_run
    have h_run_n' := automata_FinRun_FixSuffix h_run'
    have h_as_eq : FixSuffix n as' default = FixSuffix n as default := by
      ext k
      rcases Classical.em (k < n) with h_k | h_k <;> simp [FixSuffix, h_k]
      have h_as_k : as k = al.get ⟨k, (by omega : k < al.length)⟩ := by simp [h_al]
      have h_as_k' : as' k = al.get ⟨k, (by omega : k < al.length)⟩ := by simp [h_al']
      rw [h_as_k, h_as_k']
    rw [h_as_eq] at h_run_n'
    have h_ss_n := det_automata_fin_run_unique h_run_n n (by omega)
    have h_ss_n' := det_automata_fin_run_unique h_run_n' n (by omega)
    simp [FixSuffix] at h_ss_n h_ss_n'
    rw [h_ss_n] at h_acc
    rw [h_ss_n'] at h_acc'
    contradiction
  · intro h_compl
    let as := fun k ↦ if h : k < al.length then al[k] else default
    have h_al : al = List.ofFn (fun k : Fin al.length ↦ as k) := by
      simp [List.ext_get_iff]
      intro k h_k ; simp [as, h_k]
    use al.length, as ; simp [← h_al]
    let ss := MakeDetRun M as
    have h_run : M.toND.FinRun al.length as ss := by
      exact det_automata_fin_run_exists al.length as
    use ss ; constructor
    · exact h_run
    intro h_acc
    have : al ∈ (M.toND.AcceptedLang acc) := by
      use al.length, as
      simp [← h_al] ; use! ss
    contradiction

end AcceptedLangCompl
