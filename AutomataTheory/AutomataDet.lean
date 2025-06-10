/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.AutomataBasic

/-!
The deterministic automaton class DetAutomaton extends the Automaton class
by providing unique initial and next states and thus making it deterministic.
-/

open Function Set Filter

section DetAutomata

class DetAutomaton (A : Type*) extends Automaton A where
  get_init : State
  get_next : State → A → State
  det_init : init = {get_init}
  det_next : ∀ s a, next s a = {get_next s a}

variable {A : Type*}

def MakeDetRun (M : DetAutomaton A) (as : ℕ → A) : ℕ → M.State
  | 0 => M.get_init
  | k + 1 => M.get_next (MakeDetRun M as k) (as k)

variable {M : DetAutomaton A}

theorem det_automata_inf_run_exists (as : ℕ → A) :
    InfRun M.toAutomaton as (MakeDetRun M as) := by
  constructor
  · simp [M.det_init, MakeDetRun]
  · simp [M.det_next, MakeDetRun]

theorem det_automata_inf_run_unique {as : ℕ → A} {ss : ℕ → M.State}
    (h : InfRun M.toAutomaton as ss) : ss = MakeDetRun M as := by
  ext k ; induction' k with k h_ind
  · have h_init := h.1
    simp [M.det_init] at h_init
    assumption
  · rw [MakeDetRun, ← h_ind]
    have h_next := h.2 k
    simp [M.det_next] at h_next
    assumption

theorem det_automata_fin_run_exists (n : ℕ) (as : ℕ → A) :
    FinRun M.toAutomaton n as (MakeDetRun M as) := by
  exact automata_InfRun_iff_FinRun.mp (det_automata_inf_run_exists as) n

theorem det_automata_fin_run_unique {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : FinRun M.toAutomaton n as ss) : ∀ k < n + 1, ss k = MakeDetRun M as k := by
  rcases h with ⟨h_init, h_next⟩
  intro k h_k ; induction' k with k h_ind
  · simp [M.det_init] at h_init
    simpa [MakeDetRun]
  · have h_next' := h_next k (by omega)
    simp [M.det_next] at h_next'
    have h_ss_k := h_ind (by omega)
    simpa [MakeDetRun, ← h_ss_k]

end DetAutomata

section AcceptedLangCompl

variable {A : Type*} {M : DetAutomaton A} {acc : Set M.State}

theorem accepted_lang_compl [Inhabited A] :
    AcceptedLang M.toAutomaton accᶜ = (AcceptedLang M.toAutomaton acc)ᶜ := by
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
    have h_run : FinRun DetAutomaton.toAutomaton al.length as ss := by
      exact det_automata_fin_run_exists al.length as
    use ss ; constructor
    · exact h_run
    intro h_acc
    have : al ∈ (AcceptedLang DetAutomaton.toAutomaton acc) := by
      use al.length, as
      simp [← h_al] ; use! ss
    contradiction

end AcceptedLangCompl
