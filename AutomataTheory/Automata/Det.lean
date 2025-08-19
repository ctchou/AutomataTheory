/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc

/-!
The deterministic automaton class `DetAutomaton` is analogous to the
`Automaton` class, except that its initial and next states are unique.
-/

open Function Set

section DetAutomata

class DetAutomaton (A : Type) where
  State : Type
  init : State
  next : State → A → State

variable {A : Type}

/-- Converting a `DetAutomaton` to an `Automaton`.
-/
def DetAutomaton.toNA (M : DetAutomaton A) : Automaton A where
  State := M.State
  init := {M.init}
  next := ({M.next · ·})

/-- The unique run of a `DetAutomaton` on an input sequence from `A`.
-/
def DetAutomaton.DetRun (M : DetAutomaton A) (as : ℕ → A) : ℕ → M.State
  | 0 => M.init
  | k + 1 => M.next (DetRun M as k) (as k)

variable {M : DetAutomaton A}

/-- A `DetAutomaton` has an infinite run on any infinite input.
-/
theorem det_automata_inf_run_exists (as : ℕ → A) :
    M.toNA.InfRun as (M.DetRun as) := by
  constructor <;> simp [DetAutomaton.toNA, DetAutomaton.DetRun]

/-- A `DetAutomaton` has a unique infinite run on any infinite input.
-/
theorem det_automata_inf_run_unique {as : ℕ → A} {ss : ℕ → M.State}
    (h : M.toNA.InfRun as ss) : ss = M.DetRun as := by
  ext k
  induction' k with k h_ind
  · simpa [DetAutomaton.toNA] using h.1
  · simpa [DetAutomaton.toNA, DetAutomaton.DetRun, h_ind] using h.2 k

/-- A `DetAutomaton` has a finite run on any finite input.
-/
theorem det_automata_fin_run_exists (n : ℕ) (as : ℕ → A) :
    M.toNA.FinRun n as (M.DetRun as) :=
  automata_InfRun_iff_FinRun.mp (det_automata_inf_run_exists as) n

/-- A `DetAutomaton` has a unique finite run on any finite input.
-/
theorem det_automata_fin_run_unique {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : M.toNA.FinRun n as ss) : ∀ k < n + 1, ss k = M.DetRun as k := by
  rcases h with ⟨h_init, h_next⟩
  intro k h_k ; induction' k with k h_ind
  · simp [DetAutomaton.toNA] at h_init
    simpa [DetAutomaton.DetRun]
  · have h_next' := h_next k (by omega)
    simp [DetAutomaton.toNA] at h_next'
    have h_ss_k := h_ind (by omega)
    simpa [DetAutomaton.DetRun, ← h_ss_k]

end DetAutomata

section DetAutomatonAcceptedLang

variable {A : Type} {M : DetAutomaton A} {acc : Set M.State}

/-- For a `DetAutomaton`, complementing the language it accepts can be achieved
by simply complementing the set of accepting states.
-/
theorem accepted_lang_compl [Inhabited A] :
    M.toNA.AcceptedLang accᶜ = (M.toNA.AcceptedLang acc)ᶜ := by
  ext al
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    rintro ⟨n', as', ⟨ss', h_run', h_acc'⟩, h_al'⟩
    have h_len : al.length = n := by rw [h_al, List.length_ofFn (f := (fun k : Fin n ↦ as k))]
    have h_len' : al.length = n' := by rw [h_al', List.length_ofFn (f := (fun k : Fin n' ↦ as' k))]
    obtain ⟨rfl⟩ : n' = n := h_len'.symm.trans h_len
    have h_run_n := automata_FinRun_FixSuffix h_run
    have h_run_n' := automata_FinRun_FixSuffix h_run'
    have h_as_eq : FixSuffix as' n default = FixSuffix as n default := by
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
    let ss := M.DetRun as
    have h_run : M.toNA.FinRun al.length as ss := by
      exact det_automata_fin_run_exists al.length as
    use ss ; constructor
    · exact h_run
    intro h_acc
    have : al ∈ (M.toNA.AcceptedLang acc) := by
      use al.length, as
      simp [← h_al] ; use! ss
    contradiction

/-- The ω-language accepted by a deterministic Buchi automaton is the ω-limit
of the language accepted by the same automaton.
-/
theorem det_automta_accepted_omega_lang :
    M.toNA.AcceptedOmegaLang acc = (M.toNA.AcceptedLang acc)↗ω := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨φ, h_mono, h_acc⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    use φ ; simp [h_mono] ; intro m
    use (φ m), as ; constructor <;> [skip ; rfl]
    use ss ; simp [h_acc]
    exact automata_InfRun_iff_FinRun.mp h_run (φ m)
  · simp only [instOmegaLimit, OmegaLimit, frequently_iff_strict_mono, mem_setOf_eq]
    rintro ⟨φ, h_mono, h_acc⟩
    use (M.DetRun as) ; constructor
    · apply det_automata_inf_run_exists
    apply frequently_iff_strict_mono.mpr
    use φ ; simp [h_mono] ; intro m
    obtain ⟨n, as', ⟨ss, h_run', h_acc'⟩, h_as'⟩ := h_acc m
    simp [instFinSubseq, FinSubseq, List.ofFn_inj'] at h_as'
    obtain ⟨rfl, h_as'⟩ := h_as'
    simp [funext_iff, Fin.forall_iff] at h_as'
    have h_run : M.toNA.FinRun (φ m) as ss := automata_FinRun_modulo
      (M := M.toNA) (n := φ m) (as := as') (as' := as) (ss := ss) (ss' := ss) (by grind) (by grind) h_run'
    have := det_automata_fin_run_unique h_run (φ m) (by omega)
    simp_all

end DetAutomatonAcceptedLang

section DetMuller

variable {A : Type}

/-- Muller acceptance condition for a deterministic automaton.
-/
def DetAutomaton.MullerAccept (M : DetAutomaton A) (accSet : Set (Set M.State)) (as : ℕ → A) :=
  InfOcc (M.DetRun as) ∈ accSet

/-- For a deterministic Muller automaton, complementing the ω-language it accepts
can be achieved by simply complementing the set of accepting state sets.
-/
theorem det_muller_accept_compl (M : DetAutomaton A) (accSet : Set (Set M.State)) (as : ℕ → A) :
    M.MullerAccept accSetᶜ as ↔ ¬ M.MullerAccept accSet as := by
  simp [DetAutomaton.MullerAccept]

/-- The ω-limit of the language accepted by a deterministic automaton is
accepted by a deterministic Muller automaton.
-/
theorem det_muller_accept_omega_limit (M : DetAutomaton A) [Finite M.State] (acc : Set M.State) :
    ∃ accSet, {as | M.MullerAccept accSet as} = (M.toNA.AcceptedLang acc)↗ω := by
  use {acc' | (acc' ∩ acc).Nonempty} ; ext as
  simp [← det_automta_accepted_omega_lang, DetAutomaton.MullerAccept] ; constructor
  · rintro ⟨s, h_inf, h_acc⟩
    use (M.DetRun as) ; constructor
    · exact det_automata_inf_run_exists as
    obtain ⟨φ, h_mono, h_s⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    use φ ; simp [*]
  · rintro ⟨ss, h_run, h_acc⟩
    obtain ⟨rfl⟩ := det_automata_inf_run_unique h_run
    have : Finite M.toNA.State := by assumption
    obtain ⟨s, h_s, h_inf⟩ := frequently_in_finite_set.mp h_acc
    use s ; aesop

end DetMuller
