/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Basic
import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.InfOcc

/-!
The deterministic automaton class `Automata.DA` is analogous to the
`Automata.NA` class, except that its initial and next states are unique.
-/

open Function Set Filter Stream'

namespace Automata

section DetAutomataBasic

class DA (A : Type) where
  State : Type
  init : State
  next : State → A → State

variable {A : Type}

/-- Converting a `DA` to an `NA`.
-/
def DA.toNA (M : DA A) : NA A where
  State := M.State
  init := {M.init}
  next := ({M.next · ·})
--  next := fun s a ↦ {M.next s a}

/-- The unique run of a `DA` on an input sequence from `A`.
-/
def DA.DetRun (M : DA A) (as : Stream' A) : Stream' M.State
  | 0 => M.init
  | k + 1 => M.next (DetRun M as k) (as k)

/-- The state of `M` after inputting `al` starting from state `s`.
-/
def DA.RunFromOn (M : DA A) (s : M.State) (al : List A) : M.State :=
  al.foldl M.next s

/-- The state of `M` after inputting `al` starting from the initial state.
-/
def DA.RunOn (M : DA A) : List A → M.State :=
  M.RunFromOn M.init

variable {M : DA A}

/-- A `DA` has an infinite run on any infinite input.
-/
theorem da_inf_run_exists (as : Stream' A) :
    M.toNA.InfRun as (M.DetRun as) := by
  constructor <;> simp [DA.toNA, DA.DetRun]

/-- A `DA` has a unique infinite run on any infinite input.
-/
theorem da_inf_run_unique {as : Stream' A} {ss : Stream' M.State}
    (h : M.toNA.InfRun as ss) : ss = M.DetRun as := by
  ext k ; simp [get.eq_1] ; induction' k with k h_ind
  · simpa [DA.toNA] using h.1
  · simpa [DA.DetRun, DA.toNA, h_ind] using h.2 k

/-- A `DA` has a finite run on any finite input.
-/
theorem da_fin_run_exists (n : ℕ) (as : Stream' A) :
    M.toNA.FinRun n as (M.DetRun as) :=
  na_InfRun_iff_FinRun.mp (da_inf_run_exists as) n

/-- A `DA` has a unique finite run on any finite input.
-/
theorem da_fin_run_unique {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h : M.toNA.FinRun n as ss) : ∀ k < n + 1, ss k = M.DetRun as k := by
  rcases h with ⟨h_init, h_next⟩
  intro k h_k ; induction' k with k h_ind
  · simp [DA.toNA] at h_init
    simpa [DA.DetRun]
  · have h_next' := h_next k (by omega)
    simp [DA.toNA] at h_next'
    have h_ss_k := h_ind (by omega)
    simpa [DA.DetRun, ← h_ss_k]

/-- Running on `al1 ++ al2` starting from `s` is the same as running
on `al1` starting from `s` and then running on `al2` from the reached state.
-/
theorem da_run_from_on_append (M : DA A) (s : M.State) (al1 al2 : List A) :
    M.RunFromOn s (al1 ++ al2) = M.RunFromOn (M.RunFromOn s al1) al2 := by
  simp only [DA.RunFromOn, List.foldl_append]

/-- Relatung `DA.RunOn` and `DA.DetRun`.
-/
theorem da_run_on_of_det_run (M : DA A) (as : Stream' A) (n : ℕ) :
    M.RunOn (as.extract 0 n) = M.DetRun as n := by
  induction' n with n h_ind
  · simp [extract_eq_nil, DA.DetRun, DA.RunOn, DA.RunFromOn]
  have h1 := extract_succ_right' (xs := as) (show 0 ≤ n by omega)
  rw [DA.RunOn, DA.DetRun, ← h_ind, h1, da_run_from_on_append] ; rfl

/-- A technical result for extending a finite run to an infinite run.
-/
theorem da_run_on_to_det_run [Inhabited A] (M : DA A) (al : List A) :
    M.RunOn al = M.DetRun al.padDefault al.length := by
  simp [← da_run_on_of_det_run M al.padDefault al.length, extract_padDefault]

/-- A finite word `al` is accepted by `M` if and only if `M` reaches an
accepting state after running on `al` starting from the initial state.
-/
theorem da_acc_lang_iff_run_acc [Inhabited A] (M : DA A) (acc : Set M.State) (al : List A) :
    al ∈ M.toNA.AcceptedLang acc ↔ M.RunOn al ∈ acc := by
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, rfl⟩
    have h0 := da_fin_run_unique h_run n (by omega)
    have h1 := da_run_on_of_det_run M as n
    simp [h1, ← h0, h_acc]
  · intro h_acc
    use al.length, al.padDefault ; simp [extract_padDefault]
    use (M.DetRun al.padDefault) ; constructor
    · exact da_fin_run_exists (M := M) al.length al.padDefault
    · simp [← da_run_on_to_det_run, h_acc]

end DetAutomataBasic

section DetAcceptedLang

variable {A : Type} {M : DA A} {acc : Set M.State}

/-- For a `DA`, complementing the language it accepts can be achieved
by simply complementing the set of accepting states.
-/
theorem da_acc_lang_compl [Inhabited A] :
    M.toNA.AcceptedLang accᶜ = (M.toNA.AcceptedLang acc)ᶜ := by
  ext al
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    rintro ⟨n', as', ⟨ss', h_run', h_acc'⟩, h_al'⟩
    have h_len : al.length = n := by simp [← h_al, length_extract]
    have h_len' : al.length = n' := by simp [← h_al', length_extract]
    obtain ⟨rfl⟩ := show n' = n by rw [← h_len, ← h_len']
    have h_run_n := na_FinRun_fixSuffix h_run
    have h_run_n' := na_FinRun_fixSuffix h_run'
    have h_as_eq : fixSuffix as' n default = fixSuffix as n default := by
      ext k ; simp [get.eq_1] ; rcases Classical.em (k < n) with h_k | h_k <;> simp [fixSuffix, h_k]
      have h_as_k : as k = al.get ⟨k, (by omega)⟩ := by simp (disch := omega) [← h_al, get_extract']
      have h_as_k' : as' k = al.get ⟨k, (by omega)⟩ := by simp (disch := omega) [← h_al', get_extract']
      rw [h_as_k, h_as_k']
    rw [h_as_eq] at h_run_n'
    have h_ss_n := da_fin_run_unique h_run_n n (by omega)
    have h_ss_n' := da_fin_run_unique h_run_n' n (by omega)
    simp [fixSuffix] at h_ss_n h_ss_n'
    rw [h_ss_n] at h_acc ; rw [h_ss_n'] at h_acc'
    contradiction
  · intro h_compl
--    let as := fun k ↦ if h : k < al.length then al[k] else default
    let as := al.padDefault
    have h_al : as.extract 0 al.length = al := by simp [as, extract_padDefault]
    use al.length, as ; simp [h_al]
    let ss := M.DetRun as
    have h_run : M.toNA.FinRun al.length as ss := by exact da_fin_run_exists al.length as
    use ss ; constructor
    · exact h_run
    intro h_acc
    have : al ∈ (M.toNA.AcceptedLang acc) := by
      use al.length, as ; simp [h_al] ; use! ss
    contradiction

/-- The ω-language accepted by a deterministic Buchi automaton is the ω-limit
of the language accepted by the same automaton.
-/
theorem da_acc_omega_lang :
    M.toNA.AcceptedOmegaLang acc = (M.toNA.AcceptedLang acc)↗ω := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨φ, h_mono, h_acc⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    use φ ; simp [h_mono] ; intro m
    use (φ m), as ; constructor <;> [skip ; rfl]
    use ss ; simp [h_acc]
    exact na_InfRun_iff_FinRun.mp h_run (φ m)
  · simp only [instOmegaLimit, OmegaLimit, frequently_iff_strict_mono, mem_setOf_eq]
    rintro ⟨φ, h_mono, h_acc⟩
    use (M.DetRun as) ; constructor
    · apply da_inf_run_exists
    apply frequently_iff_strict_mono.mpr
    use φ ; simp [h_mono] ; intro m
    obtain ⟨n, as', ⟨ss, h_run', h_acc'⟩, h_as'⟩ := h_acc m
    have h_as' := extract_eq_extract h_as' ; simp at h_as'
    obtain ⟨rfl, h_as'⟩ := h_as'
    have h_run : M.toNA.FinRun (φ m) as ss := na_FinRun_modulo
      (M := M.toNA) (n := φ m) (as := as') (as' := as) (ss := ss) (ss' := ss) (by grind) (by grind) h_run'
    have := da_fin_run_unique h_run (φ m) (by omega)
    simp_all

end DetAcceptedLang

section DetMullerAccept

variable {A : Type}

/-- Muller acceptance condition for a deterministic automaton.
-/
def DA.MullerAccept (M : DA A) (accSet : Set (Set M.State)) (as : Stream' A) :=
  InfOcc (M.DetRun as) ∈ accSet

/-- For a deterministic Muller automaton, complementing the ω-language it accepts
can be achieved by simply complementing the set of accepting state sets.
-/
theorem det_muller_accept_compl (M : DA A) (accSet : Set (Set M.State)) (as : Stream' A) :
    M.MullerAccept accSetᶜ as ↔ ¬ M.MullerAccept accSet as := by
  simp [DA.MullerAccept]

/-- The ω-limit of the language accepted by a deterministic automaton is
accepted by a deterministic Muller automaton.
-/
theorem det_muller_accept_omega_limit (M : DA A) [Finite M.State] (acc : Set M.State) :
    ∃ accSet, {as | M.MullerAccept accSet as} = (M.toNA.AcceptedLang acc)↗ω := by
  use {acc' | (acc' ∩ acc).Nonempty} ; ext as
  simp [← da_acc_omega_lang, DA.MullerAccept] ; constructor
  · rintro ⟨s, h_inf, h_acc⟩
    use (M.DetRun as) ; constructor
    · exact da_inf_run_exists as
    obtain ⟨φ, h_mono, h_s⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    use φ ; simp [*]
  · rintro ⟨ss, h_run, h_acc⟩
    obtain ⟨rfl⟩ := da_inf_run_unique h_run
    have : Finite M.toNA.State := by assumption
    obtain ⟨s, h_s, h_inf⟩ := frequently_in_finite_set.mp h_acc
    use s ; aesop

/-- The ω-language accepted by a deterministic Muller automaton is a boolean
combination of the ω-limits of accepted languages.  Note that this result does
not need to assume that the automaton is finite-state.
-/
theorem det_muller_accept_boolean_form (M : DA A) (accSet : Set (Set M.State)) :
    {as | M.MullerAccept accSet as} =
    ⋃ acc ∈ accSet, (⋂ s ∈ acc, (M.toNA.AcceptedLang {s})↗ω) ∩ (⋂ s ∈ accᶜ, ((M.toNA.AcceptedLang {s})↗ω)ᶜ) := by
  ext as ; simp [DA.MullerAccept, mem_setOf_eq, ← da_acc_omega_lang] ; constructor
  · intro h_acc ; use InfOcc (M.DetRun as); simp [h_acc] ; constructor <;> intro s h_s
    · use (M.DetRun as) ; constructor
      · exact da_inf_run_exists as
      · exact h_s
    · rintro ⟨ss, h_run, h_inf⟩
      obtain ⟨rfl⟩ := da_inf_run_unique h_run
      contradiction
  · rintro ⟨acc, h_inf, h_acc, h_fin⟩
    suffices h : acc = InfOcc (M.DetRun as) by simp [← h, h_acc]
    ext s ; constructor <;> intro h_s
    · obtain ⟨ss, h_run, h_inf'⟩ := h_inf s h_s
      obtain ⟨rfl⟩ := da_inf_run_unique h_run
      exact h_inf'
    · by_contra h_contra
      have h_as := h_fin s h_contra
      simp only [NA.AcceptedOmegaLang, NA.BuchiAccept, mem_singleton_iff, mem_setOf_eq, not_exists, not_and] at h_as
      have := h_as (M.DetRun as) (da_inf_run_exists as)
      contradiction

end DetMullerAccept
