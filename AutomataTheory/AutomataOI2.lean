/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.AutomataProd
import AutomataTheory.AutomataHist
import AutomataTheory.Temporal

/-!
The OI2 [*] construction is used to prove the closure of ω-regular langauges
under (finite) intersection.  The the new accepting condition uses the 1-bit
history state to ensure that the accepting states of (M 0) and those of (M 1)
alternate with each other, so that both occur infinitely often if either occurs
infinitely often.

[*] "OI2" = "Omega Intersection of 2 automata"
-/

open Function Set Filter

section AutomataOI2

open Classical

variable {A : Type*} (M : Fin 2 → Automaton A) (acc : (i : Fin 2) → Set ((M i).State))

def Automaton.OI2_HistInit : Set (Fin 2) := {0}

def Automaton.OI2_HistNext : (Automaton.Prod M).State × Fin 2 → A → Set (Fin 2) :=
  fun s _ ↦
    if s.1 0 ∈ acc 0 ∧ s.2 = 0 then {1} else
    if s.1 1 ∈ acc 1 ∧ s.2 = 1 then {0} else {s.2}

def Automaton.OI2 : Automaton A :=
  (Automaton.Prod M).addHist Automaton.OI2_HistInit (Automaton.OI2_HistNext M acc)

def Automaton.OI2_Acc : Set (Automaton.OI2 M acc).State :=
  { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 } ∪ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }

private lemma automata_oi2_lemma1 {as : ℕ → A} {ss : ℕ → (Automaton.OI2 M acc).State}
    (h_run : InfRun (Automaton.OI2 M acc) as ss) :
      (∃ᶠ k in atTop, ss k ∈ { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 }) ↔
      (∃ᶠ k in atTop, ss k ∈ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }) := by
  constructor <;> intro h_inf
  · suffices h_lt : LeadsTo ss {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} by
      exact frequently_leads_to_frequently h_inf h_lt
    have h_lt1 : LeadsTo ss {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} {s | s.2 = 1} := by
      apply leads_to_step ; simp [Step]
      intro k h_acc h_hist
      have h_step := (h_run.2 k).2
      simp [Automaton.OI2_HistNext, h_acc, h_hist] at h_step
      assumption
    have h_lt2 : LeadsTo ss {s | s.2 = 1} {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} := by
      apply leads_to_until_frequently_1
      · simp [Step]
        intro k h_hist h_acc
        rw [imp_not_comm] at h_acc
        have h_acc := h_acc h_hist
        have h_step := (h_run.2 k).2
        simp [Automaton.OI2_HistNext, h_acc, h_hist] at h_step
        assumption
      · let p k := ss k ∈ {s | s.1 0 ∈ acc 0 ∧ s.2 = 0}
        let q k := ss k ∉ {s | s.2 = 1}
        have h_imp : ∀ k, p k → q k := by
          intro k ; simp [p, q]
          intro _ h ; simp [h]
        exact Frequently.mono h_inf h_imp
    exact leads_to_trans h_lt1 h_lt2
  · suffices h_lt : LeadsTo ss {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} by
      exact frequently_leads_to_frequently h_inf h_lt
    have h_lt1 : LeadsTo ss {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} {s | s.2 = 0} := by
      apply leads_to_step ; simp [Step]
      intro k h_acc h_hist
      have h_step := (h_run.2 k).2
      simp [Automaton.OI2_HistNext, h_acc, h_hist] at h_step
      assumption
    have h_lt2 : LeadsTo ss {s | s.2 = 0} {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} := by
      apply leads_to_until_frequently_1
      · simp [Step]
        intro k h_hist h_acc
        rw [imp_not_comm] at h_acc
        have h_acc := h_acc h_hist
        have h_step := (h_run.2 k).2
        simp [Automaton.OI2_HistNext, h_acc, h_hist] at h_step
        assumption
      · let p k := ss k ∈ {s | s.1 1 ∈ acc 1 ∧ s.2 = 1}
        let q k := ss k ∉ {s | s.2 = 0}
        have h_imp : ∀ k, p k → q k := by
          intro k ; simp [p, q]
          intro _ h ; simp [h]
        exact Frequently.mono h_inf h_imp
    exact leads_to_trans h_lt1 h_lt2

private lemma automata_oi2_lemma2 {as : ℕ → A} {ss : ℕ → (Automaton.OI2 M acc).State}
    (h_run : InfRun (Automaton.OI2 M acc) as ss)
    (h_inf0 : ∃ᶠ k in atTop, ss k ∈ { s | s.1 0 ∈ acc 0 })
    (h_inf1 : ∃ᶠ k in atTop, ss k ∈ { s | s.1 1 ∈ acc 1 }) :
      ∃ᶠ k in atTop, ss k ∈ { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 } ∪ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 } := by
  have h_true : ∃ᶠ k in atTop, ss k ∈ univ := by simp [atTop_neBot]
  apply frequently_leads_to_frequently h_true
  apply leads_to_cases (p := univ) (q := {s | s.2 = 0}) <;> simp [univ_inter]
  · have h_inter : {s : (Automaton.OI2 M acc).State | s.1 0 ∈ acc 0 ∧ s.2 = 0} = {s | s.2 = 0} ∩ {s | s.1 0 ∈ acc 0} := by
      ext s ; simp ; tauto
    rw [h_inter]
    apply leads_to_until_frequently_2 (h2 := h_inf0)
    simp [Step]
    intro k h_hist h_acc
    have h_step := (h_run.2 k).2
    simp [Automaton.OI2_HistNext, h_acc, h_hist] at h_step
    assumption
  · have h_inter : {s : (Automaton.OI2 M acc).State | s.1 1 ∈ acc 1 ∧ s.2 = 1} = {s | s.2 = 1} ∩ {s | s.1 1 ∈ acc 1} := by
      ext s ; simp ; tauto
    have h_compl : {s : (Automaton.OI2 M acc).State | s.2 = 0}ᶜ = {s | s.2 = 1} := by
      ext s ; simp
      constructor
      · exact Fin.eq_one_of_ne_zero s.2
      . intro h ; simp [h]
    rw [h_inter, h_compl]
    apply leads_to_until_frequently_2 (h2 := h_inf1)
    simp [Step]
    intro k h_hist h_acc
    have h_step := (h_run.2 k).2
    simp [Automaton.OI2_HistNext, h_acc, h_hist] at h_step
    assumption

theorem accepted_omega_lang_inter2 :
    AcceptedOmegaLang (Automaton.OI2 M acc) (Automaton.OI2_Acc M acc) = ⋂ i : Fin 2, AcceptedOmegaLang (M i) (acc i) := by
  ext as ; simp [AcceptedOmegaLang, BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩ i
    have h_run1 := automata_hist_inf_run_proj (Automaton.Prod M) Automaton.OI2_HistInit (Automaton.OI2_HistNext M acc) h_run
    have h_run' := automata_prod_inf_run.mp h_run1 i
--    have h_run' := (automata_prod_inf_run M as (Prod.fst ∘ ss)).mp h_run1 i
    use (fun k ↦ (Prod.fst ∘ ss) k i) ; constructor
    · assumption
    let p0 k := ss k ∈ { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 }
    let p1 k := ss k ∈ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }
    have h_inf_or : ∃ᶠ k in atTop, p0 k ∨ p1 k := by exact h_inf
    rw [frequently_or_distrib] at h_inf_or
    let p0' k := (Prod.fst ∘ ss) k 0 ∈ acc 0
    let p1' k := (Prod.fst ∘ ss) k 1 ∈ acc 1
    have h_p0_p0' : ∀ k, p0 k → p0' k := by intro k ; simp [p0, p0'] ; tauto
    have h_p1_p1' : ∀ k, p1 k → p1' k := by intro k ; simp [p1, p1'] ; tauto
    revert i ; rw [Fin.forall_fin_two]
    constructor <;> intro h_run_i
    · rcases h_inf_or with h_inf0 | h_inf1
      · exact Frequently.mono h_inf0 h_p0_p0'
      · rw [← automata_oi2_lemma1 M acc h_run] at h_inf1
        exact Frequently.mono h_inf1 h_p0_p0'
    · rcases h_inf_or with h_inf0 | h_inf1
      · rw [automata_oi2_lemma1 M acc h_run] at h_inf0
        exact Frequently.mono h_inf0 h_p1_p1'
      · exact Frequently.mono h_inf1 h_p1_p1'
  · intro h_all
    choose ss h_ss using h_all
    let ss' := fun k i ↦ ss i k
    have h_ss' : ∀ i, InfRun (M i) as (fun k ↦ ss' k i) := by intro i ; exact (h_ss i).1
    have h_run' := automata_prod_inf_run.mpr h_ss'
    have h_hist_init : Automaton.OI2_HistInit.Nonempty := by simp [Automaton.OI2_HistInit]
    have h_hist_next : ∀ s a, (Automaton.OI2_HistNext M acc s a).Nonempty := by
      intro s a ; simp only [Automaton.OI2_HistNext]
      rcases Classical.em (s.1 0 ∈ acc 0 ∧ s.2 = 0) with cond1 | cond1 <;> simp [cond1]
      rcases Classical.em (s.1 1 ∈ acc 1 ∧ s.2 = 1) with cond2 | cond2 <;> simp [cond2]
    have h_runh := automata_hist_inf_run_exists (Automaton.Prod M) Automaton.OI2_HistInit (Automaton.OI2_HistNext M acc)
      h_hist_init h_hist_next h_run'
    obtain ⟨hs, h_run⟩ := h_runh
    use (fun k ↦ (ss' k, hs k))
    constructor
    · assumption
    have h_inf0 : ∃ᶠ k in atTop, ss' k ∈ { s | s 0 ∈ acc 0 } := by simp [ss', (h_ss 0).2]
    have h_inf1 : ∃ᶠ k in atTop, ss' k ∈ { s | s 1 ∈ acc 1 } := by simp [ss', (h_ss 1).2]
    exact automata_oi2_lemma2 M acc h_run h_inf0 h_inf1

end AutomataOI2
