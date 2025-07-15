/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Congruences.Basic
import AutomataTheory.Automata.Det

/-!
The deterministic automaton corresponding to a right congruence relation.
Note that the theorems in this file do not require that the congruence
relation is of finite index.
-/

open Function Set

section AutomataCongr

variable {A : Type*}

def DetAutomaton.ofCongr (c : Congruence A) : DetAutomaton A where
  State := Quotient c.eq
  init := ⟦ [] ⟧
  next := fun s a ↦ Quotient.lift (fun u ↦ ⟦ u ++ [a] ⟧) ( by
    intro u v h_eq ; simp ; exact Congruence.right_congr u v h_eq [a]
  ) s

variable {c : Congruence A}

theorem automaton_congr_run (as : ℕ → A) (n : ℕ) :
    MakeDetRun (DetAutomaton.ofCongr c) as n = ⟦ List.ofFn (fun k : Fin n ↦ as k) ⟧ := by
  induction' n with n h_ind
  · simp [MakeDetRun, DetAutomaton.ofCongr]
  simp only [MakeDetRun, h_ind]
  simp only [DetAutomaton.ofCongr, Quotient.lift_mk, Quotient.eq]
  suffices h_eq : ((List.ofFn fun k : Fin n ↦ as ↑k) ++ [as n]) = (List.ofFn fun k : Fin (n + 1) ↦ as ↑k) by
    simp [h_eq, c.eq.iseqv.refl]
  exact Eq.symm List.ofFn_succ_last

theorem accepted_lang_congr [Inhabited A] (s : (DetAutomaton.ofCongr c).State) :
    AcceptedLang (DetAutomaton.ofCongr c).toAutomaton {s} = Quotient.mk c.eq ⁻¹' {s} := by
  ext al ; simp [AcceptedLang, FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, rfl⟩, rfl⟩
    have h_ss_n := det_automata_fin_run_unique h_run n (by omega)
    simp [h_ss_n, automaton_congr_run]
  · rintro ⟨rfl⟩
    let as := fun k ↦ if h : k < al.length then al[k] else default
    use al.length, as
    constructor <;> [skip ; simp [as]]
    use (MakeDetRun (DetAutomaton.ofCongr c) as)
    constructor
    · exact det_automata_fin_run_exists al.length as
    · simp [automaton_congr_run, as]

end AutomataCongr
