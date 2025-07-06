/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.AutomataDet

/-!
A congruence is an equivalence relation on finite sequences that is
preserved by concatenation either on the left or on the right or both.
For now, we assume only the right congruence condition.  We will
add the left congruence condition if and when it is needed.
-/

open Function Set

section Congruences

class Congruence (A : Type*) extends eq : Setoid (List A) where
--  left_congr : ∀ u v, eq u v → ∀ w, eq (w ++ u) (w ++ v)
  right_congr : ∀ u v, eq u v → ∀ w, eq (u ++ w) (v ++ w)

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

end Congruences
