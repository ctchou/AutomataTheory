/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.DetProd

-- set_option diagnostics true
-- set_option diagnostics.threshold 10

/-!
This file proves various closure properties of deterministic Muller
(ω-)langauges.  Note that we do require that the Muller automaton
to have a finite state type.
-/

open Function Set Filter

section DetMullerLang

variable {A : Type}

/-- An ω-language is deterministic Muller iff it is accepted by a
finite-state deterministic Muller automaton
-/
def DetMullerLang (L : Set (ℕ → A)) :=
  ∃ M : DetAutomaton.{0, 0} A, ∃ accSet : Set (Set M.State),
  Finite M.State ∧ L = { as | M.MullerAccept accSet as }

/-- Deterministic Muller languages are closed under complementation.
-/
theorem det_muller_lang_compl {L : Set (ℕ → A)}
    (h : DetMullerLang L) : DetMullerLang Lᶜ := by
  obtain ⟨M, accSet, h_fin, rfl⟩ := h
  use M, accSetᶜ ; constructor
  · exact h_fin
  · ext as ; simp [det_muller_accept_compl]

/-- Deterministic Muller languages are closed under intersection.
-/
theorem det_muller_lang_inter {L0 L1 : Set (ℕ → A)}
    (h0 : DetMullerLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 ∩ L1) := by
  obtain ⟨M0, accSet0, h_fin0, rfl⟩ := h0
  obtain ⟨M1, accSet1, h_fin1, rfl⟩ := h1
  let M : Fin 2 → DetAutomaton A
    | 0 => M0
    | 1 => M1
  let accSet : (i : Fin 2) → Set (Set (M i).State)
    | 0 => accSet0
    | 1 => accSet1
  use (DetAutomaton.Prod M), (DetAutomaton.MullerAcc_Inter M accSet)
  have : ∀ i, Finite (M i).State := by simp [Fin.forall_fin_two] ; grind
  constructor
  · exact det_automata_prod_finite M
  · ext as
    simp [det_muller_accept_inter M accSet as, Fin.forall_fin_two] ; grind

/-- Deterministic Muller languages are closed under union.
-/
theorem det_muller_lang_union {L0 L1 : Set (ℕ → A)}
    (h0 : DetMullerLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 ∪ L1) := by
  obtain ⟨M0, accSet0, h_fin0, rfl⟩ := h0
  obtain ⟨M1, accSet1, h_fin1, rfl⟩ := h1
  let M : Fin 2 → DetAutomaton A
    | 0 => M0
    | 1 => M1
  let accSet : (i : Fin 2) → Set (Set (M i).State)
    | 0 => accSet0
    | 1 => accSet1
  use (DetAutomaton.Prod M), (DetAutomaton.MullerAcc_Union M accSet)
  have : ∀ i, Finite (M i).State := by simp [Fin.forall_fin_two] ; grind
  constructor
  · exact det_automata_prod_finite M
  · ext as
    simp [det_muller_accept_union M accSet as, Fin.exists_fin_two] ; grind

end DetMullerLang
