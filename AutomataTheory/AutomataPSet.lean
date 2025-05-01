/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Basic
import AutomataTheory.AutomataDet

section AutomataPSet

variable {A : Type*}

def AutomataPSet (M : Automata A) : DetAutomata A where
  State := Set M.State
  init := {M.init}
  next := fun ps a ↦ { ⋃ s ∈ ps, M.next s a }
  get_init := M.init
  get_next := fun ps a ↦ ⋃ s ∈ ps, M.next s a
  det_init := by simp
  det_next := by simp

variable (M : Automata A)

theorem automata_pset_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :
    FinRun M n as ss ↔ (∀ k, MakeFinRun (AutomataPSet M) n as k (ss k)) := by
  sorry

theorem automata_pset_inf_run (as : ℕ → A) (ss : ℕ → M.State) :
    InfRun M as ss ↔ (∀ k, MakeInfRun (AutomataPSet M) as k (ss k)) := by
  sorry

end AutomataPSet
