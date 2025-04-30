/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import AutomataTheory.AutomataBasic

open BigOperators Function Set Filter

section DetAutomata

class DetAutomata (A : Type*) extends Automata A where
  get_init : State
  get_next : State → A → State
  det_init : init = {get_init}
  det_next : ∀ s a, next s a = {get_next s a}

variable {A : Type*}

def MakeFinRun (M : DetAutomata A) (n : ℕ) (as : Fin n → A) (k : Fin (n + 1)) : M.State :=
  if h : k > 0 then
    have : k - 1 < k := by linarith
    have h'' : k - 1 ≠ Fin.last n := by sorry
    M.get_next (MakeFinRun M n as (k - 1)) (as (Fin.castPred (k - 1) h''))
  else M.get_init

-- def MakeFinRun (M : DetAutomata A) (n : ℕ) (as : Fin n → A) : Fin (n + 1) → M.State
--   | 0 => M.get_init
--   | k + 1 => M.get_next (MakeFinRun M n as k) (as k)

def MakeInfRun (M : DetAutomata A) (as : ℕ → A) : ℕ → M.State
  | 0 => M.get_init
  | k + 1 => M.get_next (MakeInfRun M as k) (as k)

-- def Deterministic (M : Automata A) : Prop :=
--   (∃ s0, M.init = {s0}) ∧ (∀ s a, ∃ s', M.next s a = {s'})

variable (M : DetAutomata A)

-- theorem det_automata_uniq_fin_run (n : ℕ) (as : Fin n → A) :
--     ∃ ss : Fin (n + 1) → M.State, FinRun M.toAutomata n as ss := by
--   sorry

end DetAutomata

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
    FinRun M n as ss ↔ FinRun (AutomataPSet M).toAutomata n as (fun k : Fin (n + 1) ↦ {s | s = ss k}) := by
  sorry

end AutomataPSet
