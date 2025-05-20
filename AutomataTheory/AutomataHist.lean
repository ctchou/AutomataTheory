/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.AutomataBasic

open Function Set Filter

section AutomataHist

variable {A H : Type*}

def AutomataHist (M : Automaton A) (hist_init : Set H) (hist_next : M.State × H → A → Set H) : Automaton A where
  State := M.State × H
  init := { s | s.1 ∈ M.init ∧ s.2 ∈ hist_init }
  next := fun s a ↦ { s' | s'.1 ∈ M.next s.1 a ∧ s'.2 ∈ hist_next s a }

variable (M : Automaton A) (hist_init : Set H) (hist_next : M.State × H → A → Set H)

theorem automata_hist_inf_run_proj {as : ℕ → A} {ss : ℕ → M.State × H}
    (h : InfRun (AutomataHist M hist_init hist_next) as ss) : InfRun M as (Prod.fst ∘ ss) := by
  constructor
  · have h' := h.1
    simp [AutomataHist] at h'
    exact h'.1
  · intro k
    have h' := h.2 k
    simp [AutomataHist] at h'
    exact h'.1

private def MakeHist (as : ℕ → A) (ss : ℕ → M.State) (hs0 : H) (hs' : M.State × H → A -> H) : ℕ → H
  | 0 => hs0
  | k + 1 => hs' (ss k, MakeHist as ss hs0 hs' k) (as k)

theorem automata_hist_inf_run_exists {as : ℕ → A} {ss : ℕ → M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : InfRun M as ss) : ∃ hs : ℕ → H, InfRun (AutomataHist M hist_init hist_next) as (fun k ↦ (ss k, hs k)) := by
  obtain ⟨hs0, h_hs0⟩ := h_init
  choose hs' h_hs' using h_next
  let hs := MakeHist M as ss hs0 hs'
  use hs ; constructor
  · simp [AutomataHist, MakeHist, h.1, hs]
    exact h_hs0
  · intro k
    simp [AutomataHist, MakeHist, hs, h.2 k]
    apply h_hs'

end AutomataHist
