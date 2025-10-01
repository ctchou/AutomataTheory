/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Basic

/-!
The construction of adding a history state component to an NA.
-/

open Function Set Filter Stream'

namespace Automata

section AutomataHist

variable {A H : Type}

/-- Note that in the next state, the history component can depend on both the original
and the history components of the current state, but the original component is unaffected
by the history component of the current state.
-/
def NA.addHist (M : NA A) (hist_init : Set H) (hist_next : M.State × H → A → Set H) : NA A where
  State := M.State × H
  init := { s | s.1 ∈ M.init ∧ s.2 ∈ hist_init }
  next := fun s a ↦ { s' | s'.1 ∈ M.next s.1 a ∧ s'.2 ∈ hist_next s a }

variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}

/-- The original state components of a finite run of the history NA is
a finite run of the original NA.
-/
theorem na_hist_fin_run_proj {n : ℕ} {as : Stream' A} {ss : Stream' (M.State × H)}
    (h : (M.addHist hist_init hist_next).FinRun n as ss) : M.FinRun n as (Prod.fst ∘ ss) := by
  constructor
  · have h' := h.1
    simp [NA.addHist] at h'
    exact h'.1
  · intro k h_k
    have h' := h.2 k h_k
    simp [NA.addHist] at h'
    exact h'.1

/-- The original state components of an infinite run of the history NA is
an infinite run of the original NA.
-/
theorem na_hist_inf_run_proj {as : Stream' A} {ss : Stream' (M.State × H)}
    (h : (M.addHist hist_init hist_next).InfRun as ss) : M.InfRun as (Prod.fst ∘ ss) := by
  constructor
  · have h' := h.1
    simp [NA.addHist] at h'
    exact h'.1
  · intro k
    have h' := h.2 k
    simp [NA.addHist] at h'
    exact h'.1

private def MakeHist (as : Stream' A) (ss : Stream' M.State) (hs0 : H) (hs' : M.State × H → A -> H) : Stream' H
  | 0 => hs0
  | k + 1 => hs' (ss k, MakeHist as ss hs0 hs' k) (as k)

/-- Any finite run of the original NA can be extended to a finite run of
the history NA, assuming that the history component can always "follow along".
-/
theorem na_hist_fin_run_exists {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : M.FinRun n as ss) : ∃ hs : Stream' H, (M.addHist hist_init hist_next).FinRun n as (fun k ↦ (ss k, hs k)) := by
  obtain ⟨hs0, h_hs0⟩ := h_init
  choose hs' h_hs' using h_next
  let hs := MakeHist as ss hs0 hs'
  use hs ; constructor
  · simp [NA.addHist, MakeHist, h.1, hs]
    exact h_hs0
  · intro k h_k
    simp [NA.addHist, MakeHist, hs, h.2 k h_k]
    apply h_hs'

/-- Any infinite run of the original NA can be extended to an infinite run of
the history NA, assuming that the history component can always "follow along".
-/
theorem na_hist_inf_run_exists {as : Stream' A} {ss : Stream' M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : M.InfRun as ss) : ∃ hs : Stream' H, (M.addHist hist_init hist_next).InfRun as (fun k ↦ (ss k, hs k)) := by
  obtain ⟨hs0, h_hs0⟩ := h_init
  choose hs' h_hs' using h_next
  let hs := MakeHist as ss hs0 hs'
  use hs ; constructor
  · simp [NA.addHist, MakeHist, h.1, hs]
    exact h_hs0
  · intro k
    simp [NA.addHist, MakeHist, hs, h.2 k]
    apply h_hs'

end AutomataHist
