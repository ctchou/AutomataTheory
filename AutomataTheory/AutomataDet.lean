/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import AutomataTheory.AutomataBasic

open BigOperators Function Set Filter

section DetAutomata

class DetAutomata (A : Type*) extends Automata A where
  get_init : State
  get_next : State → A → State
  det_init : init = {get_init}
  det_next : ∀ s a, next s a = {get_next s a}

variable {A : Type*}

def MakeInfRun (M : DetAutomata A) (as : ℕ → A) : ℕ → M.State
  | 0 => M.get_init
  | k + 1 => M.get_next (MakeInfRun M as k) (as k)

variable (M : DetAutomata A)

theorem det_automata_inf_run_exists (as : ℕ → A) :
    InfRun M.toAutomata as (MakeInfRun M as) := by
  constructor
  · simp [M.det_init, MakeInfRun]
  · simp [M.det_next, MakeInfRun]

theorem det_automata_inf_run_unique (as : ℕ → A) :
    ∀ ss, InfRun M.toAutomata as ss → ss = MakeInfRun M as := by
  intro ss h_run
  ext k ; induction' k with k h_ind
  · have h_init := h_run.1
    simp [M.det_init] at h_init
    assumption
  · rw [MakeInfRun, ← h_ind]
    have h_next := h_run.2 k
    simp [M.det_next] at h_next
    assumption

def MakeFinRun (M : DetAutomata A) (n : ℕ) (as : Fin n → A) (k : Fin (n + 1)) : M.State :=
  if h : k > 0 then
    have h1 : k - 1 < k := by exact Fin.sub_one_lt_iff.mpr h
    have h2 : k - 1 ≠ Fin.last n := by exact Fin.ne_last_of_lt h1
    M.get_next (MakeFinRun M n as (k - 1)) (as (Fin.castPred (k - 1) h2))
  else M.get_init

theorem det_automata_fin_run_exists (n : ℕ) (as : Fin n → A) :
    FinRun M.toAutomata n as (MakeFinRun M n as) := by
  constructor
  · simp [M.det_init, MakeFinRun]
  · intro k ; simp [M.det_next]
    rw [MakeFinRun] ; simp
    have h1 : k.succ - 1 = k.castSucc := by rw [sub_eq_iff_eq_add] ; simp
    congr ; simp [h1]

theorem det_automata_fin_run_unique (n : ℕ) (as : Fin n → A) :
    ∀ ss, FinRun M.toAutomata n as ss → ss = MakeFinRun M n as := by
  intro ss h_run
  ext k ; induction' k using Fin.induction with k h_ind
  · have h_init := h_run.1
    simp [M.det_init] at h_init
    simp [MakeFinRun, h_init]
  · have h1 : k.succ > 0 := by exact Fin.succ_pos k
    have h2 : k.succ - 1 = k.castSucc := by rw [sub_eq_iff_eq_add] ; simp
    rw [MakeFinRun] ; simp [h1, h2, ← h_ind]
    have h_next := h_run.2 k
    simp [M.det_next] at h_next
    assumption

end DetAutomata

section AcceptedLangCompl

variable {A : Type*} (M : DetAutomata A) (acc : Set M.State)

private lemma ofFn_eq_imp_eq {n : ℕ} {as as' : Fin n → A}
    (h : List.ofFn as = List.ofFn as') : as = as' := by
  ext k
  have h_k : as k = (List.ofFn as)[k] := by simp [List.getElem_ofFn]
  have h_k' : as' k = (List.ofFn as')[k] := by simp [List.getElem_ofFn]
  rw [h_k, h_k'] ; simp [h]

theorem accepted_lang_compl :
    AcceptedLang M.toAutomata accᶜ = (AcceptedLang M.toAutomata acc)ᶜ := by
  ext al
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    rintro ⟨n', as', ⟨ss', h_run', h_acc'⟩, h_al'⟩
    have h_n_eq : n' = n := by
      rw [← List.length_ofFn (f := as'), ← List.length_ofFn (f := as), ← h_al', ← h_al]
    obtain ⟨rfl⟩ := h_n_eq
    have h_as_eq : as' = as := by apply ofFn_eq_imp_eq ; rw [← h_al, ← h_al']
    obtain ⟨rfl⟩ := h_as_eq
    have h_ss := det_automata_fin_run_unique M n as ss h_run
    have h_ss' := det_automata_fin_run_unique M n as ss' h_run'
    have h_ss_eq : ss' = ss := by simp [h_ss, h_ss']
    obtain ⟨rfl⟩ := h_ss_eq
    contradiction
  · intro h_compl
    let n := al.length
    let as := fun k : Fin n ↦ al[k]
    have h_al : al = List.ofFn as := by symm ; exact List.ofFn_getElem al
    use n, as ; simp [h_al]
    let ss := MakeFinRun M n as
    have h_run : FinRun DetAutomata.toAutomata n as ss := by exact det_automata_fin_run_exists M n as
    use ss ; constructor
    · exact h_run
    intro h_acc
    have : al ∈ (AcceptedLang DetAutomata.toAutomata acc) := by
      use n, as ; simp [h_al] ; use! ss
    contradiction

end AcceptedLangCompl

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

-- theorem automata_pset_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :
--     FinRun M n as ss ↔ FinRun (AutomataPSet M).toAutomata n as (fun k : Fin (n + 1) ↦ {s | s = ss k}) := by
--   sorry

end AutomataPSet

-- def MakeFinRun (M : DetAutomata A) (n : ℕ) (as : Fin n → A) : Fin (n + 1) → M.State
--   | 0 => M.get_init
--   | ⟨k + 1, _⟩ => M.get_next (MakeFinRun M n as ⟨k, by omega⟩) (as ⟨k, by omega⟩)

-- def MakeFinRun (M : DetAutomata A) (n : ℕ) (as : Fin n → A) : Fin (n + 1) → M.State :=
--   match n with
--   | 0 => fun _ ↦ M.get_init
--   | _ + 1 =>
--     let as' := fun k : ℕ ↦ if k < n + 1 then as k else as 0
--     fun k ↦ MakeInfRun M as' k.toNat

-- def Deterministic (M : Automata A) : Prop :=
--   (∃ s0, M.init = {s0}) ∧ (∀ s a, ∃ s', M.next s a = {s'})
