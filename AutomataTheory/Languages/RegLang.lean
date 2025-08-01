/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Sum
import AutomataTheory.Automata.Prod
import AutomataTheory.Automata.PSet
import AutomataTheory.Automata.Concat
import AutomataTheory.Automata.Loop
import AutomataTheory.Automata.Congr

/-!
This file proves various closure properties of regular langauges.
Note that we do require that the automaton accepting a regular language
to have a finite state type.
-/

open Function Set Filter Sum
open scoped Computability

section RegLang

open Classical

variable {A : Type}

def RegLang (L : Set (List A)) :=
  ∃ M : Automaton.{0, 0} A, ∃ acc : Set M.State, Finite M.State ∧ L = M.AcceptedLang acc

theorem reg_lang_union {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∪ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automaton A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (Automaton.Sum M_u), (Automaton.Sum_Acc M_u acc_u)
  constructor
  · have h_fin : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    exact Finite.instSigma
  · ext as
    simp [h_l0, h_l1, accepted_lang_union M_u acc_u, Fin.exists_fin_two, M_u, acc_u]

theorem reg_lang_inter [Inhabited A] {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∩ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automaton A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (Automaton.Prod M_u), (Automaton.Prod_Acc M_u acc_u)
  constructor
  · have h_fin : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    exact Pi.finite
  · ext as
    simp [h_l0, h_l1, accepted_lang_inter M_u acc_u, Fin.forall_fin_two, M_u, acc_u]

theorem reg_lang_compl [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang Lᶜ := by
  obtain ⟨M, acc, h_fin, h_l⟩ := h
  use M.PSet.toNA, (M.PSet_Acc acc)ᶜ
  constructor
  · exact Set.instFinite
  · rw [accepted_lang_compl, accepted_lang_pset, h_l]

theorem reg_lang_concat_ne {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) (h_ne : [] ∉ L1) : RegLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  use (M0.Concat acc0 M1), (inr '' acc1)
  constructor
  · exact Finite.instSum
  · have h_l1' : L1 = L1 \ {[]} := by
      ext al ; simp
      intro h1 h2 ; simp [h2] at h1
      contradiction
    rw [h_l1] at h_l1'
    rw [h_l0, h_l1, h_l1', accepted_lang_concat_ne]

theorem reg_lang_concat_e {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) (h_e : [] ∈ L1) : RegLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  use (M0.Concat acc0 M1), (inl '' acc0 ∪ inr '' acc1)
  constructor
  · exact Finite.instSum
  · have h_l1' : L1 = (L1 \ {[]}) ∪ {[]} := by
      symm ; apply Set.diff_union_of_subset ; simp [h_e]
    have h_l1'' : [] ∉ L1 \ {[]} := by simp
    rw [h_l1] at h_l1' h_l1''
    rw [h_l0, h_l1, h_l1', lang_ConcatFin_union_distrib_right, lang_ConcatFin_epsilon_right,
        accepted_lang_acc_union, accepted_lang_concat_e, accepted_lang_concat_ne, union_comm]

theorem reg_lang_concat [Inhabited A] {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 * L1) := by
  rcases Classical.em ([] ∈ L1) with h_e | h_ne
  · exact reg_lang_concat_e h0 h1 h_e
  . exact reg_lang_concat_ne h0 h1 h_ne

theorem reg_lang_iter [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang L∗ := by
  obtain ⟨M, acc, h_fin, h_l⟩ := h
  use (M.Loop acc), {inl ()}
  constructor
  · exact Finite.instSum
  · simp [h_l, accepted_lang_loop]

theorem reg_lang_fin_idx_congr [Inhabited A] {c : Congruence A}
    (h : Finite (c.QuotType)) (s : c.QuotType) : RegLang (c.EqvCls s) := by
  use c.toDA.toNA, {s}
  constructor
  · exact h
  · symm ; exact accepted_lang_congr s

end RegLang

section BasicRegLang

variable {A : Type}

def M_empty : Automaton A where
  State := Unit
  init := {}
  next := fun _ _ ↦ {}

def acc_empty : Set Unit := {()}

theorem reg_lang_empty : RegLang (∅ : Set (List A)) := by
  use M_empty, acc_empty ; constructor
  · exact Finite.of_fintype Unit
  ext al ; constructor
  · intro h
    simp_all only [mem_empty_iff_false]
  · rintro ⟨n, as, ⟨ss, ⟨h_init, _⟩ ,_⟩, _⟩
    simp [M_empty] at h_init

def M_epsilon : Automaton A where
  State := Unit
  init := {()}
  next := fun _ _ ↦ {}

def acc_epsilon : Set Unit := {()}

theorem reg_lang_epsilon [Inhabited A] : RegLang ({[]} : Set (List A)) := by
  use M_epsilon, acc_epsilon ; constructor
  · exact Finite.of_fintype Unit
  ext al ; constructor
  · simp ; intro h_al
    use 0, (fun k ↦ default) ; simp [h_al]
    use (fun k ↦ ())
    simp [Automaton.FinRun, M_epsilon, acc_epsilon]
  · rintro ⟨n, as, ⟨ss, ⟨h_init, h_next⟩, h_acc⟩, h_al⟩
    suffices h_n : n = 0 by
      simp [h_n] at h_al ; simp [h_al]
    by_contra h_contra
    have h_step := h_next 0 (by omega)
    simp [M_epsilon] at h_step

end BasicRegLang
