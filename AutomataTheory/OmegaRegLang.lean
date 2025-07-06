/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.AutomataOI2
import AutomataTheory.RegLang

/-!
This file proves various closure properties of ω-regular langauges.
Note that we do require that the automaton accepting an ω-regular language
to have a finite state type.
-/

open Function Set Filter Sum

section OmegaRegLang

variable {A : Type}

def OmegaRegLang (L : Set (ℕ → A)) :=
  ∃ M : Automaton.{0, 0} A, ∃ acc : Set M.State, Finite M.State ∧ L = AcceptedOmegaLang M acc

theorem omega_reg_lang_union {L0 L1 : Set (ℕ → A)}
    (h0 : OmegaRegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (L0 ∪ L1) := by
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
    simp [h_l0, h_l1, accepted_omega_lang_union M_u acc_u, Fin.exists_fin_two, M_u, acc_u]

theorem omega_reg_lang_inter {L0 L1 : Set (ℕ → A)}
    (h0 : OmegaRegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (L0 ∩ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automaton A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (Automaton.OI2 M_u acc_u), (Automaton.OI2_Acc M_u acc_u)
  constructor
  · simp [Automaton.OI2, Automaton.addHist, Automaton.Prod]
    have h_fin1 : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    have h_fin2 : Finite ((i : Fin 2) → (M_u i).State) := by exact Pi.finite
    exact Finite.instProd
  · ext as
    simp [h_l0, h_l1, accepted_omega_lang_inter2 M_u acc_u, Fin.forall_fin_two, M_u, acc_u]

theorem omega_reg_lang_concat {L0 : Set (List A)} {L1 : Set (ℕ → A)}
    (h0 : RegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (ConcatInf L0 L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  use (M0.Concat acc0 M1), (inr '' acc1)
  constructor
  · exact Finite.instSum
  · simp [h_l0, h_l1, accepted_omega_lang_concat]

theorem omega_reg_lang_iter {L : Set (List A)}
    (h : RegLang L) : OmegaRegLang (IterOmega L) := by
  obtain ⟨M, acc, h_fin, h_l⟩ := h
  use (AutomataLoop M acc), {inl ()}
  constructor
  · exact Finite.instSum
  · simp [h_l, accepted_omega_lang_loop]

end OmegaRegLang
