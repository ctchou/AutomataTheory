/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import AutomataTheory.AutomataSum
import AutomataTheory.AutomataOI2

open BigOperators Function Set Filter

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
  use (AutomataSum M_u), (AutomataSum_Acc M_u acc_u)
  constructor
  · simp [AutomataSum]
    have h_fin : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
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
  use (AutomataOI2 M_u acc_u), (AutomataOI2_Acc M_u acc_u)
  constructor
  · simp [AutomataOI2, AutomataHist, AutomataProd]
    have h_fin1 : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    have h_fin2 : Finite ((i : Fin 2) → (M_u i).State) := by exact Pi.finite
    exact Finite.instProd
  · ext as
    simp [h_l0, h_l1, accepted_omega_lang_inter2 M_u acc_u, Fin.forall_fin_two, M_u, acc_u]

end OmegaRegLang
