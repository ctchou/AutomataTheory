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
import AutomataTheory.AutomataProd

open BigOperators Function Set Filter

section RegLang

variable {A : Type}

def RegLang (L : Set (List A)) :=
  ∃ M : Automata.{0, 0} A, ∃ acc : Set M.State, Finite M.State ∧ L = AcceptedLang M acc

theorem _reg_lang_union {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∪ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automata A
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
    simp [h_l0, h_l1, accepted_lang_union M_u acc_u, Fin.exists_fin_two, M_u, acc_u]

theorem _reg_lang_inter {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∩ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automata A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (AutomataProd M_u), (AutomataProd_Acc M_u acc_u)
  constructor
  · simp [AutomataProd]
    have h_fin : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    exact Pi.finite
  · ext as
    simp [h_l0, h_l1, accepted_lang_inter M_u acc_u, Fin.forall_fin_two, M_u, acc_u]

end RegLang
