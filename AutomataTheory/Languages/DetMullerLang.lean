/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.DetConcat
import AutomataTheory.Automata.DetProd
import AutomataTheory.Languages.RegLang

/-!
This file proves various closure properties of deterministic Muller
(ω-)langauges.  Note that we do require that the Muller automata
to have finite state types.
-/

open Function Set

section DetMullerLang

variable {A : Type}

/-- An ω-language is deterministic Muller iff it is accepted by a
finite-state deterministic Muller automaton.
-/
def DetMullerLang (L : Set (ℕ → A)) :=
  ∃ M : Automata.DA A, ∃ accSet : Set (Set M.State),
  Finite M.State ∧ L = { as | M.MullerAccept accSet as }

/-- Deterministic Muller languages are closed under complementation.
-/
theorem det_muller_lang_compl {L : Set (ℕ → A)}
    (h : DetMullerLang L) : DetMullerLang Lᶜ := by
  obtain ⟨M, accSet, h_fin, rfl⟩ := h
  use M, accSetᶜ ; constructor
  · exact h_fin
  · ext as ; simp [Automata.det_muller_accept_compl]

/-- Deterministic Muller languages are closed under intersection.
-/
theorem det_muller_lang_inter {L0 L1 : Set (ℕ → A)}
    (h0 : DetMullerLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 ∩ L1) := by
  obtain ⟨M0, accSet0, h_fin0, rfl⟩ := h0
  obtain ⟨M1, accSet1, h_fin1, rfl⟩ := h1
  let M : Fin 2 → Automata.DA A
    | 0 => M0
    | 1 => M1
  let accSet : (i : Fin 2) → Set (Set (M i).State)
    | 0 => accSet0
    | 1 => accSet1
  use (Automata.DA.Prod M), (Automata.DA.MullerAcc_Inter M accSet)
  have : ∀ i, Finite (M i).State := by simp [Fin.forall_fin_two] ; grind
  constructor
  · exact Automata.da_prod_finite M
  · ext as
    simp [Automata.det_muller_accept_inter M accSet as, Fin.forall_fin_two] ; grind

/-- Deterministic Muller languages are closed under union.
-/
theorem det_muller_lang_union {L0 L1 : Set (ℕ → A)}
    (h0 : DetMullerLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 ∪ L1) := by
  obtain ⟨M0, accSet0, h_fin0, rfl⟩ := h0
  obtain ⟨M1, accSet1, h_fin1, rfl⟩ := h1
  let M : Fin 2 → Automata.DA A
    | 0 => M0
    | 1 => M1
  let accSet : (i : Fin 2) → Set (Set (M i).State)
    | 0 => accSet0
    | 1 => accSet1
  use (Automata.DA.Prod M), (Automata.DA.MullerAcc_Union M accSet)
  have : ∀ i, Finite (M i).State := by simp [Fin.forall_fin_two] ; grind
  constructor
  · exact Automata.da_prod_finite M
  · ext as
    simp [Automata.det_muller_accept_union M accSet as, Fin.exists_fin_two] ; grind

/-- The ω-limit of a regular language is a deterministic Muller language.
-/
theorem det_muller_lang_omega_limit {L : Set (List A)}
    (h : RegLang L) : DetMullerLang L↗ω := by
  obtain ⟨M, acc, h_fin, rfl⟩ := reg_lang_det_accept h
  obtain ⟨accSet, h_acc⟩ := Automata.det_muller_accept_omega_limit M acc
  use M, accSet ; constructor
  · exact h_fin
  · simp [h_acc]

/-- The concatenation of a regular language and a deterministic Muller language
is a deterministic Muller language.
-/
theorem det_muller_lang_concat {L0 : Set (List A)} {L1 : Set (ℕ → A)}
    (h0 : RegLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, rfl⟩ := reg_lang_det_accept h0
  obtain ⟨M1, accSet1, h_fin1, rfl⟩ := h1
  use (M0.Concat acc0 M1), (Automata.DA.MullerAcc_Concat M0 acc0 M1 accSet1)
  constructor
  · apply Finite.instProd
  · ext as ; constructor
    · rintro ⟨al0, as1, ⟨n, as0, h_as0, h_al0⟩, h_as1, h_as⟩
      have h_acc0 : M0.toNA.FinAccept acc0 n as := by
        obtain ⟨ss0, h_run0, h_acc0⟩ := h_as0
        use ss0 ; simp [h_as, h_acc0] ; constructor
        · exact h_run0.1
        intro k h_k ; simp [h_al0, instAppendListInf, AppendListInf, h_k, h_run0.2 k h_k]
      have h_acc1 : M1.MullerAccept accSet1 (as <<< n) := by
        have h_len0 : n = al0.length := by simp [h_al0]
        simp [h_as, h_len0, ← suffixFrom_listLength_AppendListInf] ; exact h_as1
      exact Automata.da_concat_to_muller_accept M0 acc0 M1 accSet1 as n h_acc0 h_acc1
    · intro h_acc
      obtain ⟨n, h_acc0, h_acc1⟩ := Automata.da_concat_of_muller_accept M0 acc0 M1 accSet1 as h_acc
      use (List.ofFn (fun k : Fin n ↦ as k)), (as <<< n)
      simp [h_acc1, ← appendListInf_ofFnPrefix_SuffixFrom] ; use n, as

end DetMullerLang
