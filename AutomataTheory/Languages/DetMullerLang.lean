/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.DetConcat
import AutomataTheory.Automata.DetProd
import AutomataTheory.Languages.OmegaRegLang

/-!
This file proves various closure properties of deterministic Muller
(ω-)langauges.  Note that we do require that the Muller automata
to have finite state types.
-/

open Function Set
open scoped Computability

section DetMullerLang

variable {A : Type}

/-- An ω-language is deterministic Muller iff it is accepted by a
finite-state deterministic Muller automaton.
-/
def DetMullerLang (L : Set (ℕ → A)) :=
  ∃ M : Automata.DA A, ∃ accSet : Set (Set M.State),
  Finite M.State ∧ L = { as | M.MullerAccept accSet as }

/-- The language `∅` is a deterministic Muller language.
-/
theorem det_muller_lang_empty :
    DetMullerLang (∅ : Set (ℕ → A)) := by
  let M := Automata.DA.mk (A := A) Unit () (fun _ _ ↦ ())
  use M, ∅ ; constructor
  · exact Finite.of_fintype Unit
  ext as ; simp [Automata.DA.MullerAccept]

/-- The language `univ` is a deterministic Muller language.
-/
theorem det_muller_lang_univ :
    DetMullerLang (univ : Set (ℕ → A)) := by
  let M := Automata.DA.mk (A := A) Unit () (fun _ _ ↦ ())
  use M, {{()}} ; constructor
  · exact Finite.of_fintype Unit
  ext as ; simp [Automata.DA.MullerAccept]
  have h : M.DetRun as = fun _ ↦ () := by
    ext k ; induction' k <;> simp [Automata.DA.DetRun, M]
  ext s ; simp [h, InfOcc]

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

/-- Deterministic Muller languages are closed under finite bounded indexed intersection.
-/
theorem det_muller_lang_biInter {I : Type} [Finite I] {s : Set I} {L : I → Set (ℕ → A)}
    (h : ∀ i ∈ s, DetMullerLang (L i)) : DetMullerLang (⋂ i ∈ s, L i) := by
  generalize h_n : s.ncard = n
  induction' n with n h_ind generalizing s
  . obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp [det_muller_lang_univ]
  obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
  simp ; apply det_muller_lang_inter <;> grind

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

/-- Deterministic Muller languages are closed under finite bounded indexed union.
-/
theorem det_muller_lang_biUnion {I : Type} [Finite I] {s : Set I} {L : I → Set (ℕ → A)}
    (h : ∀ i ∈ s, DetMullerLang (L i)) : DetMullerLang (⋃ i ∈ s, L i) := by
  generalize h_n : s.ncard = n
  induction' n with n h_ind generalizing s
  . obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp [det_muller_lang_empty]
  obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
  simp ; apply det_muller_lang_union <;> grind

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
        simp [h_as, h_len0, suffixFrom_listLength_AppendListInf] ; exact h_as1
      exact Automata.da_concat_to_muller_accept M0 acc0 M1 accSet1 as n h_acc0 h_acc1
    · intro h_acc
      obtain ⟨n, h_acc0, h_acc1⟩ := Automata.da_concat_of_muller_accept M0 acc0 M1 accSet1 as h_acc
      use (as ⇊ 0 n), (as <<< n)
      simp [h_acc1, appendListInf_FinSubseq_SuffixFrom]
      use n, as ; simp [h_acc0] ; rfl

/-- Every deterministic Muller language is an ω-regular language.
-/
theorem det_muller_lang_imp_omega_reg_lang [Inhabited A] {L : Set (ℕ → A)}
    (h : DetMullerLang L) : OmegaRegLang L := by
  obtain ⟨M, accSet, h_fin, rfl⟩ := h
  rw [Automata.det_muller_accept_boolean_form]
  have h_reg : ∀ s, RegLang (M.toNA.AcceptedLang {s}) := by
    intro s ; use M.toNA, {s} ; simp [Automata.DA.toNA, h_fin]
  apply omega_reg_lang_biUnion ; intro acc h_acc
  apply omega_reg_lang_inter <;> apply omega_reg_lang_biInter <;> intro s h_s
  · apply omega_reg_lang_omega_limit
    simp [h_reg]
  · apply omega_reg_lang_compl ; apply omega_reg_lang_omega_limit
    simp [h_reg]

/-- Every deterministic Muller language is an ω-regular language.
-/
theorem omega_reg_lang_imp_det_muller_lang [Inhabited A] {L : Set (ℕ → A)}
    (h : OmegaRegLang L) : DetMullerLang L := by
  obtain ⟨n, U, V, h_reg, rfl⟩ := omega_reg_lang_iff_finite_union_form.mp h
  rw [← biUnion_univ] ; apply det_muller_lang_biUnion
  intro i _ ; apply det_muller_lang_concat
  · exact (h_reg i).1
  · have h_v := (h_reg i).2
    obtain ⟨W, h_w, h_omega⟩ := choueka_lemma h_v
    rw [h_omega] ; apply det_muller_lang_concat
    · exact reg_lang_iter h_v
    · exact det_muller_lang_omega_limit h_w

/-- McNaughton's theorem: An ω-language is ω-regular
if and only if it is deterministic Muller.
-/
theorem omega_reg_lang_iff_det_muller_lang [Inhabited A] {L : Set (ℕ → A)} :
    OmegaRegLang L ↔ DetMullerLang L := by
  constructor
  · intro h ; exact omega_reg_lang_imp_det_muller_lang h
  · intro h ; exact det_muller_lang_imp_omega_reg_lang h

end DetMullerLang
