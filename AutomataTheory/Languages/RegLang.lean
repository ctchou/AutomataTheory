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
Note that we do require that the Automata.NA accepting a regular language
to have a finite state type.
-/

open Function Set Filter Sum
open scoped Computability

section RegLang

open Classical

variable {A : Type}

/-- A language is regular iff it is accepted by a finite-state Automata.NA.
-/
def RegLang (L : Set (List A)) :=
  ∃ M : Automata.NA A, ∃ acc : Set M.State, Finite M.State ∧ M.AcceptedLang acc = L

/-- The language `∅` is regular.
-/
theorem reg_lang_empty :
    RegLang (∅ : Set (List A)) := by
  let M := Automata.NA.mk (A := A) Unit ∅ (fun _ _ ↦ ∅)
  use M, ∅ ; constructor
  · exact Finite.of_fintype Unit
  ext al ; simp
  rintro ⟨n, as, ⟨ss, _, h_acc⟩, rfl⟩ ; simp at h_acc

/-- The language `{[]}` is regular.
-/
theorem reg_lang_epsilon [Inhabited A] :
    RegLang ({[]} : Set (List A)) := by
  let M := Automata.NA.mk (A := A) Unit {()} (fun _ _ ↦ {})
  use M, {()} ; constructor
  · exact Finite.of_fintype Unit
  ext al ; simp ; constructor
  · rintro ⟨n, as, ⟨ss, ⟨h_init, h_next⟩, h_acc⟩, h_al⟩
    suffices h_n : n = 0 by simp [← h_al, h_n, extract_nil]
    by_contra ; specialize h_next 0 (by omega) ; simp [M] at h_next
  · rintro ⟨rfl⟩
    use 0, (fun k ↦ default) ; simp [extract_nil]
    use (fun k ↦ ()) ; simp [M, Automata.NA.FinRun]

/-- The language `univ` is regular.
-/
theorem reg_lang_univ [Inhabited A] :
    RegLang (univ : Set (List A)) := by
  let M := Automata.NA.mk (A := A) Unit {()} (fun _ _ ↦ {()})
  use M, {()} ; constructor
  · exact Finite.of_fintype Unit
  ext al ; simp
  use al.length, al.padDefault ; simp [extract_padDefault]
  use (fun _ ↦ ()) ; simp [M, Automata.NA.FinRun]

/-- Regular languages are closed under union.
-/
theorem reg_lang_union {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∪ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automata.NA A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (Automata.NA.Sum M_u), (Automata.NA.Sum_Acc M_u acc_u)
  constructor
  · have h_fin : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    exact Finite.instSigma
  · ext as
    simp [h_l0, h_l1, Automata.acc_lang_union M_u acc_u, Fin.exists_fin_two, M_u, acc_u]

/-- Regular languages are closed under finite bounded indexed union.
-/
theorem reg_lang_biUnion {I : Type} [Finite I] {s : Set I} {L : I → Set (List A)}
    (h : ∀ i ∈ s, RegLang (L i)) : RegLang (⋃ i ∈ s, L i) := by
  generalize h_n : s.ncard = n
  induction' n with n h_ind generalizing s
  . obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp [reg_lang_empty]
  obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
  simp ; apply reg_lang_union <;> grind

/-- Regular languages are closed under intersection.
-/
theorem reg_lang_inter [Inhabited A] {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∩ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automata.NA A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (Automata.NA.Prod M_u), (Automata.NA.Prod_Acc M_u acc_u)
  constructor
  · have h_fin : ∀ i, Finite (M_u i).State := by simp [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    exact Pi.finite
  · ext as
    simp [h_l0, h_l1, Automata.acc_lang_inter M_u acc_u, Fin.forall_fin_two, M_u, acc_u]

/-- Regular languages are closed under finite bounded indexed intersection.
-/
theorem reg_lang_biInter [Inhabited A] {I : Type} [Finite I] {s : Set I} {L : I → Set (List A)}
    (h : ∀ i ∈ s, RegLang (L i)) : RegLang (⋂ i ∈ s, L i) := by
  generalize h_n : s.ncard = n
  induction' n with n h_ind generalizing s
  . obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp [reg_lang_univ]
  obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
  simp ; apply reg_lang_inter <;> grind

/-- A regular language is always accepted by a deterministic finite automaton.
-/
theorem reg_lang_det_accept {L : Set (List A)} (h : RegLang L) :
    ∃ M : Automata.DA A, ∃ acc : Set M.State, Finite M.State ∧ L = M.toNA.AcceptedLang acc := by
  obtain ⟨M, acc, h_fin, rfl⟩ := h
  use M.PSet, (M.PSet_Acc acc) ; constructor
  · exact Set.instFinite
  · symm ; exact Automata.acc_lang_pset M acc

/-- Regular languages are closed under complementation.
-/
theorem reg_lang_compl [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang Lᶜ := by
  obtain ⟨M, acc, h_fin, h_l⟩ := reg_lang_det_accept h
  use M.toNA, accᶜ ; constructor
  · exact h_fin
  · simp [Automata.da_acc_lang_compl, h_l]

/-- Helper lemma for `reg_lang_concat` below.
-/
lemma reg_lang_concat_ne {L0 L1 : Set (List A)}
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
    rw [← h_l1] at h_l1'
    rw [← h_l0, ← h_l1, h_l1', Automata.acc_lang_concat_ne]

/-- Helper lemma for `reg_lang_concat` below.
-/
lemma reg_lang_concat_e {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) (h_e : [] ∈ L1) : RegLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  use (M0.Concat acc0 M1), (inl '' acc0 ∪ inr '' acc1)
  constructor
  · exact Finite.instSum
  · have h_l1' : L1 = (L1 \ {[]}) ∪ {[]} := by
      symm ; apply Set.diff_union_of_subset ; simp [h_e]
    have h_l1'' : [] ∉ L1 \ {[]} := by simp
    rw [← h_l1] at h_l1' h_l1''
    rw [← h_l0, ← h_l1, h_l1', ConcatFin_union_distrib, ConcatFin_epsilon,
        Automata.acc_lang_acc_union, Automata.acc_lang_concat_e, Automata.acc_lang_concat_ne, union_comm]

/-- Regular languages are closed under concatenation.
-/
theorem reg_lang_concat [Inhabited A] {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 * L1) := by
  rcases Classical.em ([] ∈ L1) with h_e | h_ne
  · exact reg_lang_concat_e h0 h1 h_e
  . exact reg_lang_concat_ne h0 h1 h_ne

/-- Regular languages are closed under Kleene star.
-/
theorem reg_lang_iter [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang L∗ := by
  obtain ⟨M, acc, h_fin, h_l⟩ := h
  use (M.Loop acc), {inl ()}
  constructor
  · exact Finite.instSum
  · simp [h_l, Automata.acc_lang_loop]

/-- If a (right) congruence is of finite index,
then each of its equivalence classes is regular.
-/
theorem reg_lang_fin_idx_congr [Inhabited A] {c : Congruence A}
    (h : Finite (c.QuotType)) (s : c.QuotType) : RegLang (c.EqvCls s) := by
  use c.toDA.toNA, {s}
  constructor
  · exact h
  · exact acc_lang_congr s

end RegLang
