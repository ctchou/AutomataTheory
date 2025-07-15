/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.OI2
import AutomataTheory.Automata.Pair

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
  use (M.Loop acc), {inl ()}
  constructor
  · exact Finite.instSum
  · simp [h_l, accepted_omega_lang_loop]

theorem omega_reg_lang_iff_finite_union_form [Inhabited A] {L : Set (ℕ → A)} :
    OmegaRegLang L ↔
    ∃ n : ℕ, ∃ U V : Fin n → Set (List A),
      (∀ i, RegLang (U i) ∧ RegLang (V i)) ∧ L = ⋃ i, ConcatInf (U i) (IterOmega (V i)) := by
  constructor
  · rintro ⟨M, acc, h_fin, rfl⟩
    rw [omega_reg_lang_finite_union_form]
    have eq_init : Fin (Nat.card ↑M.init) ≃ ↑M.init := by exact (Finite.equivFin ↑Automaton.init).symm
    have eq_acc : Fin (Nat.card ↑acc) ≃ ↑acc := by exact (Finite.equivFin ↑acc).symm
    have eq_prod := Equiv.prodCongr eq_init eq_acc
    have eq_fin_prod := (finProdFinEquiv (m := Nat.card ↑M.init) (n := Nat.card ↑acc)).symm
    have eq := Equiv.trans eq_fin_prod eq_prod
    use ((Nat.card ↑M.init) * (Nat.card ↑acc))
    use (fun i ↦ M.PairLang (eq i).1 (eq i).2)
    use (fun i ↦ M.PairLang (eq i).2 (eq i).2)
    constructor
    · intro i ; constructor <;> exact pair_lang_regular
    · ext as ; simp ; constructor
      · rintro ⟨s0, h_s0, sa, h_sa, h_mem⟩
        use (eq.invFun (⟨s0, h_s0⟩, ⟨sa, h_sa⟩))
        simp [h_mem]
      · rintro ⟨i, h_mem⟩
        use (eq i).1 ; simp [(eq i).1.property]
        use (eq i).2 ; simp [(eq i).2.property, h_mem]
  · rintro ⟨n, U, V, h_reg, rfl⟩
    induction' n with n h_ind
    · use { State := Unit, init := {}, next := fun _ _ ↦ {} }, {} ; constructor
      · exact Finite.of_fintype Unit
      ext as ; simp ; by_contra h_contra
      obtain ⟨ss, h_run, _⟩ := h_contra
      simp [InfRun] at h_run
    let U' := (fun i : Fin n ↦ U i.castSucc)
    let V' := (fun i : Fin n ↦ V i.castSucc)
    specialize h_ind U' V' (by intro i ; simp [U', V', h_reg i.castSucc])
    have h : (⋃ i, ConcatInf (U i) (IterOmega (V i)))
           = (⋃ i, ConcatInf (U' i) (IterOmega (V' i))) ∪ ConcatInf (U (Fin.last n)) (IterOmega (V (Fin.last n))) := by
      ext as ; simp ; constructor
      · rintro ⟨i, h_i⟩
        obtain (⟨i', rfl⟩ | rfl) := Fin.eq_castSucc_or_eq_last i
        . left ; use i'
        . right ; assumption
      · rintro (⟨i, h_i⟩ | h_n)
        · use i.castSucc
        · use (Fin.last n)
    rw [h]
    apply omega_reg_lang_union h_ind
    apply omega_reg_lang_concat
    · exact (h_reg (Fin.last n)).1
    · apply omega_reg_lang_iter
      exact (h_reg (Fin.last n)).2

end OmegaRegLang
