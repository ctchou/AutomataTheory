/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Pair
import AutomataTheory.Mathlib.InfGraphRamsey

/-!
The theory of an automaton-based congruence used by J.R. Büchi to
prove the closure of ω-regular langauges under complementation.
-/

open Function Set Filter

section BuchiCongrBasic

variable {A : Type}

def Automaton.BuchiCongr (M : Automaton A) (acc : Set M.State) : Congruence A where
  eq.r u v := ∀ s s' : M.State,
    (u ∈ M.PairLang s s' ↔ v ∈ M.PairLang s s') ∧ (u ∈ M.PairAccLang acc s s' ↔ v ∈ M.PairAccLang acc s s')
  eq.iseqv.refl := by simp
  eq.iseqv.symm := by intro u v h s s' ; simp_all only [and_self]
  eq.iseqv.trans := by intro u v w h1 h2 s s' ; simp_all only [and_self]
  right_congr := by
    intro u v h w s s'
    constructor <;> [constructor ; constructor] <;> intro h'
    · obtain ⟨t, h_u, h_w⟩ := pair_lang_split h'
      have h_v := (h s t).1.mp h_u
      exact pair_lang_concat h_v h_w
    · obtain ⟨t, h_v, h_w⟩ := pair_lang_split h'
      have h_u := (h s t).1.mpr h_v
      exact pair_lang_concat h_u h_w
    · obtain ⟨t, (⟨h_u, h_w⟩ | ⟨h_u, h_w⟩)⟩ := pair_acc_lang_split h'
      · have h_v := (h s t).2.mp h_u
        exact pair_acc_lang_concat_0 h_v h_w
      · have h_v := (h s t).1.mp h_u
        exact pair_acc_lang_concat_1 h_v h_w
    · obtain ⟨t, (⟨h_v, h_w⟩ | ⟨h_v, h_w⟩)⟩ := pair_acc_lang_split h'
      · have h_u := (h s t).2.mpr h_v
        exact pair_acc_lang_concat_0 h_u h_w
      · have h_u := (h s t).1.mpr h_v
        exact pair_acc_lang_concat_1 h_u h_w

variable {M : Automaton A} {acc : Set M.State}

theorem buchi_congr_saturates : (M.BuchiCongr acc).Saturates (M.AcceptedOmegaLang acc) := by
  rintro p q ⟨as, h_congr, ss, ⟨h_init, h_next⟩, h_acc⟩ as' h_congr'
  obtain ⟨φ, h_mono, h_eqv_p, h_eqv_q⟩ := congruence_mem_concat_omega_lang h_congr
  obtain ⟨φ', h_mono', h_eqv_p', h_eqv_q'⟩ := congruence_mem_concat_omega_lang h_congr'
  have h_congr_p := congruence_same_eqvcls_imp_eq h_eqv_p h_eqv_p'
  have h_congr_q := fun m ↦ congruence_same_eqvcls_imp_eq (h_eqv_q m) (h_eqv_q' m)
  have h_pair_0 := pair_lang_fin_subseq h_next (show 0 ≤ φ 0 by omega)
  have h_pair_1 := fun m ↦ pair_lang_fin_subseq h_next (le_of_lt <| h_mono (show m < m + 1 by omega))
  have h_pair_0' := (h_congr_p (ss 0) (ss (φ 0))).1.mp <| h_pair_0
  have h_pair_1' := fun m ↦ (h_congr_q m (ss (φ m)) (ss (φ (m + 1)))).1.mp <| h_pair_1 m
  have h_inf := pair_acc_lang_frequently_from_run h_next h_acc h_mono
  have h_inf' : ∃ᶠ m in atTop, FinSubseq as' (φ' m) (φ' (m + 1)) ∈ M.PairAccLang acc (ss (φ m)) (ss (φ (m + 1))) := by
    apply Frequently.mono h_inf ; intro m
    exact (h_congr_q m (ss (φ m)) (ss (φ (m + 1)))).2.mp
  obtain ⟨ss0', h_ss_0, h_ss_φ0, h_next0'⟩ := h_pair_0'
  simp [FinSubseq] at h_ss_φ0 h_next0'
  have h_lem1 : ∀ m, FinSubseq (fun k ↦ as' (k + φ' 0)) (φ' m - φ' 0) (φ' (m + 1) - φ' 0)
      = FinSubseq as' (φ' m) (φ' (m + 1)) := by
    intro m
    have : φ' 0 ≤ φ' m := by simp [StrictMono.le_iff_le h_mono']
    simp [FinSubseq, add_assoc, (show φ' m - φ' 0 + φ' 0 = φ' m by omega),
      (show φ' (m + 1) - φ' 0 - (φ' m - φ' 0) = φ' (m + 1) - φ' m by omega)]
  obtain ⟨ss1', h_ss1', h_next1', h_acc1'⟩ := pair_acc_lang_frequently_to_run
    (acc := acc) (φ := (φ' · - φ' 0)) (as := fun k ↦ as' (k + φ' 0))
    (ss' := fun k ↦ ss (φ k)) (base_zero_strict_mono h_mono') (base_zero_shift φ')
    (by simp [h_lem1, h_pair_1'])
    (by simp [h_lem1, h_inf'])
  use (fun k ↦ if k < φ' 0 then ss0' k else ss1' (k - φ' 0))
  constructor
  · constructor
    · rcases (show φ' 0 = 0 ∨ φ' 0 > 0 by omega) with h_k | h_k
      · simp [h_k] ; grind
      · grind
    intro k
    rcases (show k + 1 < φ' 0 ∨ k + 1 = φ' 0 ∨ k + 1 > φ' 0 by omega) with h_k | h_k | h_k
    · grind
    · have h_k' : k < φ' 0 := by omega
      have h1 := h_ss1' 0
      simp at h1
      have h2 := h_next0' k h_k'
      simp [h_k, h_ss_φ0] at h2
      simp [h_k, h_k', h1, h2]
    · simp [(show ¬ k < φ' 0 by omega), (show ¬ k + 1 < φ' 0 by omega)]
      have h1 := h_next1' (k - φ' 0)
      simp [(show k - φ' 0 + φ' 0 = k by omega)] at h1
      simp [(show k + 1 - φ' 0 = k - φ' 0 + 1 by omega), h1]
  · simp [Filter.frequently_atTop] at h_acc1' ⊢
    intro k0
    obtain ⟨k1, h_k1, h_k1_acc⟩ := h_acc1' (k0 + φ' 0)
    use (k1 + φ' 0)
    simp [(show k0 ≤ k1 + φ' 0 by omega), h_k1_acc]

end BuchiCongrBasic

section BuchiCongrFinite

open Classical

variable {A : Type}

noncomputable def Automaton.BuchiCongrParam (M : Automaton A) (acc : Set M.State)
    (π : M.State → M.State → Prop × Prop) : (M.BuchiCongr acc).QuotType :=
  if h : ∃ u, ∀ s s', ((π s s').1 ↔ u ∈ M.PairLang s s') ∧ ((π s s').2 ↔ u ∈ M.PairAccLang acc s s')
  then ⟦ choose h ⟧
  else ⟦ [] ⟧

variable {M : Automaton A} {acc : Set M.State}

theorem buchi_congr_param_surjective : Surjective (M.BuchiCongrParam acc) := by
  intro q
  let π s s' := (q.out ∈ M.PairLang s s', q.out ∈ M.PairAccLang acc s s')
  have h : ∃ u, ∀ s s', ((π s s').1 ↔ u ∈ M.PairLang s s') ∧ ((π s s').2 ↔ u ∈ M.PairAccLang acc s s') := by
    use q.out ; intro s s' ; simp [π]
  use π
  simp [Automaton.BuchiCongrParam, h]
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  intro s s'
  have h1 := choose_spec h s s'
  simp [π] at h1
  simp [h1]

theorem buchi_congr_finite_index [Finite M.State] : Finite (M.BuchiCongr acc).QuotType := by
  exact Finite.of_surjective (M.BuchiCongrParam acc) buchi_congr_param_surjective

lemma strict_mono_of_infinite {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns := by
  use (Nat.nth (· ∈ ns)) ; constructor
  · exact Nat.nth_strictMono h
  · exact Nat.range_nth_of_infinite h

theorem buchi_congr_ample [Finite M.State] : (M.BuchiCongr acc).Ample := by
  intro as
  have : Finite (M.BuchiCongr acc).QuotType := buchi_congr_finite_index
  let color (t : Finset ℕ) : (M.BuchiCongr acc).QuotType :=
    if h : t.Nonempty then ⟦ FinSubseq as (t.min' h) (t.max' h) ⟧ else ⟦ [] ⟧
  obtain ⟨q, ns, h_ns, h_color⟩ := inf_graph_ramsey color
  obtain ⟨φ, h_mono, rfl⟩ := strict_mono_of_infinite h_ns
  let p : (M.BuchiCongr acc).QuotType := ⟦ FinSubseq as 0 (φ 0) ⟧
  use p, q, (FinSubseq as 0 (φ 0)), (SuffixFrom (φ 0) as) ; constructorm* _ ∧ _
  · simp [Congruence.EqvCls, p]
  · use (φ · - φ 0) ; simp [base_zero_strict_mono h_mono]
    intro m
    have h_lem1 : FinSubseq (SuffixFrom (φ 0) as) (φ m - φ 0) (φ (m + 1) - φ 0) = FinSubseq as (φ m) (φ (m + 1)) := by
      have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le h_mono]
      simp [FinSubseq, SuffixFrom, add_assoc, (show φ m - φ 0 + φ 0 = φ m by omega),
        (show φ (m + 1) - φ 0 - (φ m - φ 0) = φ (m + 1) - φ m by omega)]
    simp [h_lem1]
    have h_card2 : Finset.card {φ m, φ (m + 1)} = 2 := by
      apply Finset.card_pair
      have := h_mono (show m < m + 1 by omega)
      omega
    have h_ne2 : Finset.Nonempty {φ m, φ (m + 1)} := by apply Finset.card_pos.mp ; omega
    have h_min : Finset.min' {φ m, φ (m + 1)} h_ne2 = φ m := by
      have := h_mono (show m < m + 1 by omega)
      have := Finset.min'_le {φ m, φ (m + 1)} (φ m) (by simp)
      have := Finset.min'_mem {φ m, φ (m + 1)} h_ne2
      simp at this ; omega
    have h_max : Finset.max' {φ m, φ (m + 1)} h_ne2 = φ (m + 1) := by
      have := h_mono (show m < m + 1 by omega)
      have := Finset.le_max' {φ m, φ (m + 1)} (φ (m + 1)) (by simp)
      have := Finset.max'_mem {φ m, φ (m + 1)} h_ne2
      simp at this ; omega
    have h_color := h_color {φ m, φ (m + 1)} h_card2 (by intro x ; simp ; grind)
    simp [color, h_min, h_max] at h_color
    simp [Congruence.EqvCls, h_color]
  · simp [FinSubseq, ← appendListInf_ofFnPrefix_SuffixFrom]

end BuchiCongrFinite
