/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib

import AutomataTheory.Languages.OmegaRegLang

/-!
This file proves the main lemma in Choueka's paper (see README for the reference).
-/

open Function Set List Filter
open scoped Computability

namespace Automata

section ToBeMoved

variable {A : Type}

def DA.RunFromOn (M : DA A) (s : M.State) (al : List A) : M.State :=
  al.foldl M.next s

def DA.RunOn (M : DA A) : List A → M.State :=
  M.RunFromOn M.init

theorem da_run_from_on_append (M : DA A) (s : M.State) (al1 al2 : List A) :
    M.RunFromOn s (al1 ++ al2) = M.RunFromOn (M.RunFromOn s al1) al2 := by
  simp only [DA.RunFromOn, foldl_append]

theorem da_run_on_of_det_run (M : DA A) (as : ℕ → A) (n : ℕ) :
    M.RunOn (as ⇊ 0 n) = M.DetRun as n := by
  induction' n with n h_ind
  · simp [DA.DetRun, DA.RunOn, DA.RunFromOn, instFinSubseq, FinSubseq]
  have h1 := finSubseq_succ_right as (show 0 ≤ n by omega)
  rw [DA.RunOn, DA.DetRun, ← h_ind, h1, da_run_from_on_append] ; rfl

theorem da_run_on_to_det_run [Inhabited A] (M : DA A) (al : List A) :
    M.RunOn al = M.DetRun al.ExtendInf al.length := by
  rw [← da_run_on_of_det_run M al.ExtendInf al.length]
  congr ; ext i a ; simp [instFinSubseq, FinSubseq, List.ExtendInf]

theorem da_acc_lang_iff_run_acc [Inhabited A] (M : DA A) (acc : Set M.State) (al : List A) :
    al ∈ M.toNA.AcceptedLang acc ↔ M.RunOn al ∈ acc := by
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, rfl⟩
    have h0 := da_fin_run_unique h_run n (by omega)
    have h1 := da_run_on_of_det_run M as n
    simp [instFinSubseq, FinSubseq] at h1
    simp [h1, ← h0, h_acc]
  · intro h_acc
    use al.length, al.ExtendInf ; simp [List.ExtendInf]
    use (M.DetRun al.ExtendInf)
    constructor
    · exact da_fin_run_exists (M := M) al.length al.ExtendInf
    · simp [← da_run_on_to_det_run, h_acc]

theorem greater_subseq_lemma (φ φ' : ℕ → ℕ) (hi : Injective φ') :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, φ (σ n) < φ' (σ (n + 1)) := by
  have h_step : ∀ n, ∃ m > n, φ n < φ' m := by
    intro n
    have h_inf : {m | m > n}.Infinite := by
      apply infinite_of_forall_exists_gt ; intro k
      use (k + n + 1) ; simp ; omega
    have h_inf' := Infinite.image (injOn_of_injective hi) h_inf
    have h_fin : {m | m ≤ φ n}.Finite := by exact finite_le_nat (φ n)
    obtain ⟨k, ⟨m, h_m, rfl⟩, h_m'⟩ := Infinite.exists_notMem_finite h_inf' h_fin
    simp at h_m h_m' ; use m
  choose f h_f h_φ using h_step
  use (fun k ↦ f^[k] 0) ; constructor
  · apply strictMono_nat_of_lt_succ ; simp [iterate_succ_apply', h_f]
  · simp [iterate_succ_apply', h_φ]

variable {X : Type*}

end ToBeMoved

section ChouekaLemma

variable {A : Type}

def DA.ChouekaLang' (M : DA A) (acc : Set M.State) : Set (List A) :=
  { x | ∃ y z, y ≠ [] ∧ z ≠ [] ∧ x = y ++ z ∧
    M.RunOn y ∈ acc ∧ M.RunOn z = M.RunOn x ∧
    ∀ z', z' <+: z → z' ≠ [] → z' ≠ z → M.RunOn z' ≠ M.RunOn (y ++ z') }

def DA.ChouekaLang (M : DA A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ m, 0 < m ∧ m < al.length ∧
    M.RunOn (al.extract 0 m) ∈ acc ∧ M.RunOn (al.extract m al.length) = M.RunOn al ∧
    ∀ k, m < k → k < al.length → ¬ M.RunOn (al.extract m k) = M.RunOn (al.extract 0 k) }

theorem choueka_lang_omega_limit_subset_omega_power [Inhabited A] {M : DA A} {acc : Set M.State} :
    (M.ChouekaLang acc)↗ω ⊆ (M.toNA.AcceptedLang acc)^ω := by
  intro as ; simp [instOmegaLimit, OmegaLimit, frequently_iff_strict_mono]
  intro φ h_φ_mono h_prefix
  have h_m_ex : ∀ n, ∃ m, 0 < m ∧ m < φ n ∧
      M.RunOn (as ⇊ 0 m) ∈ acc ∧ M.RunOn (as ⇊ m (φ n)) = M.RunOn (as ⇊ 0 (φ n)) ∧
      ∀ k, m < k → k < φ n → M.RunOn (as ⇊ m k) ≠ M.RunOn (as ⇊ 0 k) := by
    intro n
    obtain ⟨m, h_m0, h_m1, h_acc, h_run, h_run'⟩ := h_prefix n
    simp [length_FinSubseq] at h_m1
    simp [-extract_eq_drop_take, extract_FinSubseq2 (show m ≤ φ n by omega)] at h_acc
    simp [-extract_eq_drop_take, extract_FinSubseq1] at h_run
    use m ; simp [h_m0, h_m1, h_acc, h_run]
    intro k h_k h_k'
    specialize h_run' k h_k (by simp [length_FinSubseq, h_k'])
    simp [-extract_eq_drop_take, extract_FinSubseq2 (show k ≤ φ n by omega)] at h_run'
    exact h_run'
  choose φ' h_φ'_0 h_φ'_n h_acc h_run h_run' using h_m_ex
  have h_inj : Injective φ' := by
    intro n1 n2 h_φ' ; by_contra h_contra
    wlog h : n1 < n2 generalizing n1 n2 with h'
    · exact h' h_φ'.symm (by omega) (by omega)
    have := h_φ_mono h ; have := h_φ'_n n1 ; have := h_run n1
    have := h_run' n2 (φ n1) (by omega) (by omega)
    simp_all
  obtain ⟨σ, h_σ_mono, h_φ_φ'⟩ := greater_subseq_lemma φ φ' h_inj
  use (fun k ↦ if k = 0 then 0 else φ' (σ (k - 1))) ; simp ; constructor
  · apply strictMono_nat_of_lt_succ ; intro n
    rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n]
    · exact h_φ'_0 (σ 0)
    have := h_φ'_n (σ (n - 1))
    have := h_φ_φ' (n - 1)
    grind
  · intro n
    simp [da_acc_lang_iff_run_acc]
    rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n]
    · exact h_acc (σ 0)
    have h1 := h_φ'_n (σ (n - 1))
    have h2 := h_φ_φ' (n - 1) ; simp [show n - 1 + 1 = n by omega] at h2
    have h3 := finSubseq_append_finSubseq as (show φ' (σ (n - 1)) ≤ φ (σ (n - 1)) by omega)
      (show φ (σ (n - 1)) ≤ φ' (σ n) by omega)
    have h4 := h_run (σ (n - 1)) ; simp [DA.RunOn] at h4
    simp [← h3, DA.RunOn, da_run_from_on_append, h4]
    have h5 := finSubseq_append_finSubseq as (show 0 ≤ φ (σ (n - 1)) by omega)
      (show φ (σ (n - 1)) ≤ φ' (σ n) by omega)
    simp [← da_run_from_on_append, h5]
    exact h_acc (σ n)

-- ∀ {Color : Type u_1} {Vertex : Type u_2} [Finite Color] (color : Edge → Color) [Infinite Vertex],
--   ∃ c s, s.Infinite ∧ ∀ (e : Edge), Finset.card e = 2 → ↑e ⊆ s → color e = c

lemma ramsey_lemma {C : Type*} {cs : Set C} {φ : ℕ → ℕ} {col : ℕ → ℕ → C}
    (h_fin : cs.Finite) (h_mono : StrictMono φ) (h_col : ∀ i j, i < j → col (φ i) (φ j) ∈ cs) :
    ∃ c ∈ cs, ∃ ξ : ℕ → ℕ, StrictMono ξ ∧ ∀ i j, i < j → col (φ (ξ i)) (φ (ξ i)) = c := by
  sorry

theorem choueka_lang_omega_power_subset_omega_limit [Inhabited A]
    {M : DA A} [Finite M.State] {acc : Set M.State}
    {V : Set (List A)} (h_lang : M.toNA.AcceptedLang acc = V∗) :
    V^ω ⊆ V∗ * (M.ChouekaLang acc)↗ω := by
  rintro as ⟨φ, h_φ_mono, h_φ_0, h_φ_V⟩
  have h_kstar : ∀ i j, i ≤ j → (as⇊ (φ i) (φ (j))) ∈ V∗ := by
    intro i j h_ij ; simp [instIterStar, IterStar]
    use (j - i) ; generalize h_n : j - i = n
    induction' n with n h_ind generalizing i j <;> simp [instIterFin, IterFin]
    · simp [empty_FinSubseq, (show i = j by omega)]
    use (as ⇊ (φ i) (φ (j - 1))), (as ⇊ (φ (j - 1)) (φ j)) ; constructorm* _ ∧ _
    · exact h_ind i (j - 1) (by omega) (by omega)
    · specialize h_φ_V (j - 1)
      simp [(show j - 1 + 1 = j by omega)] at h_φ_V
      exact h_φ_V
    · symm ; apply append_FinSubseq_FinSubseq <;>
        apply StrictMono.monotone h_φ_mono <;> omega
  let color (i j : ℕ) : M.State := M.RunOn (as ⇊ i j)
  have h_color : ∀ i j, i < j → color (φ i) (φ j) ∈ acc := by
    intro i j h_ij ; simp [color, ← da_acc_lang_iff_run_acc, h_lang]
    apply h_kstar ; omega
  obtain ⟨s, h_acc, ξ, h_ξ_mono, h_ξ_color⟩ := ramsey_lemma (acc.toFinite) h_φ_mono h_color
  use (as ⇊ 0 (φ (ξ 0))), (as <<< (φ (ξ 0)))
  simp [appendListInf_FinSubseq_SuffixFrom] ; constructor
  · specialize h_kstar 0 (ξ 0) (by omega)
    simp [h_φ_0] at h_kstar
    exact h_kstar
  sorry

end ChouekaLemma
