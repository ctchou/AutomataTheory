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

theorem greater_subseq_lemma {φ φ' : ℕ → ℕ} (hi : Injective φ') :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, (φ ∘ σ) n < (φ' ∘ σ) (n + 1) := by
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

theorem length_FinSubseq {xs : ℕ → X} {m n : ℕ} :
    (xs ⇊ m n).length = n - m := by
  simp [instFinSubseq, FinSubseq]

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
    ∀ k, m < k → k < al.length → M.RunOn (al.extract m k) ≠ M.RunOn (al.extract 0 k) }

variable {V : Set (List A)} (h_v : RegLang V)
  {M : DA A} [Finite M.State] {acc : Set M.State} (h_m : V∗ = M.toNA.AcceptedLang acc)

theorem choueka_lang_omega_limit_subset_omega_power :
    (M.ChouekaLang acc)↗ω ⊆ V^ω := by
  intro as ; simp [instOmegaLimit, OmegaLimit, frequently_iff_strict_mono]
  intro φ h_mono h_prefix
  have : ∀ n, ∃ m, 0 < m ∧ m < φ n ∧
      M.RunOn (as ⇊ 0 m) ∈ acc ∧ M.RunOn (as ⇊ m (φ n)) = M.RunOn (as ⇊ 0 (φ n)) ∧
      ∀ k, m < k → k < φ n → M.RunOn (as ⇊ m k) ≠ M.RunOn (as ⇊ 0 k) := by
    intro n
    obtain ⟨y, z, h_y0, h_z0, h_yz, h_acc, h_run, h_run'⟩ := h_prefix n
    let m := y.length
    have : y.length + z.length = φ n := by
      simp [← length_append, ← h_yz, length_FinSubseq]
    simp [← finSubseq_append_finSubseq as (show 0 ≤ y.length by omega) (show y.length ≤ (φ n) by omega)] at h_yz
    obtain ⟨_, _⟩ := append_inj h_yz (by simp [length_FinSubseq])
    --use y.length
    sorry
  sorry

end ChouekaLemma
