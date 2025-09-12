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

open Function Set List
open scoped Computability

namespace Automata

section ToBeMoved

variable {X : Type*}

theorem finSubseq_append_finSubseq (xs : ℕ → X) {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs ⇊ k m) ++ (xs ⇊ m n) = xs ⇊ k n := by
  ext i x ; simp [instFinSubseq, FinSubseq, getElem?_append] ; grind

theorem finSubseq_succ_right (xs : ℕ → X) {m n : ℕ} (h_mn : m ≤ n) :
    xs ⇊ m (n + 1) = xs ⇊ m n ++ [xs n] := by
  rw [← finSubseq_append_finSubseq xs h_mn (show n ≤ n + 1 by omega)]
  congr ; simp [instFinSubseq, FinSubseq]

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

end ToBeMoved

section ChouekaLemma

variable {A : Type}

def ChouekaLang (M : DA A) (acc : Set M.State) : Set (List A) :=
  { x | ∃ y z, y ≠ [] ∧ z ≠ [] ∧ x = y ++ z ∧
    M.RunOn y ∈ acc ∧ M.RunOn z = M.RunOn x ∧
    ∀ z', z' <+: z → z' ≠ [] → z' ≠ z → M.RunOn z' ≠ M.RunOn (y ++ z') }

variable {V : Set (List A)} (h_v : RegLang V)
  {M : DA A} [Finite M.State] {acc : Set M.State} (h_m : V∗ = M.toNA.AcceptedLang acc)

end ChouekaLemma
