/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Mathlib.Imports

/-!
This file contains some definitions and theorems about finite and infinite sequences,
which are modeled by types `List X` and `ℕ → X` respectively (X being an arbitrary type).
It is imported directly or indirectly by all other files in AutomataTheory except those
in AutomataTheort.Mathlib.
-/

open Function Set Filter

section Sequences

variable {X : Type*}

def AppendListInf (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < xl.length then xl[k] else xs (k - xl.length)

instance instAppendListInf : HAppend (List X) (ℕ → X) (ℕ → X) :=
  { hAppend := AppendListInf }

def AppendFinInf {n : ℕ} (xs : Fin n → X) (xs' : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < n then xs ⟨k, h⟩ else xs' (k - n)

instance instAppendFinInf {n : ℕ} : HAppend (Fin n → X) (ℕ → X) (ℕ → X) :=
  { hAppend := AppendFinInf }

def SuffixFrom (xs : ℕ → X) (n : ℕ) : ℕ → X :=
  fun k ↦ xs (k + n)

instance instSuffixFrom : HShiftLeft (ℕ → X) (ℕ) (ℕ → X) :=
  { hShiftLeft := SuffixFrom }

def FixSuffix (xs : ℕ → X) (n : ℕ) (x : X) : ℕ → X :=
  fun k ↦ if k < n then xs k else x

def FinSubseq (xs : ℕ → X) (lo hi : ℕ) : List X :=
  List.ofFn (fun k : Fin (hi - lo) ↦ xs (k + lo))

variable {xl : List X} {xs xs' : ℕ → X}

theorem ofFn_eq_ofFn {m n n' : ℕ}
    (h : List.ofFn (fun k : Fin (m - n) ↦ xs (k + n)) = List.ofFn (fun k : Fin n' ↦ xs' k)) :
    m - n = n' ∧ ∀ k < n', xs (k + n) = xs' k := by
  simp [List.ofFn_inj'] at h
  obtain ⟨rfl, h'⟩ := h
  simp [funext_iff, Fin.forall_iff] at h'
  simp ; intro k h_k
  specialize h' k h_k
  simp [h']

theorem ofFn_of_append_ofFn_oFn {m n : ℕ} (h : n ≤ m) :
    (List.ofFn fun k : Fin m ↦ xs k) = (List.ofFn fun k : Fin n ↦ xs k) ++ List.ofFn fun k : Fin (m - n) ↦ xs (k + n) := by
  ext k x
  simp [← List.ofFn_fin_append, Fin.append, Fin.addCases, (by omega : n + (m - n) = m)]
  intro h_k_m
  rcases Classical.em (k < n) with h_k_n | h_k_n <;> simp [h_k_n]
  simp [(by omega : k - n + n = k)]

theorem appendListInf_ofFnPrefix_SuffixFrom {n : ℕ} :
    xs = (List.ofFn fun k : Fin n ↦ xs ↑k) ++ (xs <<< n) := by
  ext k ; simp [instAppendListInf, AppendListInf, instSuffixFrom, SuffixFrom]
  rcases Classical.em (k < n) with h_k | h_k
  · simp [h_k]
  · simp [(by omega : k - n + n = k)]

theorem appendListInf_elt_skip_list {n : ℕ} :
    (xl ++ xs) (n + xl.length) = xs n := by
  simp [instAppendListInf, AppendListInf]

theorem suffixFrom_listLength_AppendListInf :
    xs = (xl ++ xs) <<< xl.length := by
  ext k ; simp [instSuffixFrom, SuffixFrom, instAppendListInf, AppendListInf]

theorem frequently_in_finite_set [Finite X] {s : Set X} :
    (∃ᶠ k in atTop, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k in atTop, xs k = x := by
  constructor
  · intro h_inf
    rw [Nat.frequently_atTop_iff_infinite] at h_inf
    have : Infinite (xs ⁻¹' s) := h_inf.to_subtype
    let rf := Set.restrictPreimage s xs
    obtain ⟨⟨x, h_x⟩, h_inf'⟩ := Finite.exists_infinite_fiber rf
    rw [← Set.infinite_range_iff (Subtype.val_injective.comp Subtype.val_injective)] at h_inf'
    simp [rf, Set.range, ← Nat.frequently_atTop_iff_infinite] at h_inf'
    use x ; simp [h_x]
    apply Frequently.mono h_inf'
    tauto
  · rintro ⟨x, h_x, h_inf⟩
    apply Frequently.mono h_inf
    intro k h_k ; simpa [h_k]

end Sequences
