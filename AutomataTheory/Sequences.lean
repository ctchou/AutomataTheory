/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.Cofinite

/-!
This file contains some definitions and theorems about finite and infinite sequences,
which are modeled by types `List X` and `ℕ → X` respectively (X being an arbitrary type).
This file also contains all Mathlib imports concerning finite and infinite sequences and
is imported directly or indirectly by all other files in AutomataTheory.
-/

open Function Set Filter

section Sequences

def List.ExtendInf {X : Type*} [Inhabited X] (xl : List X) : ℕ → X :=
  fun k ↦ if h : k < xl.length then xl[k] else default

def AppendListInf {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < xl.length then xl[k] else xs (k - xl.length)

def AppendFinInf {X : Type*} {n : ℕ} (xs : Fin n → X) (xs' : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < n then xs ⟨k, h⟩ else xs' (k - n)

def FixSuffix {X : Type*} (n : ℕ) (xs : ℕ → X) (x : X) : ℕ → X :=
  fun k ↦ if k < n then xs k else x

def SuffixFrom {X : Type*} (n : ℕ) (xs : ℕ → X) : ℕ → X :=
  fun k ↦ xs (k + n)

variable {X : Type*} {xl : List X} {xs xs' : ℕ → X}

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
    xs = AppendListInf (List.ofFn fun k : Fin n ↦ xs ↑k) (SuffixFrom n xs) := by
  ext k ; simp [AppendListInf, SuffixFrom]
  rcases Classical.em (k < n) with h_k | h_k
  · simp [h_k]
  · simp [(by omega : k - n + n = k)]

theorem suffixFrom_listLength_AppendListInf :
    xs = SuffixFrom xl.length (AppendListInf xl xs) := by
  ext k ; simp [SuffixFrom, AppendListInf]

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
