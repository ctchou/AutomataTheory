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

/-- Append a list and an infinite sequence.
-/
def AppendListInf (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < xl.length then xl[k] else xs (k - xl.length)

/-- Use the infix notation `++` for `AppendListInf`.
-/
instance instAppendListInf : HAppend (List X) (ℕ → X) (ℕ → X) :=
  { hAppend := AppendListInf }

/-- Append a finite map (which is equivalent to a list) and an infinite sequence.
-/
def AppendFinInf {n : ℕ} (xs : Fin n → X) (xs' : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < n then xs ⟨k, h⟩ else xs' (k - n)

/-- Use the infix notation `++` for `AppendFintInf`.
-/
instance instAppendFinInf {n : ℕ} : HAppend (Fin n → X) (ℕ → X) (ℕ → X) :=
  { hAppend := AppendFinInf }

/-- Remove the first n elements from an infinite sequence xs.
-/
def SuffixFrom (xs : ℕ → X) (n : ℕ) : ℕ → X :=
  fun k ↦ xs (k + n)

/-- Use the infix notation `<<<` for `SuffixFrom`.
-/
instance instSuffixFrom : HShiftLeft (ℕ → X) (ℕ) (ℕ → X) :=
  { hShiftLeft := SuffixFrom }

/-- Get the list containing the elements of `xs` from position `lo` to `hi - 1`.
-/
def FinSubseq (xs : ℕ → X) (lo hi : ℕ) : List X :=
  List.ofFn (fun k : Fin (hi - lo) ↦ xs (k + lo))

/-- Use the postfix notation `⇊` for `FinSubseq`, like `xs ⇊ lo hi`.
-/
@[notation_class]
class GetSeg (α : Type*) (β : outParam (Type*)) where
  getSeg : α → β

postfix:1024 "⇊" => GetSeg.getSeg

instance instFinSubseq : GetSeg (ℕ → X) (ℕ → ℕ → List X) :=
  { getSeg := (FinSubseq ·) }

/-- Fix all elements of `xs` to `x` from position `n` onward.
-/
def FixSuffix (xs : ℕ → X) (n : ℕ) (x : X) : ℕ → X :=
  fun k ↦ if k < n then xs k else x

/- Some technical lemmas are proved below.
-/
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

theorem finSubseq_of_SuffixFrom {k m : ℕ} (h_m : k ≤ m) (n : ℕ) :
    (xs <<< k) ⇊ (m - k) (n - k) = xs ⇊ m n := by
  simp [instFinSubseq, FinSubseq, instSuffixFrom, SuffixFrom, add_assoc,
    (show m - k + k = m by omega), (show n - k - (m - k) = n - m by omega)]

end Sequences
