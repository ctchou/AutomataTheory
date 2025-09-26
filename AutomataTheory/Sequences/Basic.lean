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

open Function Set List Option Filter

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

def List.ExtendInf [Inhabited X] (xl : List X) : ℕ → X :=
  fun k ↦ if h : k < xl.length then xl[k] else default

/- Some technical lemmas are proved below.
-/
variable {xl xl' : List X} {xs xs' : ℕ → X}

theorem nil_AppendListInf :
    ([] : List X) ++ xs = xs := by
  ext k ; simp [instAppendListInf, AppendListInf]

theorem AppendListInf_assoc :
    (xl ++ xl') ++ xs = xl ++ (xl' ++ xs) := by
  ext k ; simp [instAppendListInf, AppendListInf]
  rcases (show k < xl.length ∨ (¬ k < xl.length ∧ k < xl.length + xl'.length) ∨ ¬ k < xl.length + xl'.length by omega)
    <;> grind

theorem finSubseq_eq_FinSubseq {m n m' n' : ℕ}
    (h : xs ⇊ m n = xs' ⇊ m' n') :
    n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := by
  simp [instFinSubseq, FinSubseq, List.ofFn_inj'] at h
  obtain ⟨h_eq, h_fun⟩ := h
  rw [← h_eq] at h_fun ; simp [funext_iff, Fin.forall_iff] at h_fun
  simp [← h_eq] ; intro k h_k
  rw [add_comm] ; simp [h_fun k h_k] ; congr 1 ; omega

theorem appendListInf_FinSubseq_SuffixFrom {n : ℕ} :
    (xs ⇊ 0 n) ++ (xs <<< n) = xs := by
  ext k ; simp [instAppendListInf, AppendListInf, instFinSubseq, FinSubseq, instSuffixFrom, SuffixFrom]
  rcases Classical.em (k < n) with h_k | h_k
  · simp [h_k]
  · simp [(by omega : k - n + n = k)]

theorem appendListInf_elt_skip_list {n : ℕ} :
    (xl ++ xs) (n + xl.length) = xs n := by
  simp [instAppendListInf, AppendListInf]

theorem appendListInf_elt_left {k : ℕ} (h : k < xl.length) :
    (xl ++ xs) k = xl[k] := by
  simp [instAppendListInf, AppendListInf, h]

theorem appendListInf_elt_right {k : ℕ} (h : xl.length ≤ k) :
    (xl ++ xs) k = xs (k - xl.length) := by
  simp [instAppendListInf, AppendListInf, h]

theorem appendListInf_FinSubseq_right {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ xs) ⇊ 0 n = xl ++ (xs ⇊ 0 (n - xl.length)) := by
  ext k x
  rcases (show k < xl.length ∨ (¬ k < xl.length ∧ k < n) ∨ ¬ k < n by omega) with h_k | h_k | h_k
    <;> simp [h_k, instAppendListInf, AppendListInf, instFinSubseq, FinSubseq, List.getElem?_append]
    <;> grind

theorem suffixFrom_listLength_AppendListInf :
    (xl ++ xs) <<< xl.length = xs := by
  ext k ; simp [instSuffixFrom, SuffixFrom, instAppendListInf, AppendListInf]

theorem sub_base_of_SuffixFrom {X : Type*} {xs : ℕ → X} {j k : ℕ} (h : j ≤ k) :
    (xs <<< j) (k - j) = xs k := by
  simp [instSuffixFrom, SuffixFrom, (show k - j + j = k by omega)]

theorem finSubseq_of_SuffixFrom {k m : ℕ} (h_m : k ≤ m) (n : ℕ) :
    (xs <<< k) ⇊ (m - k) (n - k) = xs ⇊ m n := by
  simp [instFinSubseq, FinSubseq, instSuffixFrom, SuffixFrom, add_assoc,
    (show m - k + k = m by omega), (show n - k - (m - k) = n - m by omega)]

theorem suffixFrom_FinSubseq0 {k n : ℕ} :
    (xs <<< k) ⇊ 0 n = xs ⇊ k (k + n) := by
  simp [instFinSubseq, FinSubseq, instSuffixFrom, SuffixFrom]

theorem length_FinSubseq {xs : ℕ → X} {m n : ℕ} :
    (xs ⇊ m n).length = n - m := by
  simp [instFinSubseq, FinSubseq]

theorem empty_FinSubseq {n : ℕ} :
    xs ⇊ n n = [] := by
  simp [instFinSubseq, FinSubseq]

theorem finSubseq_empty_iff {m n : ℕ} :
    xs ⇊ m n = [] ↔ m ≥ n := by
  simp [instFinSubseq, FinSubseq] ; omega

theorem finSubseq_elt {m n k : ℕ} (h : k < n - m) :
    (xs ⇊ m n)[k]'(by simp [length_FinSubseq, h]) = xs (k + m) := by
  simp [instFinSubseq, FinSubseq]

theorem extract_FinSubseq2' {xs : ℕ → X} {m n i j : ℕ} (h : j ≤ n - m) :
    (xs ⇊ m n).extract i j = xs ⇊ (m + i) (m + j) := by
  ext k x
  rcases (show k < j - i ∨ ¬ k < j - i by omega) with h_k | h_k <;>
    simp [instFinSubseq, FinSubseq, h_k]
  · simp [(show i + k < n - m by omega), (show k < m + j - (m + i) by omega), (show i + k + m = k + (m + i) by omega)]
  · simp [(show ¬ k < m + j - (m + i) by omega)]

theorem extract_FinSubseq2 {xs : ℕ → X} {n i j : ℕ} (h : j ≤ n) :
    (xs ⇊ 0 n).extract i j = xs ⇊ i j := by
  simp [extract_FinSubseq2' (show j ≤ n - 0 by omega)]

theorem extract_FinSubseq1 {xs : ℕ → X} {n i : ℕ} :
    (xs ⇊ 0 n).extract i = xs ⇊ i n := by
  simp [extract_FinSubseq2 (show n ≤ n by omega), length_FinSubseq]

theorem finSubseq_append_finSubseq (xs : ℕ → X) {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs ⇊ k m) ++ (xs ⇊ m n) = xs ⇊ k n := by
  ext i x ; simp [instFinSubseq, FinSubseq, List.getElem?_append] ; grind

theorem finSubseq_succ_right (xs : ℕ → X) {m n : ℕ} (h_mn : m ≤ n) :
    xs ⇊ m (n + 1) = xs ⇊ m n ++ [xs n] := by
  rw [← finSubseq_append_finSubseq xs h_mn (show n ≤ n + 1 by omega)]
  congr ; simp [instFinSubseq, FinSubseq]

theorem finSubseq_ExtendInf [Inhabited X] :
    xl.ExtendInf ⇊ 0 xl.length = xl := by
  simp [List.ExtendInf, instFinSubseq, FinSubseq]

theorem extendinf_elt_left [Inhabited X] {k : ℕ} (h : k < xl.length) :
    xl.ExtendInf k = xl[k] := by
  simp [List.ExtendInf, h]

theorem antitone_fin_eventually {n : ℕ} {f : ℕ → Fin n} (h : Antitone f) :
    ∃ i : Fin n, ∃ m, ∀ k ≥ m, f k = i := by
  have h_fin : (range f).Finite := toFinite (range f)
  have h_ne : (range f).Nonempty := by use (f 0) ; simp
  obtain ⟨i, ⟨m, rfl⟩, h_min⟩ := Finite.exists_minimal h_fin h_ne
  use (f m), m ; intro k h_k
  have h_k_m := h h_k
  have h_m_k := h_min (show f k ∈ range f by simp) h_k_m
  exact Fin.le_antisymm h_k_m h_m_k

theorem option_some_pigeonhole {X : Type*} [Finite X] {n : ℕ} (f : Fin n → Option X)
    (h : {j | (f j).isSome}.ncard > Nat.card X) :
    ∃ j1 j2, j1 ≠ j2 ∧ ∃ x, f j1 = some x ∧ f j2 = some x := by
  have ht : (some '' (univ : Set X)).Finite := by exact toFinite (some '' univ)
  have : (some '' (univ : Set X)).ncard = Nat.card X := by
    rw [ncard_image_of_injective (univ : Set X) (some_injective X)] ; exact ncard_univ X
  have hc : (some '' (univ : Set X)).ncard < {j | (f j).isSome}.ncard := by omega
  have hf : ∀ j ∈ {j | (f j).isSome}, f j ∈ some '' (univ : Set X) := by
    intro j ; simp ; rw [isSome_iff_exists] ; tauto
  obtain ⟨j1, h_j1, j2, h_j2, h_ne, h_eq⟩ := exists_ne_map_eq_of_ncard_lt_of_maps_to hc hf ht
  obtain ⟨s1, h_s1⟩ := isSome_iff_exists.mp h_j1
  obtain ⟨s2, h_s2⟩ := isSome_iff_exists.mp h_j2
  simp [h_s1, h_s2] at h_eq ; obtain ⟨rfl⟩ := h_eq
  use j1, j2 ; simp [h_ne] ; use s1

end Sequences
