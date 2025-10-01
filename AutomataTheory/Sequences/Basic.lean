/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Mathlib.Imports

/-!
This file contains some definitions and theorems about finite and infinite sequences,
which are modeled by types `List X` and `Stream' X` respectively (X being an arbitrary type).
It is imported directly or indirectly by all other files in AutomataTheory except those
in AutomataTheory.Mathlib.
-/

open Function Set Option Stream'

section List

/-- Pad a finite sequence into an infinite sequence using `default`.
-/
def List.padDefault [Inhabited X] (xl : List X) : Stream' X :=
  fun k ↦ if h : k < xl.length then xl[k] else default

end List

section Stream'

namespace Stream'

variable {X : Type*}

/-- Get the list containing the elements of `xs` from position `m` to `n - 1`.
-/
def extract (xs : Stream' X) (m n : ℕ) : List X :=
  List.ofFn (fun k : Fin (n - m) ↦ xs (m + k))

/-- Fix all elements of `xs` to `x` from position `n` onward.
-/
def fixSuffix (xs : Stream' X) (n : ℕ) (x : X) : Stream' X :=
  fun k ↦ if k < n then xs k else x

/- Some miscellaneous theorems are proved below. -/

theorem get_drop' {xs : Stream' X} {n k : ℕ} :
    (xs.drop n) k = xs (n + k) := by
  apply get_drop

theorem get_append_left' {k : ℕ} (h : k < xl.length) :
    (xl ++ₛ xs) k = xl[k] := by
  apply get_append_left

theorem get_append_right' {k : ℕ} (h : xl.length ≤ k) :
    (xl ++ₛ xs) k = xs (k - xl.length) := by
  obtain ⟨n, rfl⟩ := show ∃ n, k = xl.length + n by use (k - xl.length) ; omega
  simp ; apply get_append_right

theorem extract_eq_ofFn {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = List.ofFn (fun k : Fin (n - m) ↦ xs (m + k)) := by
  rfl

theorem extract_eq_extract {xs xs' : Stream' X} {m n m' n' : ℕ}
    (h : xs.extract m n = xs'.extract m' n') :
    n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := by
  simp [extract, List.ofFn_inj'] at h
  obtain ⟨h_eq, h_fun⟩ := h
  rw [← h_eq] at h_fun ; simp [funext_iff, Fin.forall_iff] at h_fun
  simp [← h_eq] ; intro k h_k ; simp [h_fun k h_k]

theorem extract_eq_drop_take {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = take (n - m) (xs.drop m) := by
  ext k x
  rcases (show k < n - m ∨ ¬ k < n - m by omega) with h_k | h_k <;>
    simp (disch := omega) [h_k, extract, getElem?_take] <;> aesop

theorem extract_eq_take {xs : Stream' X} {n : ℕ} :
    xs.extract 0 n = xs.take n := by
  simp [extract_eq_drop_take]

theorem append_extract_drop {xs : Stream' X} {n : ℕ} :
    (xs.extract 0 n) ++ₛ (xs.drop n) = xs := by
  simp [extract_eq_take]

theorem extract_apppend_right_right {xl : List X} {xs : Stream' X} {m n : ℕ} (h : xl.length ≤ m) :
    (xl ++ₛ xs).extract m n = xs.extract (m - xl.length) (n - xl.length) := by
  ext k x
  rcases (show k < n - m ∨ ¬ k < n - m by omega) with h_k | h_k <;> simp [h_k, extract]
  · simp  (disch := omega) [get_append_right'] ; grind
  · omega

theorem extract_append_zero_right {xl : List X} {xs : Stream' X} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ₛ xs).extract 0 n = xl ++ (xs.extract 0 (n - xl.length)) := by
  obtain ⟨k, rfl⟩ := show ∃ k, n = xl.length + k by use (n - xl.length) ; omega
  simp [extract_eq_take, ← append_take]

theorem extract_drop {xs : Stream' X} {k m n : ℕ} :
    (xs.drop k).extract m n = xs.extract (k + m) (k + n) := by
  have h1 : k + n - (k + m) = n - m := by omega
  simp [extract_eq_drop_take, h1]

theorem length_extract {xs : Stream' X} {m n : ℕ} :
    (xs.extract m n).length = n - m := by
  simp [extract]

theorem extract_nil {xs : Stream' X} {n : ℕ} :
    xs.extract n n = [] := by
  simp [extract]

theorem extract_nil_iff {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = [] ↔ m ≥ n := by
  simp [extract] ; omega

theorem get_extract {xs : Stream' X} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp [length_extract, h]) = xs (m + k) := by
  simp [extract]

theorem extract_extract2' {xs : Stream' X} {m n i j : ℕ} (h : j ≤ n - m) :
    (xs.extract m n).extract i j = xs.extract (m + i) (m + j) := by
  ext k x
  rcases (show k < j - i ∨ ¬ k < j - i by omega) with h_k | h_k <;>
    simp [extract, h_k]
  · simp [(show i + k < n - m by omega), (show k < m + j - (m + i) by omega), add_assoc]
  · simp [(show ¬ k < m + j - (m + i) by omega)]

theorem extract_extract2 {xs : Stream' X} {n i j : ℕ} (h : j ≤ n) :
    (xs.extract 0 n).extract i j = xs.extract i j := by
  simp [extract_extract2' (show j ≤ n - 0 by omega)]

theorem extract_extract1 {xs : Stream' X} {n i : ℕ} :
    (xs.extract 0 n).extract i = xs.extract i n := by
  simp [extract_extract2 (show n ≤ n by omega), length_extract]

theorem append_extract_extract (xs : Stream' X) {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs.extract k m) ++ (xs.extract m n) = xs.extract k n := by
  ext i x ; simp [extract, List.getElem?_append] ; grind

theorem extract_succ_right (xs : Stream' X) {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs n] := by
  rw [← append_extract_extract xs h_mn (show n ≤ n + 1 by omega)]
  congr ; simp [extract]

theorem extract_padDefault [Inhabited X] {xl : List X} :
    xl.padDefault.extract 0 xl.length = xl := by
  simp [List.padDefault, extract]

theorem padDefault_elt_left [Inhabited X] {xl : List X} {k : ℕ} (h : k < xl.length) :
    xl.padDefault k = xl[k] := by
  simp [List.padDefault, h]

end Stream'

section Misc

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

end Misc
