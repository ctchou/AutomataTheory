/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences.Basic

/-!
This file contains some definitions and theorems about
infinite occurrences in an infinite sequence.
-/

open Function Set Filter

section InfOcc

/-- `InfOcc xs` is the set of elements that appears infinitely many times in `xs`.
-/
def InfOcc {X : Type*} (xs : ℕ → X) : Set X :=
  { x | ∃ᶠ k in atTop, xs k = x }

/-- An alternative characterization of "infinitely often".
-/
theorem frequently_iff_strict_mono {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p n) ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m, p (φ m) := by
  constructor
  · intro h
    exact extraction_of_frequently_atTop h
  · rintro ⟨φ, h_mono, h_p⟩
    rw [Nat.frequently_atTop_iff_infinite]
    have h_range : range φ ⊆ {n | p n} := by
      rintro k ⟨m, rfl⟩
      simp_all only [mem_setOf_eq]
    apply Infinite.mono h_range
    exact infinite_range_of_injective h_mono.injective

/-- Note that only the → direction needs the finiteness assumption.
-/
theorem frequently_in_finite_set {X : Type*} [Finite X] {s : Set X} {xs : ℕ → X} :
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

/-- Note that only the ⊇ direction needs the finiteness assumptions.
-/
theorem inf_occ_proj {I : Type*} [Finite I] {X : I → Type*} [∀ i, Finite (X i)] {xs : ℕ → Π i, X i} {i : I} :
    (· i) '' (InfOcc xs) = InfOcc ((· i) ∘ xs) := by
  ext x_i ; simp ; constructor
  · rintro ⟨x, h_inf, rfl⟩
    obtain ⟨φ, h_mono, h_x⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    aesop
  · intro h_inf
    let s := { x : Π i, X i | x i = x_i }
    have h_inf' : ∃ᶠ k in atTop, xs k ∈ s := by exact h_inf
    obtain ⟨x, h_x, h_inf''⟩ := frequently_in_finite_set.mp h_inf'
    aesop

end InfOcc
