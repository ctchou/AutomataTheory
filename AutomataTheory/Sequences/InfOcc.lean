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

open Function Set Prod Option Filter
open Classical

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

/-- Removing any finite prefix of `xs` does not change `InfOcc xs`.
-/
theorem inf_occ_suffix {X : Type*} (xs : ℕ → X) (k : ℕ) :
    InfOcc (xs <<< k) = InfOcc xs := by
  ext x ; simp [InfOcc, frequently_atTop] ; constructor
  · intro h_inf n ; obtain ⟨m, h_m, rfl⟩ := h_inf n
    use (k + m) ; simp [get_drop'] ; omega
  · intro h_inf n ; obtain ⟨m, h_m, rfl⟩ := h_inf (n + k)
    use (m - k) ; simp [get_drop', (show n ≤ m - k by omega), (show k + (m - k) = m by omega)]

/-- Over a finite type, `xs k` is in `InfOcc xs` for all sufficiently large `k`.
-/
theorem inf_occ_eventually {X : Type*} [Finite X] (xs : ℕ → X) :
    ∀ᶠ k in atTop, xs k ∈ InfOcc xs := by
  have h_compl : ∀ x ∈ (InfOcc xs)ᶜ, ∃ n, ∀ k ≥ n, xs k ≠ x := by simp [InfOcc]
  choose lb h_lb using h_compl
  let fs_compl := Finite.toFinset <| toFinite (InfOcc xs)ᶜ
  let glb := fs_compl.sup (fun x ↦ if h : x ∈ (InfOcc xs)ᶜ then lb x h else 0)
  have h_glb : ∀ x, (h : x ∈ (InfOcc xs)ᶜ) → lb x h ≤ glb := by
    intro x h ; refine Finset.le_sup_of_le (b := x) (by simpa [fs_compl]) (by simp [h])
  apply eventually_atTop.mpr
  use glb ; intro k h_k ; by_contra h_contra
  have := h_glb (xs k) h_contra
  have := h_lb (xs k) h_contra k (by omega)
  contradiction

/-- Note that only the ⊇ direction needs the finiteness assumptions.
-/
theorem inf_occ_proj {I : Type*} [Finite I] {X : I → Type*} [h : ∀ i, Finite (X i)] (xs : ℕ → Π i, X i) (i : I) :
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

/-- Same as inf_acc_proj, but for pair types.  This result does follow from
inf_occ_proj, but that proof (see below) turns out to be longer.
-/
theorem inf_occ_pair {X1 X2 : Type*} [Finite X1] [Finite X2] (xs : ℕ → X1 × X2) :
    fst '' (InfOcc xs) = InfOcc (fst ∘ xs) ∧
    snd '' (InfOcc xs) = InfOcc (snd ∘ xs) := by
  constructor
  · ext x1 ; simp ; constructor
    · rintro ⟨x2, h_inf⟩
      obtain ⟨φ, h_mono, h_x⟩ := frequently_iff_strict_mono.mp h_inf
      apply frequently_iff_strict_mono.mpr
      aesop
    · intro h_inf
      let s := { x : X1 × X2 | x.1 = x1 }
      have h_inf' : ∃ᶠ k in atTop, xs k ∈ s := by exact h_inf
      obtain ⟨x, h_x, h_inf''⟩ := frequently_in_finite_set.mp h_inf'
      aesop
  · ext x2 ; simp ; constructor
    · rintro ⟨x1, h_inf⟩
      obtain ⟨φ, h_mono, h_x⟩ := frequently_iff_strict_mono.mp h_inf
      apply frequently_iff_strict_mono.mpr
      aesop
    · intro h_inf
      let s := { x : X1 × X2 | x.2 = x2 }
      have h_inf' : ∃ᶠ k in atTop, xs k ∈ s := by exact h_inf
      obtain ⟨x, h_x, h_inf''⟩ := frequently_in_finite_set.mp h_inf'
      aesop

/- The following two proofs are due to Aaron Liu.
The ⊆ direction of the first proof doesn't need injectivity assumption.
-/
theorem infOcc_comp_of_injective {α β : Type*} {f : α → β} (hf : f.Injective) (xs : ℕ → α) :
    InfOcc (f ∘ xs) = f '' InfOcc xs := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨k, -, rfl⟩ := hx.exists
    simpa [InfOcc, hf.eq_iff] using hx
  · rw [Set.image_subset_iff]
    intro x hx
    simpa [InfOcc, hf.eq_iff] using hx

theorem inf_occ_pair' {X1 : Type u} {X2 : Type v} [Finite X1] [Finite X2] (xs : ℕ → X1 × X2) :
    fst '' (InfOcc xs) = InfOcc (fst ∘ xs) ∧
    snd '' (InfOcc xs) = InfOcc (snd ∘ xs) := by
  let e := (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm.trans (prodEquivPiFinTwo (ULift.{max u v} X1) (ULift.{max u v} X2))
  have fes : Prod.fst ∘ e.symm = ULift.down ∘ (· 0) := rfl
  have ses : Prod.snd ∘ e.symm = ULift.down ∘ (· 1) := rfl
  rw [← xs.id_comp, ← e.symm_comp_self]
  simp_rw [← Function.comp_assoc, fes, ses, Function.comp_assoc]
  rw [infOcc_comp_of_injective ULift.down_injective, infOcc_comp_of_injective ULift.down_injective,
    infOcc_comp_of_injective e.symm.injective]
  have finite (i : Fin 2) : Finite (![ULift.{max u v} X1, ULift.{max u v} X2] i) := by
    fin_cases i
    · exact inferInstanceAs (Finite (ULift.{max u v} X1))
    · exact inferInstanceAs (Finite (ULift.{max u v} X2))
  have hi := @inf_occ_proj (Fin 2) _ ![ULift.{max u v} X1, ULift.{max u v} X2] finite (e ∘ xs)
  simpa [Set.image_image] using And.intro
    (congrArg (Set.image ULift.down.{max u v}) (@hi 0))
    (congrArg (Set.image ULift.down.{max u v}) (@hi 1))

-- The following proof is due to Kyle Miller
instance {X : Type*} [Finite X] : Finite (Option X) :=
  have := Fintype.ofFinite X
  Finite.of_fintype _

theorem inf_occ_opt {X : Type*} [Finite X] (os : ℕ → Option X) (y : X)
    (h : ∀ o ∈ InfOcc os, o.isSome) :
    {x | ∃ o ∈ InfOcc os, o = some x} = InfOcc ((getD · y) ∘ os) := by
  ext x ; constructor
  · rintro ⟨o, h_inf, rfl⟩
    apply Frequently.mono h_inf
    intro k h_k ; simp [h_k]
  · intro h_inf ; simp
    obtain ⟨n, h_n⟩ := eventually_atTop.mp <| inf_occ_eventually os
    have h_n' : ∀ m ≥ n, ∃ x, os m = some x := by
      intro m h_m
      exact isSome_iff_exists.mp <| h (os m) <| h_n m h_m
    simp [← inf_occ_suffix os n]
    simp [← inf_occ_suffix ((getD · y) ∘ os) n] at h_inf
    apply Frequently.mono h_inf
    intro k
    obtain ⟨x', h_x'⟩ := h_n' (n + k) (by omega)
    simp [get_drop', h_x']

end InfOcc
