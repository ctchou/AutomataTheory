/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences.Basic

/-!
Given a strictly monotonic function `φ : ℕ → ℕ` with `φ 0 = 0` and `k : ℕ`,
`Segment φ k` is the unique `m : ℕ` such that `φ m ≤ k < φ (k + 1)`.
This file proves various properties aboout segments, which are used to
reason about the omega iteration of a language (L^ω).
-/

open Function Set

section Segments

open Classical

/- Given a strictly monotonic function `φ : ℕ → ℕ` with `φ 0 = 0` and `k : ℕ`,
`Segment φ k` is the unique `m : ℕ` such that `φ m ≤ k < φ (k + 1)`.
-/
noncomputable def Segment (φ : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k ∈ range φ then Nat.count (· ∈ range φ) k else Nat.count (· ∈ range φ) k - 1

variable {φ : ℕ → ℕ}

lemma nth_succ_gap {p : ℕ → Prop} (hf : (setOf p).Infinite) (n : ℕ) :
    ∀ k < Nat.nth p (n + 1) - Nat.nth p n, k > 0 → ¬ p (k + Nat.nth p n) := by
  intro k h_k1 h_k0 h_p_k
  let m := Nat.count p (k + Nat.nth p n)
  have h_k_ex : Nat.nth p m = k + Nat.nth p n := by simp [m, Nat.nth_count h_p_k]
  have h_n_m : n < m := by apply (Nat.nth_lt_nth hf).mp ; omega
  have h_m_n : m < n + 1 := by apply (Nat.nth_lt_nth hf).mp ; omega
  omega

theorem strict_mono_infinite (hm : StrictMono φ) :
    (range φ).Infinite := by
  exact infinite_range_of_injective hm.injective

-- The following proof is due to Kyle Miller.
theorem nth_of_strict_mono (hm : StrictMono φ) (n : ℕ) :
    φ n = Nat.nth (· ∈ range φ) n := by
  rw [← Nat.nth_comp_of_strictMono hm (by simp)]
  · simp
  intro hf ; exfalso
  have : (range φ).Infinite := strict_mono_infinite hm
  exact absurd hf this

theorem count_out_range_pos (h0 : φ 0 = 0) (n : ℕ) (hn : n ∉ range φ) :
    Nat.count (· ∈ range φ) n > 0 := by
  have h0' : 0 ∈ range φ := by use 0
  have h1 : n ≠ 0 := by rintro ⟨rfl⟩ ; contradiction
  have h2 : 1 ≤ n := by omega
  have h3 := Nat.count_monotone (· ∈ range φ) h2
  simp [Nat.count_succ, h0', -mem_range] at h3 ⊢
  omega

theorem segment_plus_one (h0 : φ 0 = 0) (k : ℕ) :
    Segment φ k + 1 = Nat.count (· ∈ range φ) (k + 1) := by
  rcases Classical.em (k ∈ range φ) with h_k | h_k <;> simp [Segment, Nat.count_succ, h_k, -mem_range]
  suffices _ : Nat.count (· ∈ range φ) k > 0 by omega
  exact count_out_range_pos h0 k h_k

theorem segment_upper_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    k < φ (Segment φ k + 1) := by
  rw [nth_of_strict_mono hm (Segment φ k + 1), segment_plus_one h0 k]
  suffices _ : k + 1 ≤ Nat.nth (· ∈ range φ) (Nat.count (· ∈ range φ) (k + 1)) by omega
  apply Nat.le_nth_count
  exact strict_mono_infinite hm

theorem segment_lower_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    φ (Segment φ k) ≤ k := by
  rw [nth_of_strict_mono hm (Segment φ k)]
  rcases Classical.em (k ∈ range φ) with h_k | h_k <;> simp [Segment, h_k, -mem_range]
  suffices _ : Nat.nth (· ∈ range φ) (Nat.count (· ∈ range φ) k - 1) < k by omega
  apply Nat.nth_lt_of_lt_count
  have : Nat.count (· ∈ range φ) k > 0 := by exact count_out_range_pos h0 k h_k
  omega

theorem segment_idem (hm : StrictMono φ) (k : ℕ) :
    Segment φ (φ k) = k := by
  have h_rng : φ k ∈ range φ := by simp
  rw [Segment] ; simp [h_rng, -mem_range]
  rw [nth_of_strict_mono hm]
  have h_eq := Nat.count_nth_of_infinite (p := (· ∈ range φ)) <| strict_mono_infinite hm
  rw [h_eq]

theorem segment_zero (hm : StrictMono φ) (h0 : φ 0 = 0) :
    Segment φ 0 = 0 := by
  calc _ = Segment φ (φ 0) := by simp [h0]
       _ = _ := by simp [segment_idem hm]

theorem segment_range_gap (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m < k) (hu : k < φ (m + 1)) : k ∉ range φ := by
  rw [nth_of_strict_mono hm m] at hl
  rw [nth_of_strict_mono hm (m + 1)] at hu
  have h_inf := strict_mono_infinite hm
  have h_gap := nth_succ_gap (p := (· ∈ range φ)) h_inf m (k - Nat.nth (· ∈ range φ) m) (by omega) (by omega)
  rw [(show k - Nat.nth (· ∈ range φ) m + Nat.nth (· ∈ range φ) m = k by omega)] at h_gap
  exact h_gap

theorem segment_range_val (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) (hu : k < φ (m + 1)) : Segment φ k = m := by
  obtain (rfl | hu') := show φ m = k ∨ φ m < k by omega
  · exact segment_idem hm m
  obtain ⟨j, h_j, rfl⟩ := show ∃ j < φ (m + 1) - φ m - 1, k = j + φ m + 1 by use (k - φ m - 1) ; omega
  induction' j with j h_ind
  · have h1 : φ m ∈ range φ := by use m
    have h2 : φ m + 1 ∉ range φ := by apply segment_range_gap hm (show φ m < φ m + 1 by omega) ; omega
    have h3 := nth_of_strict_mono hm m
    rw [Segment] ; simp [h1, h2, Nat.count_succ, -mem_range] ; rw [h3]
    have h_eq := Nat.count_nth_of_infinite (p := (· ∈ range φ)) <| strict_mono_infinite hm
    rw [h_eq]
  have h_ind' := h_ind (by omega) (by omega) (by omega) (by omega)
  have h1 : j + 1 + φ m ∉ range φ := by apply segment_range_gap hm (show φ m < j + 1 + φ m by omega) ; omega
  have h2 : j + 1 + φ m + 1 ∉ range φ := by apply segment_range_gap hm (show φ m < j + 1 + φ m + 1 by omega) ; omega
  rw [Segment] at h_ind' ⊢
  simp [h1, (show j + φ m + 1 = j + 1 + φ m by omega), -mem_range] at h_ind'
  simp [h1, h2, Nat.count_succ, -mem_range]
  exact h_ind'

theorem segment_galois_connection (hm : StrictMono φ) (h0 : φ 0 = 0) :
    GaloisConnection φ (Segment φ) := by
  intro m k ; constructor
  · intro h
    by_contra! h_con
    have h1 : Segment φ k + 1 ≤ m := by omega
    have := (StrictMono.le_iff_le hm).mpr h1
    have := segment_upper_bound hm h0 k
    omega
  · intro h
    by_contra! h_con
    have := (StrictMono.le_iff_le hm).mpr h
    have := segment_lower_bound hm h0 k
    omega

end Segments

section Segments'

/- Segment' φ k does not assume φ 0 = 0, but returns a meaningful value
   only when k ≥ φ 0 and returns 0 for all k < φ 0.
-/
noncomputable def Segment' (φ : ℕ → ℕ) (k : ℕ) : ℕ :=
  Segment (φ · - φ 0) (k - φ 0)

lemma base_zero_shift (φ : ℕ → ℕ) :
    (φ · - φ 0) 0 = 0 := by
  simp

lemma base_zero_strict_mono {φ : ℕ → ℕ} (hm : StrictMono φ) :
    StrictMono (φ · - φ 0) := by
  intro m n h_m_n ; simp
  have := hm h_m_n
  have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le hm]
  have : φ 0 ≤ φ n := by simp [StrictMono.le_iff_le hm]
  omega

variable {φ : ℕ → ℕ}

theorem segment'_zero (hm : StrictMono φ) {k : ℕ} (h : k ≤ φ 0) :
    Segment' φ k = 0 := by
  simp [Segment', (show k - φ 0 = 0 by omega)]
  exact segment_zero (base_zero_strict_mono hm) (base_zero_shift φ)

theorem segment'_upper_bound (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    k < φ (Segment' φ k + 1) := by
  simp [Segment']
  have := segment_upper_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega

theorem segment'_lower_bound (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    φ (Segment' φ k) ≤ k := by
  simp [Segment']
  have := segment_lower_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega

theorem segment'_idem (hm : StrictMono φ) (k : ℕ) :
    Segment' φ (φ k) = k := by
  simp [Segment']
  exact segment_idem (base_zero_strict_mono hm) k

theorem segment'_range_val (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) (hu : k < φ (m + 1)) : Segment' φ k = m := by
  simp [Segment']
  have h : φ 0 ≤ k := by
    have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le hm]
    omega
  have hl' : (φ · - φ 0) m ≤ k - φ 0 := by simp ; omega
  have hu' : k - φ 0 < (φ · - φ 0) (m + 1) := by simp ; omega
  exact segment_range_val (base_zero_strict_mono hm) hl' hu'

theorem segment'_lower_val (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) : m ≤ Segment' φ k := by
  simp [Segment']
  have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le hm]
  exact (segment_galois_connection (base_zero_strict_mono hm) (base_zero_shift φ) m (k - φ 0)).mp (by omega)

end Segments'
