/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Basic

open Function Set Filter

section Sequences

def AppendListInf {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < xl.length then xl[k] else xs (k - xl.length)

def AppendFinInf {X : Type*} {n : ℕ} (xs : Fin n → X) (xs' : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < n then xs ⟨k, h⟩ else xs' (k - n)

def FixSuffix {X : Type*} (n : ℕ) (xs : ℕ → X) (x : X) : ℕ → X :=
  fun k ↦ if k < n then xs k else x

def SuffixFrom {X : Type*} (n : ℕ) (xs : ℕ → X) : ℕ → X :=
  fun k ↦ xs (k + n)

def Step {X : Type*} (xs : ℕ → X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → xs (k + 1) ∈ q

def LeadsTo {X : Type*} (xs : ℕ → X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → ∃ k' ≥ k, xs k' ∈ q

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
  · simp [h_k, (by omega : k - n + n = k)]

theorem suffixFrom_listLength_AppendListInf :
    xs = SuffixFrom xl.length (AppendListInf xl xs) := by
  ext k ; simp [SuffixFrom, AppendListInf]

theorem leads_to_step {p q : Set X}
    (h : Step xs p q) : LeadsTo xs p q := by
  intro k h_p
  use (k + 1) ; constructor
  · omega
  · exact h k h_p

theorem leads_to_trans {p q r : Set X}
    (h1 : LeadsTo xs p q) (h2 : LeadsTo xs q r) : LeadsTo xs p r := by
  intro k h_p
  obtain ⟨k', h_k', h_q⟩ := h1 k h_p
  obtain ⟨k'', h_k'', h_r⟩ := h2 k' h_q
  use k'' ; constructor
  · omega
  · assumption

theorem leads_to_cases {p q r s : Set X}
    (h1 : LeadsTo xs (p ∩ q) r) (h2 : LeadsTo xs (p ∩ qᶜ) s) : LeadsTo xs p (r ∪ s) := by
  intro k h_p
  rcases Classical.em (xs k ∈ q) with h_q | h_not_q
  · let h_pq : xs k ∈ p ∩ q := by tauto
    obtain ⟨k', h_k', h_r⟩ := h1 k h_pq
    use k' ; simp [h_k', h_r]
  . let h_pq : xs k ∈ p ∩ qᶜ := by tauto
    obtain ⟨k', h_k', h_s⟩ := h2 k h_pq
    use k' ; simp [h_k', h_s]

theorem leads_to_until_frequently_1 {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∉ p) : LeadsTo xs p q := by
  intro k h_p
  by_contra! h_q
  have h_p' : ∀ k' ≥ k, xs k' ∈ p := by
    intro k' h_k'
    simp [le_iff_exists_add] at h_k'
    obtain ⟨n, h_k'⟩ := h_k'
    revert k' h_k'
    induction' n with n h_ind <;> intro k' h_k' <;> simp [h_k']
    · assumption
    have h_pq_n : xs (k + n) ∈ p ∩ qᶜ := by
      have h_q_n := h_q (k + n) (by omega)
      simp [h_q_n]
      exact h_ind (k + n) (rfl)
    exact h1 (k + n) h_pq_n
  rw [frequently_atTop] at h2
  obtain ⟨k', h_k', h_not_p⟩ := h2 k
  have := h_p' k' h_k'
  contradiction

theorem leads_to_until_frequently_2 {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∈ q) : LeadsTo xs p (p ∩ q) := by
  intro k h_p
  by_contra! h_not_pq
  have h_p_not_q : ∀ k' ≥ k, xs k' ∈ p ∩ qᶜ := by
    intro k' h_k'
    simp [le_iff_exists_add] at h_k'
    obtain ⟨n, h_k'⟩ := h_k'
    revert k' h_k'
    induction' n with n h_ind <;> intro k' h_k' <;> simp [h_k']
    · have h_not_pq' := h_not_pq k (by omega)
      tauto
    have h_n := h_ind (k + n) (rfl)
    have h_n_p := h1 (k + n) h_n
    have h_n_q := h_not_pq (k + n + 1) (by omega)
    simp [h_n_p] at h_n_q
    simp [← add_assoc] ; tauto
  rw [frequently_atTop] at h2
  obtain ⟨k', h_k', h_q'⟩ := h2 k
  have := (h_p_not_q k' h_k').2
  contradiction

theorem frequently_leads_to_frequently {p q : Set X}
    (h1 : ∃ᶠ k in atTop, xs k ∈ p) (h2 : LeadsTo xs p q) : ∃ᶠ k in atTop, xs k ∈ q := by
  rw [frequently_atTop] at h1 ⊢
  intro k0
  obtain ⟨k1, h_k1, h_k1_p⟩ := h1 k0
  obtain ⟨k2, h_k2, h_k2_q⟩ := h2 k1 h_k1_p
  use k2 ; constructor
  · omega
  · assumption

end Sequences

section Segments

open Classical

noncomputable def Segment (φ : ℕ → ℕ) (k : ℕ) :=
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

end Segments
