/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences

/-!
This file contains some definitions and theorems for doing
"temporal reasoning" over infinite sequences.  They are used to
prove that omega-regular languages are closed under intersection.
-/

open Function Set Filter

section Temporal

def Step {X : Type*} (xs : ℕ → X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → xs (k + 1) ∈ q

def LeadsTo {X : Type*} (xs : ℕ → X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → ∃ k' ≥ k, xs k' ∈ q

variable {X : Type*} {xs : ℕ → X}

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

end Temporal
