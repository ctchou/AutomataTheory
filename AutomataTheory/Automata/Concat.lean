/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Languages.Basic
import AutomataTheory.Automata.Basic

/-!
The concatenation of automaton M0 followed by automaton M1.
This construction is used to prove that the regular languages are closed
under concatenation and the concatenation of a regular language followed
by an ω-regular language is an ω-regular language.  This contruction works
even when the state types are infinite.
-/

open Function Set Filter Sum
open Classical

section AutomataConcat

variable {A : Type*}

def Automaton.Concat (M0 : Automaton A) (acc0 : Set M0.State) (M1 : Automaton A) : Automaton A where
  State := M0.State ⊕ M1.State
  init := inl '' M0.init
  next := fun s a ↦ match (s) with
    | inl s0 => inl '' (M0.next s0 a) ∪
                inr '' { s1' | (s0 ∈ acc0 ∧ ∃ s1 ∈ M1.init, s1' ∈ M1.next s1 a) }
    | inr s1 => inr '' (M1.next s1 a)

variable {M0 M1 : Automaton A} {acc0 : Set M0.State}

private lemma not_M0_state {s : (M0.Concat acc0 M1).State}
    (h : ¬ ∃ s0, s = inl s0) : ∃ s1, s = inr s1 := by
  rw [← isLeft_iff, not_isLeft] at h
  simpa [← isRight_iff]

private lemma not_M1_state {s : (M0.Concat acc0 M1).State}
    (h : ¬ ∃ s1, s = inr s1) : ∃ s0, s = inl s0 := by
  rw [← isRight_iff, not_isRight] at h
  simpa [← isLeft_iff]

theorem automata_concat_fin_run_0 {m : ℕ} {as : ℕ → A} {ss : ℕ → (M0.Concat acc0 M1).State} :
    (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s0, ss m = inl s0) ↔
    (∃ ss0, M0.FinRun m as ss0 ∧ ∀ k < m + 1, ss k = inl (ss0 k)) := by
  constructor
  · rintro ⟨⟨h_init, h_next⟩, ⟨s0_m, h_s0_m⟩⟩
    have h_all0 : ∀ k < m + 1, ∃ s0, ss k = inl s0 := by
      by_contra h_contra
      simp only [not_forall] at h_contra
      obtain ⟨n, h_n, h_ss_n⟩ := h_contra
      obtain ⟨s1, h_ss_n⟩ := not_M0_state h_ss_n
      have h_contra : ∀ k < m - n + 1, ∃ s1, ss (k + n) = inr s1 := by
        intro k h_k ; induction' k with k k_ind
        · use s1 ; simpa
        obtain ⟨s1', h_s1'⟩ := k_ind (by omega)
        have h_next_k := h_next (k + n) (by omega)
        simp [h_s1', Automaton.Concat] at h_next_k
        obtain ⟨s1'', _, h_s1''⟩ := h_next_k
        use s1'' ; rw [h_s1''] ; congr 1 ; omega
      obtain ⟨s1_m, h_s1_m⟩ := h_contra (m - n) (by omega)
      simp [(by omega: m - n + n = m), h_s0_m] at h_s1_m
    choose ss0 h_ss0 using h_all0
    use (fun k ↦ if h : k < m + 1 then ss0 k h else s0_m)
    constructor <;> [constructor ; skip]
    · simp [h_ss0 0 (by omega), Automaton.Concat] at h_init
      simpa
    · intro k h_k
      have h_next_k := h_next k h_k
      simp [h_ss0 k (by omega), h_ss0 (k + 1) (by omega), Automaton.Concat] at h_next_k
      simpa [h_k, (by omega : k < m + 1)]
    · intro k h_k ; simp [h_k, h_ss0 k h_k]
  · rintro ⟨ss0, ⟨h_init0, h_next0⟩, h_ss0⟩
    constructor <;> [constructor ; skip]
    · simpa [h_ss0 0 (by omega), Automaton.Concat]
    · intro k h_k
      simp [h_ss0 k (by omega), h_ss0 (k + 1) (by omega), Automaton.Concat]
      exact h_next0 k h_k
    · use (ss0 m) ; exact h_ss0 m (by omega)

theorem automata_concat_fin_run_1 {m : ℕ} {as : ℕ → A} {ss : ℕ → (M0.Concat acc0 M1).State} :
    (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s1, ss m = inr s1) ↔
    ∃ n < m, (∃ ss0, M0.FinRun n as ss0 ∧ ss0 n ∈ acc0 ∧ ∀ k < n + 1, ss k = inl (ss0 k)) ∧
             (∃ ss1, M1.FinRun (m - n) (as <<< n) ss1 ∧ ∀ k ≥ n + 1, k < m + 1 → ss k = inr (ss1 (k - n))) := by
  constructor
  · rintro ⟨⟨⟨s0, h_s0_init, h_s0⟩, h_next⟩, h_sm⟩
    have h_n : ∃ n s1, ss n = inr s1 := by use m
    use (Nat.find h_n - 1)
    have h_n_pos : 0 < Nat.find h_n := by
      by_contra
      have h_n_0 : Nat.find h_n = 0 := by omega
      obtain ⟨s1, h_s1⟩ := Nat.find_spec h_n
      rw [h_n_0] at h_s1
      simp [← h_s0] at h_s1
    have h_n_dec_inc := Nat.sub_one_add_one_eq_of_pos h_n_pos
    have h_ss0 : ∀ k < Nat.find h_n, ∃ s0, ss k = inl s0 := by
      intro k h_k ; exact not_M1_state (Nat.find_min h_n h_k)
    choose ss0 h_ss0 using h_ss0
    have h_n' : Nat.find h_n - 1 < Nat.find h_n := by omega
    have h_ss_n' := h_ss0 (Nat.find h_n - 1) h_n'
    obtain ⟨sn, h_ss_n⟩ := Nat.find_spec h_n
    have h_n_m := Nat.find_min' h_n h_sm
    have h_next_n := h_next (Nat.find h_n - 1) (by omega)
    simp [h_ss_n', h_ss_n, h_n_dec_inc, Automaton.Concat] at h_next_n
    obtain ⟨h_n'_acc, ⟨sn1, h_sn1_init, h_sn1_next⟩⟩ := h_next_n
    simp only [h_n_dec_inc]
    constructor <;> [skip ; constructor]
    . omega
    · use (fun k ↦ if h : k < Nat.find h_n then ss0 k h else s0)
      constructor <;> [constructor ; constructor]
      · have h_ss_0 := h_ss0 0 h_n_pos
        rw [← h_s0, inl.inj_iff] at h_ss_0
        simpa [h_n_pos, ← h_ss_0]
      · intro k h_k
        have h_k0 : k < Nat.find h_n := by omega
        have h_k1 : k + 1 < Nat.find h_n := by omega
        have h_ss_k0 := h_ss0 k h_k0
        have h_ss_k1 := h_ss0 (k + 1) h_k1
        have h_next_k := h_next k (by omega)
        simp [h_ss_k0, h_ss_k1, Automaton.Concat] at h_next_k
        simpa [h_k0, h_k1]
      · simpa [h_n']
      · intro k h_k ; simp [h_k, h_ss0 k h_k]
    · have h_ss1 : ∀ k < m - Nat.find h_n + 1, ∃ s1, ss (k + Nat.find h_n) = inr s1 := by
        intro k h_k ; induction' k with k k_ind
        · use sn ; simpa
        obtain ⟨sk, h_sk⟩ := k_ind (by omega)
        have h_next_k := h_next (k + Nat.find h_n) (by omega)
        simp [h_sk, Automaton.Concat] at h_next_k
        rcases h_next_k with ⟨sk1, _, h_sk1⟩
        use sk1 ; rw [h_sk1] ; congr 1 ; omega
      choose ss1 h_ss1 using h_ss1
      use (fun k ↦ if k = 0 then sn1 else if h : k < m - Nat.find h_n + 2 then ss1 (k - 1) (by omega) else sn1)
      constructor <;> [constructor ; skip]
      · simpa
      · intro k h_k_m
        rcases (by omega : k = 0 ∨ k ≠ 0) with h_k | h_k
        · have h_ss_n'' := h_ss1 0
          simp [h_ss_n] at h_ss_n''
          rw [inr.inj_iff] at h_ss_n''
          simpa [instSuffixFrom, SuffixFrom, h_k, ← h_ss_n'']
        · have h_k0 : k - 1 + Nat.find h_n + 1 = k + Nat.find h_n := by omega
          have h_next_k := h_next (k - 1 + Nat.find h_n) (by omega)
          simp [Automaton.Concat, h_k0, h_ss1 (k - 1) (by omega)] at h_next_k
          obtain ⟨sk1, h_sk1_next, h_sk1⟩ := h_next_k
          have h_k1 : k < m - Nat.find h_n + 1 := by omega
          have h_k2 : k < m - Nat.find h_n + 2 := by omega
          have h_k3 : k + (Nat.find h_n - 1) = (k - 1) + Nat.find h_n := by omega
          rw [h_ss1 k (by omega), inr.inj_iff] at h_sk1
          simpa [instSuffixFrom, SuffixFrom, h_k, h_k1, h_k2, h_k3, ← h_sk1]
      · intro k h_k h_k_m
        have h_k1 : k - (Nat.find h_n - 1) ≠ 0 := by omega
        have h_k2 : (k - (Nat.find h_n - 1) - 1) = k - Nat.find h_n := by omega
        have h_k3 : k - (Nat.find h_n - 1) < m - Nat.find h_n + 2 := by omega
        simp [h_k1, h_k2, h_k3, ← h_ss1 (k - Nat.find h_n)]
        congr ; omega
  · rintro ⟨n, h_n, ⟨ss0, ⟨h_init0, h_next0⟩, h_acc0, h_ss0⟩, ⟨ss1, ⟨h_init1, h_next1⟩, h_ss1⟩⟩
    constructor <;> [constructor ; skip]
    · simpa [h_ss0 0 (by omega), Automaton.Concat]
    · intro k h_k'
      rcases (by omega : k < n ∨ k = n ∨ k > n) with h_k | h_k | h_k
      · have h_next_k := h_next0 k h_k
        simpa [h_ss0 k (by omega), h_ss0 (k + 1) (by omega), Automaton.Concat]
      · obtain ⟨rfl⟩ := h_k
        have h_next_k := h_next1 0 (by omega)
        simp [instSuffixFrom, SuffixFrom] at h_next_k
        simp [h_ss0 n (by omega), h_ss1 (n + 1) (by omega) (by omega), Automaton.Concat, h_acc0]
        use (ss1 0)
      · have h_next_k := h_next1 (k - n) (by omega)
        simp [instSuffixFrom, SuffixFrom, (by omega : k - n + n = k), (by omega : k - n + 1 = k + 1 - n)] at h_next_k
        simpa [h_ss1 k (by omega) (by omega), h_ss1 (k + 1) (by omega) (by omega), Automaton.Concat]
    . have := h_ss1 m (by omega) (by omega)
      use (ss1 (m - n))

theorem automata_concat_inf_run {as : ℕ → A} {ss : ℕ → (M0.Concat acc0 M1).State} :
    (M0.Concat acc0 M1).InfRun as ss ∧ (∃ n s1, ss n = inr s1) ↔
    ∃ n, (∃ ss0, M0.FinRun n as ss0 ∧ ss0 n ∈ acc0 ∧ ∀ k < n + 1, ss k = inl (ss0 k)) ∧
         (∃ ss1, M1.InfRun (as <<< n) ss1 ∧ ∀ k ≥ n + 1, ss k = inr (ss1 (k - n))) := by
  constructor
  · rintro ⟨⟨⟨s0, h_s0_init, h_s0⟩, h_next⟩, h_n⟩
    use (Nat.find h_n - 1)
    have h_n_pos : 0 < Nat.find h_n := by
      by_contra
      have h_n_0 : Nat.find h_n = 0 := by omega
      obtain ⟨s1, h_s1⟩ := Nat.find_spec h_n
      rw [h_n_0] at h_s1
      simp [← h_s0] at h_s1
    have h_n_dec_inc := Nat.sub_one_add_one_eq_of_pos h_n_pos
    have h_ss0 : ∀ k < Nat.find h_n, ∃ s0, ss k = inl s0 := by
      intro k h_k ; exact not_M1_state (Nat.find_min h_n h_k)
    choose ss0 h_ss0 using h_ss0
    have h_n' : Nat.find h_n - 1 < Nat.find h_n := by omega
    have h_ss_n' := h_ss0 (Nat.find h_n - 1) h_n'
    obtain ⟨sn, h_ss_n⟩ := Nat.find_spec h_n
    have h_next_n := h_next (Nat.find h_n - 1)
    simp [h_ss_n', h_ss_n, h_n_dec_inc, Automaton.Concat] at h_next_n
    obtain ⟨h_n'_acc, ⟨sn1, h_sn1_init, h_sn1_next⟩⟩ := h_next_n
    simp only [h_n_dec_inc] ; constructor
    · use (fun k ↦ if h : k < Nat.find h_n then ss0 k h else s0)
      constructor <;> [constructor ; constructor]
      · have h_ss_0 := h_ss0 0 h_n_pos
        rw [← h_s0, inl.inj_iff] at h_ss_0
        simpa [h_n_pos, ← h_ss_0]
      · intro k h_k
        have h_k0 : k < Nat.find h_n := by omega
        have h_k1 : k + 1 < Nat.find h_n := by omega
        have h_ss_k0 := h_ss0 k h_k0
        have h_ss_k1 := h_ss0 (k + 1) h_k1
        have h_next_k := h_next k
        simp [h_ss_k0, h_ss_k1, Automaton.Concat] at h_next_k
        simpa [h_k0, h_k1]
      · simpa [h_n']
      · intro k h_k ; simp [h_k, h_ss0 k h_k]
    · have h_ss1 : ∀ k, ∃ s1, ss (k + Nat.find h_n) = inr s1 := by
        intro k ; induction' k with k k_ind
        · use sn ; simpa
        rcases k_ind with ⟨sk, h_sk⟩
        have h_next_k := h_next (k + Nat.find h_n)
        simp [h_sk, Automaton.Concat] at h_next_k
        rcases h_next_k with ⟨sk1, _, h_sk1⟩
        use sk1 ; rw [h_sk1] ; congr 1 ; omega
      choose ss1 h_ss1 using h_ss1
      use (fun k ↦ if k = 0 then sn1 else ss1 (k - 1))
      constructor <;> [constructor ; skip]
      · simpa
      · intro k
        rcases (by omega : k = 0 ∨ k ≠ 0) with h_k | h_k
        · have h_ss_n'' := h_ss1 0
          simp [h_ss_n] at h_ss_n''
          rw [inr.inj_iff] at h_ss_n''
          simpa [instSuffixFrom, SuffixFrom, h_k, ← h_ss_n'']
        · have h_next_k := h_next ((k - 1) + Nat.find h_n)
          rw [(by omega : k = (k - 1) + 1)] at h_next_k
          simp [(by omega : (k - 1 + Nat.find h_n + 1) = k + Nat.find h_n)] at h_next_k
          simp [h_ss1, Automaton.Concat] at h_next_k
          simpa [instSuffixFrom, SuffixFrom, h_k, (by omega : k + (Nat.find h_n - 1) = (k - 1) + Nat.find h_n)]
      · intro k h_k
        have h_k1 : k - (Nat.find h_n - 1) ≠ 0 := by omega
        have h_k2 : (k - (Nat.find h_n - 1) - 1) = k - Nat.find h_n := by omega
        simp [h_k1, h_k2, ← h_ss1 (k - Nat.find h_n)]
        congr ; omega
  · rintro ⟨n, ⟨ss0, ⟨h_init0, h_next0⟩, h_acc0, h_ss0⟩, ⟨ss1, ⟨h_init1, h_next1⟩, h_ss1⟩⟩
    constructor <;> [constructor ; skip]
    · simpa [h_ss0 0 (by omega), Automaton.Concat]
    · intro k
      rcases (by omega : k < n ∨ k = n ∨ k > n) with h_k | h_k | h_k
      · have h_next_k := h_next0 k h_k
        simpa [h_ss0 k (by omega), h_ss0 (k + 1) (by omega), Automaton.Concat]
      · obtain ⟨rfl⟩ := h_k
        have h_next_k := h_next1 0
        simp [instSuffixFrom, SuffixFrom] at h_next_k
        simp [h_ss0 n (by omega), h_ss1 (n + 1) (by omega), Automaton.Concat, h_acc0]
        use (ss1 0)
      · have h_next_k := h_next1 (k - n)
        simp [instSuffixFrom, SuffixFrom, (by omega : k - n + n = k), (by omega : k - n + 1 = k + 1 - n)] at h_next_k
        simpa [h_ss1 k (by omega), h_ss1 (k + 1) (by omega), Automaton.Concat]
    . have := h_ss1 (n + 1) (by omega)
      use (n + 1), (ss1 (n + 1 - n))

end AutomataConcat

section AcceptedLangConcat

variable {A : Type*} {M0 M1 : Automaton A} {acc0 : Set M0.State} {acc1 : Set M1.State}

theorem accepted_lang_concat_e :
    (M0.Concat acc0 M1).AcceptedLang (inl '' acc0) = M0.AcceptedLang acc0 := by
  ext al ; constructor
  · rintro ⟨m, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    have h_m : ∃ s0, ss m = inl s0 := by
      obtain ⟨s0, _, h_s0⟩ := h_acc
      use s0 ; simp [h_s0]
    obtain ⟨ss0, h_run0,h_ss0⟩ := automata_concat_fin_run_0.mp ⟨h_run, h_m⟩
    use m, as ; simp [h_al]
    use ss0 ; simp [h_run0]
    obtain ⟨sm, h_sm_acc, h_sm⟩ := h_acc
    rw [h_ss0 m (by omega), inl.inj_iff] at h_sm
    simpa [← h_sm]
  · rintro ⟨m, as, ⟨ss0, h_run0, h_acc0⟩, h_al⟩
    use m, as ; simp [h_al]
    let ss : ℕ → (M0.Concat acc0 M1).State := inl ∘ ss0
    use ss ; constructor
    · suffices (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s0, ss m = inl s0) by tauto
      apply automata_concat_fin_run_0.mpr
      use ss0 ; simp [h_run0]
      intro k h_k ; simp [ss]
    · simp [ss] ; use (ss0 m)

theorem accepted_lang_concat_ne :
    (M0.Concat acc0 M1).AcceptedLang (inr '' acc1) =
    (M0.AcceptedLang acc0) * (M1.AcceptedLang acc1 \ {[]}) := by
  ext al ; constructor
  · rintro ⟨m, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    have h_s1_ex : ∃ s1, ss m = inr s1 := by
      rcases h_acc with ⟨s1, _, h_s1⟩
      use s1 ; rw [h_s1]
    obtain ⟨n, h_n, ⟨ss0, h_run0, h_acc0, h_ss0⟩, ⟨ss1, h_run1, h_ss1⟩⟩ := automata_concat_fin_run_1.mp ⟨h_run, h_s1_ex⟩
    use (List.ofFn (fun k : Fin n ↦ as k))
    use (List.ofFn (fun k : Fin (m - n) ↦ as (k + n)))
    constructor <;> [skip ; constructor]
    · use n, as ; simp ; use ss0
    · constructor
      · use (m - n), (as <<< n)
        constructor
        · use ss1 ; simp [h_run1]
          obtain ⟨s1, h_acc1, h_s1⟩ := h_ss1 m (by omega) (by omega) ▸ h_acc
          simpa [← inr.inj h_s1]
        · ext k a ; simp [instSuffixFrom, SuffixFrom]
      · simp ; omega
    · rw [h_al, ← ofFn_of_append_ofFn_oFn (show n ≤ m by omega)]
  . rintro ⟨al0, al1, h_al0, h_al1, h_al⟩
    obtain ⟨h_al1, h_al1_ne⟩ := h_al1
    simp at h_al1_ne
    rcases h_al0 with ⟨n, as0, ⟨⟨ss0, ⟨h_init0, h_next0⟩, h_acc0⟩, h_al0⟩⟩
    rcases h_al1 with ⟨m, as1, ⟨⟨ss1, ⟨h_init1, h_next1⟩, h_acc1⟩, h_al1⟩⟩
    have h_m : 0 < m := by
      have h_len : m = al1.length := by simp [h_al1, List.length_ofFn]
      simp [h_len, List.length_pos_iff.mpr h_al1_ne]
    let as := fun k ↦ if k < n then as0 k else as1 (k - n)
    use (n + m), as
    constructor
    · let ss := fun k ↦ if k < n + 1 then inl (ss0 k) else inr (ss1 (k - n))
      use ss
      have h_ss_nm : ss (n + m) = inr (ss1 m) := by
        have h_m1 : ¬ n + m < n + 1 := by omega
        simp [ss, h_m1]
      constructor
      · suffices (M0.Concat acc0 M1).FinRun (n + m) as ss ∧ (∃ s1, ss (n + m) = inr s1) by tauto
        apply automata_concat_fin_run_1.mpr
        use n ; constructor <;> [skip ; constructor]
        · omega
        · use ss0 ; simp [as, ss, h_acc0] ; constructor
          · exact h_init0
          · intro k h_k ; simp [h_k, h_next0 k h_k]
        · use ss1 ; constructor <;> [constructor ; skip]
          · exact h_init1
          · simp [instSuffixFrom, SuffixFrom, as] ; exact h_next1
          · simp [ss] ; omega
      · use (ss1 m)
        simp [h_acc1, h_ss_nm]
    · rw [h_al, ofFn_of_append_ofFn_oFn (by omega : n ≤ n + m)] ; congr
      · simp [as, h_al0]
      · simp [as, h_al1]

theorem accepted_omega_lang_concat :
    (M0.Concat acc0 M1).AcceptedOmegaLang (inr '' acc1) =
    (M0.AcceptedLang acc0) * (M1.AcceptedOmegaLang acc1) := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_acc⟩
    obtain ⟨n, s1, h_s1_acc, h_s1⟩ := Frequently.exists h_acc
    have h_s1_ex : ∃ n s1, ss n = inr s1 := by use n, s1 ; simp [h_s1]
    obtain ⟨n, ⟨ss0, h_run0, h_acc0, h_ss0⟩, ⟨ss1, h_run1, h_ss1⟩⟩ := automata_concat_inf_run.mp ⟨h_run, h_s1_ex⟩
    use (List.ofFn (fun k : Fin n ↦ as k)), (as <<< n)
    constructor <;> [skip ; constructor]
    · use n, as ; simp ; use ss0
    · use ss1 ; simp [h_run1]
      have h_ss1_ev : ∀ᶠ k in atTop, ss k = inr (ss1 (k - n)) := by
        simp only [eventually_atTop] ; use (n + 1)
      have h_ss1_acc := Frequently.and_eventually h_acc h_ss1_ev
      simp [frequently_atTop] at h_ss1_acc ⊢
      intro k ; obtain ⟨j, h_j, ⟨t1, h_t1_acc, h_t1⟩, h_j_ss1⟩ := h_ss1_acc (n + k)
      use (j - n) ; rw [← h_t1, inr.inj_iff] at h_j_ss1
      simpa [(by omega : k ≤ j - n), ← h_j_ss1]
    · exact appendListInf_ofFnPrefix_SuffixFrom
  · rintro ⟨al0, as1, ⟨n, as0, ⟨ss0, ⟨h_init0, h_next0⟩, h_acc0⟩, h_al0⟩, ⟨ss1, h_run1, h_acc1⟩, h_as⟩
    let ss := fun k ↦ if k < n + 1 then inl (ss0 k) else inr (ss1 (k - n))
    use ss  ; constructor
    · suffices (M0.Concat acc0 M1).InfRun as ss ∧ (∃ n s1, ss n = inr s1) by tauto
      apply automata_concat_inf_run.mpr
      use n ; constructor
      · use ss0 ; simp [ss, h_acc0] ; constructor
        · exact h_init0
        · intro k h_k ; simp [h_as, h_al0, instAppendListInf, AppendListInf, h_k]
          exact h_next0 k (by omega)
      · use ss1
        have h_len : n = al0.length := by simp [h_al0, List.length_ofFn]
        simpa [ss, h_as, h_len, ← suffixFrom_listLength_AppendListInf]
    · have h_ss1_ev : ∀ᶠ k in atTop, ss (k + n) = inr (ss1 k) := by
        simp only [eventually_atTop]
        use (n + 1) ; intro k h_k ; simp [ss] ; omega
      have h_ss1_acc := Frequently.and_eventually h_acc1 h_ss1_ev
      simp [frequently_atTop] at h_ss1_acc ⊢
      intro k ; obtain ⟨j, h_j, h_j_acc, h_j_ss1⟩ := h_ss1_acc (n + k)
      use (j + n) ; simp [(by omega : k ≤ j + n)]
      use (ss1 j) ; simp [h_j_acc, h_j_ss1]

end AcceptedLangConcat
