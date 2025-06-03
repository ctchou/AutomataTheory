/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib
-- import Mathlib.Algebra.Order.Ring.Nat
-- import Mathlib.Algebra.Order.Sub.Basic
import AutomataTheory.Languages
import AutomataTheory.AutomataBasic

open Function Set Sum Filter
open Classical

section AutomataLoop

variable {A : Type*}

def AutomataLoop (M : Automaton A) (acc : Set M.State) : Automaton A where
  State := Unit ⊕ M.State
  init := {inl ()}
  next := fun s a ↦ match (s) with
    | inl () => inr '' { s' | ∃ s0 ∈ M.init, s' ∈ M.next s0 a } ∪
                if ∃ s0 ∈ M.init, ∃ s' ∈ acc, s' ∈ M.next s0 a then {inl ()} else ∅
    | inr s  => inr '' (M.next s a) ∪
                if ∃ s' ∈ acc, s' ∈ M.next s a then {inl ()} else ∅

variable {M : Automaton A} {acc : Set M.State}

private lemma not_inl_unit {s : (AutomataLoop M acc).State} :
    s ≠ inl () ↔ ∃ s' : M.State, s = inr s' := by
  constructor
  · rw [← isRight_iff, ← not_isLeft, isLeft_iff]
    rintro h1 ⟨u, h_s⟩
    have h_u := Unit.ext u ()
    simp [h_s] at h1
  · rintro ⟨s', h_s'⟩ ; simp [h_s']

theorem automata_loop_fin_run_0 {as : ℕ → A} {ss : ℕ → (AutomataLoop M acc).State} :
    FinRun (AutomataLoop M acc) 0 as ss ∧ (∃ s0 ∈ M.init, s0 ∈ acc) ↔
    ∃ ss', FinRun M 0 as ss' ∧ ss' 0 ∈ acc ∧ ss 0 = inl () := by
  constructor
  · rintro ⟨⟨h_init, _⟩, s0, h_s0_init, h_s0_acc⟩
    simp [AutomataLoop] at h_init
    use (fun k ↦ s0)
    simp [FinRun, h_s0_init, h_s0_acc, h_init]
  · rintro ⟨ss', ⟨h_init, _⟩, h_acc, h_inl⟩
    simp [FinRun, AutomataLoop, h_inl]
    use (ss' 0)

theorem automata_loop_fin_run_1 {n : ℕ} {as : ℕ → A} {ss : ℕ → (AutomataLoop M acc).State} (h : n > 0) :
    FinRun (AutomataLoop M acc) n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k ∈ range inr) ↔
    ∃ ss', FinRun M n as ss' ∧ ss' n ∈ acc ∧ ss 0 = inl () ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by
  constructor
  · rintro ⟨⟨h_init, h_next⟩, h_inl_n, h_inr⟩
    simp [AutomataLoop] at h_init
    rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
    · obtain ⟨rfl⟩ := h_n
      specialize h_next 0 (by omega)
      simp [h_init, h_inl_n, AutomataLoop] at h_next
      obtain ⟨s0, h_s0, s1, h_acc, h_next⟩ := h_next
      use (fun k ↦ if k = 0 then s0 else if k = 1 then s1 else s0)
      simp [h_init, h_acc, h_inl_n, FinRun, h_s0, h_next]
--    · obtain ⟨s1, _, h_s1⟩ := h_inr 1 h_n (by omega)
    · obtain ⟨s1, h_s1⟩ := h_inr 1 h_n (by omega)
      have h_next_0 := h_next 0 h
      simp [h_init, ← h_s1, AutomataLoop] at h_next_0
      obtain ⟨s0, h_s0, h_next_0⟩ := h_next_0
      obtain ⟨sn1, h_sn1⟩ := h_inr (n - 1) (by omega) (by omega)
      have h_next_n1 := h_next (n - 1) (by omega)
      have h_n1 : n - 1 + 1 = n := by omega
      simp [h_n1, h_inl_n, ← h_sn1, AutomataLoop] at h_next_n1
      obtain ⟨sn, h_sn, h_next_n1⟩ := h_next_n1
      have h_ss' : ∀ k, k > 0 → k < n → ∃ ss', ss k = inr ss' := by
        intro k h_k_0 h_k_n
        obtain ⟨s', h_s'⟩ := h_inr k h_k_n h_k_0
        use s' ; simp [h_s']
      choose ss' h_ss' using h_ss'
      use (fun k ↦ if h0 : k = 0 then s0 else if hn : k < n then ss' k (by omega) hn else if k = n then sn else s0)
      simp [(show n ≠ 0 by omega), h_init, h_inl_n, h_sn, FinRun, h_s0]
      constructor
      · intro k h_k_n
        rcases (show k = 0 ∨ k = n - 1 ∨ k > 0 ∧ k < n - 1 by omega) with h_k_0 | h_k_n' | ⟨h_k_0, h_k_n'⟩
        · obtain ⟨rfl⟩ := h_k_0
          have h_ss_1 := h_ss' 1 (by omega) (h_n)
          rw [← h_s1, inr.inj_iff] at h_ss_1
          simp [h_n, ← h_ss_1, h_next_0]
        · obtain ⟨rfl⟩ := h_k_n'
          have h_ss_n1 := h_ss' (n - 1) (by omega) h_k_n
          rw [← h_sn1, inr.inj_iff] at h_ss_n1
          simp [(show n - 1 + 1 = n by omega), (show n - 1 ≠ 0 by omega), h, ← h_ss_n1, h_next_n1]
        · have h_ss_k := h_ss' k h_k_0 h_k_n
          have h_ss_k1 := h_ss' (k + 1) (by omega) (by omega)
          have h_next_k := h_next k h_k_n
          simp [h_ss_k, h_ss_k1, AutomataLoop] at h_next_k
          simp [(show k + 1 < n by omega), (show k ≠ 0 by omega), h_k_n, h_next_k]
      · intro k h_k_n h_k_0
        simp [h_k_n, h_k_0, (show k ≠ 0 by omega), h_ss']
  · rintro ⟨ss', ⟨h_init, h_next⟩, h_acc, h_inl_0, h_inl_n, h_inr⟩
    constructor <;> [constructor ; constructor]
    · simp [h_inl_0, AutomataLoop]
    · intro k h_k_n
      rcases (show k = 0 ∨ k > 0 by omega) with h_k_0 | h_k_0
      · specialize h_next 0 h
        rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
        · obtain ⟨rfl⟩ := h_n
          simp [h_k_0, h_inl_0, AutomataLoop, h_inl_n]
          use (ss' 0) ; simp [h_init] ; use (ss' 1)
        · specialize h_inr 1 h_n (by omega)
          simp [h_k_0, h_inl_0, AutomataLoop, h_inr]
          use (ss' 0)
      · specialize h_next k (h_k_n)
        have h_ss_k := h_inr k h_k_n h_k_0
        rcases (show k + 1 < n ∨ k = n - 1 by omega) with h_k_n' | h_k_n'
        · have h_ss_k' := h_inr (k + 1) h_k_n' (by omega)
          simpa [h_ss_k, h_ss_k', AutomataLoop]
        · obtain ⟨rfl⟩ := h_k_n'
          have h_n1 : n - 1 + 1 = n := by omega
          simp [h_n1] at h_next
          simp [h_n1, h_ss_k, h_inl_n, AutomataLoop]
          use (ss' n)
    · exact h_inl_n
    · intro k h_k_n h_k_0
      simp [h_inr k h_k_n h_k_0]

end AutomataLoop

section AcceptedLangLoop

end AcceptedLangLoop

variable {A : Type*} {M : Automaton A} {acc : Set M.State}

theorem accepted_lang_loop :
    AcceptedLang (AutomataLoop M acc) {inl ()} = IterStar (AcceptedLang M acc) := by
  sorry

lemma nth_succ_gap {p : ℕ → Prop} (hf : (setOf p).Infinite) (n : ℕ) :
    ∀ k < Nat.nth p (n + 1) - Nat.nth p n, k > 0 → ¬ p (k + Nat.nth p n) := by
  intro k h_k1 h_k0 h_p_k
  let m := Nat.count p (k + Nat.nth p n)
  have h_k_ex : Nat.nth p m = k + Nat.nth p n := by simp [m, Nat.nth_count h_p_k]
  have h_n_m : n < m := by apply (Nat.nth_lt_nth hf).mp ; omega
  have h_m_n : m < n + 1 := by apply (Nat.nth_lt_nth hf).mp ; omega
  omega

theorem ofFn_eq_ofFn {X : Type*} {xs xs' : ℕ → X} {m n n' : ℕ}
    (h : List.ofFn (fun k : Fin (m - n) ↦ xs (k + n)) = List.ofFn (fun k : Fin n' ↦ xs' k)) :
    m - n = n' ∧ ∀ k < n', xs (k + n) = xs' k := by
  simp [List.ofFn_inj'] at h
  obtain ⟨rfl, h'⟩ := h
  simp [funext_iff, Fin.forall_iff] at h'
  simp ; intro k h_k
  specialize h' k h_k
  simp [h']

theorem automata_FinRun_modulo {n : ℕ} {as as' : ℕ → A} {ss ss' : ℕ → M.State}
    (ha : ∀ k < n, as k = as' k) (hs : ∀ k < n + 1, ss k = ss' k) (hr : FinRun M n as ss) : FinRun M n as' ss' := by
  rcases hr with ⟨h_init, h_next⟩ ; constructor
  · simpa [← hs]
  intro k h_k ; specialize h_next k h_k
  simpa [← ha k h_k, ← hs k (by omega), ← hs (k + 1) (by omega)]

noncomputable def Segment (φ : ℕ → ℕ) (k : ℕ) :=
  if k ∈ range φ then Nat.count (· ∈ range φ) k else Nat.count (· ∈ range φ) k - 1

variable {φ : ℕ → ℕ}

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

theorem accepted_omega_lang_loop :
    AcceptedOmegaLang (AutomataLoop M acc) {inl ()} = IterOmega (AcceptedLang M acc) := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_acc⟩ ; simp at h_acc
    let φ m := Nat.nth (fun k ↦ ss k = inl ()) m
    have h_inf : {k | ss k = inl ()}.Infinite := by simpa [← Nat.frequently_atTop_iff_infinite]
    have h_mono : StrictMono φ := by exact Nat.nth_strictMono h_inf
    use φ ; simp [h_mono] ; constructor
    · have h_init := h_run.1
      simp [AutomataLoop] at h_init
      apply Nat.nth_zero_of_zero h_init
    · intro m
      use (φ (m + 1) - φ m), (SuffixFrom (φ m) as) ; constructor
      · have h_mono_m : φ (m + 1) - φ m > 0 := by have := h_mono (show m < m + 1 by omega) ; omega
        let ss1 := SuffixFrom (φ m) ss
        have h_run1 : FinRun (AutomataLoop M acc) (φ (m + 1) - φ m) (SuffixFrom (φ m) as) ss1 := by
          constructor
          · simp [ss1, SuffixFrom, AutomataLoop]
            apply Nat.nth_mem_of_infinite (p := fun k ↦ ss k = inl ()) h_inf
          intro k h_k
          simp [ss1, SuffixFrom, (show k + 1 + φ m = k + φ m + 1 by omega), h_run.2 (k + φ m)]
        have h_inl : ss1 (φ (m + 1) - φ m) = inl () := by
          simp [ss1, SuffixFrom, (show φ (m + 1) - φ m + φ m = φ (m + 1) by omega)]
          apply Nat.nth_mem_of_infinite (p := fun k ↦ ss k = inl ()) h_inf
        have h_inr : ∀ k < φ (m + 1) - φ m, k > 0 → ss1 k ∈ range inr := by
          intro k h_k1 h_k0
          obtain ⟨s', h_s'⟩ := not_inl_unit.mp <| nth_succ_gap h_inf m k h_k1 h_k0
          simp ; use s' ; symm ; exact h_s'
        obtain ⟨ss', h_run', h_acc', _⟩ := (automata_loop_fin_run_1 h_mono_m).mp ⟨h_run1, h_inl, h_inr⟩
        use ss'
      · rw [List.ofFn_inj] ; ext k
        simp [SuffixFrom]
  · rintro ⟨φ, h_mono, h_0, h_acc⟩
    choose len as' h_acc h_as' using h_acc
    choose ss' h_run h_acc using h_acc
    let seg k := Segment φ k
    let ss k := if k ∈ range φ then inl () else inr (ss' (seg k) (k - φ (seg k)))
    use ss ; constructor <;> [constructor ; skip]
    · have h_0' : ∃ k, φ k = 0 := by use 0
      simp [ss, h_0', AutomataLoop]
    · intro k
      have h_seg_k : φ (seg k) ≤ k := by exact segment_lower_bound h_mono h_0 k
      have h_seg_k1 : k < φ (seg k + 1) := by exact segment_upper_bound h_mono h_0 k
      have h_mono_k : φ (seg k + 1) - φ (seg k) > 0 := by omega
      suffices h_lhs :
          FinRun (AutomataLoop M acc) (φ (seg k + 1) - φ (seg k)) (SuffixFrom (φ (seg k)) as) (SuffixFrom (φ (seg k)) ss) ∧
          (SuffixFrom (φ (seg k)) ss) (φ (seg k + 1) - φ (seg k)) = inl () ∧
          (∀ j < φ (seg k + 1) - φ (seg k), j > 0 → (SuffixFrom (φ (seg k)) ss) j ∈ range inr) by
        have h_run_k := h_lhs.1.2 (k - φ (seg k)) (show k - φ (seg k) < φ (seg k + 1) - φ (seg k) by omega)
        simp [SuffixFrom, (show k - φ (seg k) + φ (seg k) = k by omega), (show k - φ (seg k) + 1 + φ (seg k) = k + 1 by omega)] at h_run_k
        exact h_run_k
      apply (automata_loop_fin_run_1 h_mono_k).mpr
      use (ss' (seg k))
      obtain ⟨h_len_k, h_as'_k⟩ := ofFn_eq_ofFn <| h_as' (seg k)
      simp [h_len_k, SuffixFrom]
      constructorm* _ ∧ _
      · apply automata_FinRun_modulo (n := len (seg k)) (as := as' (seg k)) (ss := ss' (seg k)) (hr := h_run (seg k))
        · intro j h_j ; simp [SuffixFrom, h_as'_k j h_j]
        · simp
      · exact h_acc (seg k)
      · simp [ss]
      · simp [ss, (show len (seg k) + φ (seg k) = φ (seg k + 1) by omega)]
      · intro j h_j_1 h_j_0
        have h_j_2 : ¬ ∃ m, φ m = j + φ (seg k) := by
          exact segment_range_gap h_mono (show φ (seg k) < j + φ (seg k) by omega) (show j + φ (seg k) < φ (seg k + 1) by omega)
        have h_j_3 : seg (j + φ (seg k)) = seg k := by
          exact segment_range_val h_mono (show φ (seg k) ≤ j + φ (seg k) by omega) (show j + φ (seg k) < φ (seg k + 1) by omega)
        simp [ss, h_j_2, h_j_3]
    · have h_uset : {k | ss k = inl ()} = range φ := by ext k ; simp [ss]
      simp [Nat.frequently_atTop_iff_infinite, h_uset]
      exact strict_mono_infinite h_mono

section DeprecatedLoop

def AutomataLoop' (M : Automaton A) (acc : Set M.State) : Automaton A where
  State := M.State
  init := M.init
  next := fun s a ↦ M.next s a ∪ { s' | s ∈ acc ∧ ∃ s0 ∈ M.init, s' ∈ M.next s0 a }

variable {M : Automaton A} {acc : Set M.State}

theorem automata_loop_fin_accept {m : ℕ} {as : ℕ → A} :
    FinAccept (AutomataLoop' M acc) acc m as ↔
    ∃ n > 0, ∃ φ : ℕ → ℕ, Monotone φ ∧ φ 0 = 0 ∧ φ n = m ∧
      ∀ k < n, FinAccept M acc (φ (k + 1) - φ k) (SuffixFrom (φ k) as) := by
  constructor
  · rintro ⟨ss, h_run, h_acc⟩
    induction' m using Nat.strong_induction_on with m h_ind
    let loop k := k < m ∧ ss (k + 1) ∉ M.next (ss k) (as k)
    rcases Classical.em (∃ k, loop k) with h_loop | h_loop
    · have h_m : 0 < m := by omega
      let m' := Nat.findGreatest loop (m - 1)
      obtain ⟨h_m', h_notM'⟩ : m' < m ∧ ss (m' + 1) ∉ M.next (ss m') (as m') := by
        obtain ⟨k, h_k⟩ := h_loop
        exact Nat.findGreatest_spec (show k ≤ m - 1 by omega) h_k
      have h_next' := h_run.2 m' h_m'
      simp [AutomataLoop', h_notM'] at h_next'
      obtain ⟨h_acc', s0, h_s0_init, h_s0_next⟩ := h_next'
      have h_accept : FinAccept M acc (m - m') (SuffixFrom m' as) := by
        use (fun k ↦ if k = 0 then s0 else ss (k + m'))
        constructor <;> [constructor ; skip]
        · simpa
        · intro k h_k
          rcases Classical.em (k = 0) with h_k' | h_k'
          · simpa [SuffixFrom, h_k', (show 1 + m' = m' + 1 by omega)]
          · have h_next : ss (k + m' + 1) ∈ M.next (ss (k + m')) (as (k + m')) := by
              have h0 := Nat.findGreatest_is_greatest (show m' < k + m' by omega) (by omega)
              simp [loop, (show k + m' < m by omega)] at h0
              exact h0
            simpa [SuffixFrom, h_k', (show k + 1 + m' = k + m' + 1 by omega)]
        · simpa [(show m - m' ≠ 0 by omega), (show m - m' + m' = m by omega)]
      have h_run' : FinRun (AutomataLoop' M acc) m' as ss := by
        constructor
        · exact h_run.1
        intro k h_k ; exact h_run.2 k (by omega)
      obtain ⟨n', h_n', φ', h_mono', h_φ'_0, h_φ'_n', h_accept'⟩ := h_ind m' h_m' h_run' h_acc'
      use (n' + 1) ; simp [(show n' + 1 > 0 by omega)]
      use (fun k ↦ if k ≤ n' then φ' k else m)
      simp [h_φ'_0] ; constructor
      · apply monotone_nat_of_le_succ ; intro k
        rcases (show k < n' ∨ k = n' ∨ k > n' by omega) with h_k | h_k | h_k
        · simp [(show k ≤ n' by omega), (show k + 1 ≤ n' by omega)]
          exact h_mono' (show k ≤ k + 1 by omega)
        · simp [h_k, h_φ'_n'] ; omega
        · simp [(show ¬ k ≤ n' by omega), (show ¬ k + 1 ≤ n' by omega)]
      · intro k h_k
        rcases (show k < n' ∨ k = n' by omega) with h_k' | h_k'
        · simp [(show k ≤ n' by omega), (show k + 1 ≤ n' by omega)]
          exact h_accept' k h_k'
        · simpa [h_k', h_φ'_n']
    · simp [loop] at h_loop
      use 1 ; simp
      use (fun k ↦ if k = 0 then 0 else m)
      constructor
      · apply monotone_nat_of_le_succ ; intro k
        rcases (show k = 0 ∨ k ≠ 0 by omega) with h_k | h_k <;> simp [h_k]
      rcases (show m = 0 ∨ m ≠ 0 by omega) with h_0 | h_1
      · simp [h_0]
        use ss ; simp [h_0] at h_acc ; simp [h_acc]
        constructor
        · have h_init := h_run.1
          simp [AutomataLoop'] at h_init
          exact h_init
        · simp
      · simp [h_1]
        use ss ; simp [h_acc]
        constructor
        · have h_init := h_run.1
          simp [AutomataLoop'] at h_init
          exact h_init
        · exact h_loop
  · rintro ⟨n, h_n, φ, h_mono, h_0', h_φ_n, h_accept⟩
    revert m
    induction' n with n h_ind
    · omega
    rcases (show n = 0 ∨ n > 0 by omega) with h_n' | h_n'
    · simp [h_n', h_0'] at h_accept
      obtain ⟨ss, h_run, h_acc⟩ := h_accept
      simp [h_n'] ; use ss ; simp [h_acc] ; constructor
      · exact h_run.1
      intro k h_k
      have h_next := h_run.2 k h_k
      simp [SuffixFrom] at h_next
      simp [AutomataLoop', h_next]
    · have h_mono' : φ n ≤ φ (n + 1) := by apply h_mono ; omega
      have h_accept0 : (∀ k < n, FinAccept M acc (φ (k + 1) - φ k) (SuffixFrom (φ k) as)) := by
        intro k h_k ; exact h_accept k (by omega)
      obtain ⟨ss0, h_run0, h_acc0⟩ := h_ind h_n' h_accept0 (rfl)
      obtain ⟨ss1, h_run1, h_acc1⟩ := h_accept n (by omega)
      intro m h_m ; rw [← h_m]
      use (fun k ↦ if k ≤ φ n then ss0 k else ss1 (k - φ n)) ; constructor
      · constructor
        · have h_init := h_run0.1
          simp [h_init]
        intro k h_k
        rcases (show k < φ n ∨ k = φ n ∨ k > φ n by omega) with h_k' | h_k' | h_k'
        · have h_next := h_run0.2 k h_k'
          simpa [(show k ≤ φ n by omega), (show k + 1 ≤ φ n by omega)]
        · simp [AutomataLoop', h_k', h_acc0] ; right ; use (ss1 0)
          have h_init := h_run1.1
          have h_next := h_run1.2 0 (by omega)
          simp [SuffixFrom] at h_next
          simp [h_init, h_next]
        · have h_next := h_run1.2 (k - φ n) (by omega)
          simp [SuffixFrom, (show k - φ n + φ n = k by omega),
                (show k - φ n + 1 = k + 1 - φ n by omega)] at h_next
          simp [AutomataLoop', h_next,
                (show ¬ k ≤ φ n by omega), (show ¬ k + 1 ≤ φ n by omega)]
      · rcases Classical.em (φ (n + 1) ≤ φ n) with h_φ_n | h_φ_n
        · have h_eq : φ (n + 1) = φ n := by omega
          simpa [h_φ_n, h_eq]
        · simpa [h_φ_n]

end DeprecatedLoop
