/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Languages.Basic
import AutomataTheory.Sequences.Segments
import AutomataTheory.Automata.Basic

/-!
The loop construction of an automaton is used to prove that the
regular language is closed under the Kleene star and the ω-power
of a regular language is an ω-regular language.
-/

open Function Set Sum Filter
open Classical

section AutomataLoop

variable {A : Type*}

def Automaton.Loop (M : Automaton A) (acc : Set M.State) : Automaton A where
  State := Unit ⊕ M.State
  init := {inl ()}
  next := fun s a ↦ match (s) with
    | inl () => inr '' { s' | ∃ s0 ∈ M.init, s' ∈ M.next s0 a } ∪
                if ∃ s0 ∈ M.init, ∃ s' ∈ acc, s' ∈ M.next s0 a then {inl ()} else ∅
    | inr s  => inr '' (M.next s a) ∪
                if ∃ s' ∈ acc, s' ∈ M.next s a then {inl ()} else ∅

variable {M : Automaton A} {acc : Set M.State}

private lemma not_inl_unit {s : (M.Loop acc).State} :
    s ≠ inl () ↔ ∃ s' : M.State, s = inr s' := by
  constructor
  · rw [← isRight_iff, ← not_isLeft, isLeft_iff]
    rintro h1 ⟨u, h_s⟩
    have h_u := Unit.ext u ()
    simp [h_s] at h1
  · rintro ⟨s', h_s'⟩ ; simp [h_s']

theorem automata_loop_fin_run {n : ℕ} {as : ℕ → A} {ss : ℕ → (M.Loop acc).State} (h : n > 0) :
    FinRun (M.Loop acc) n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k ∈ range inr) ↔
    ∃ ss', FinRun M n as ss' ∧ ss' n ∈ acc ∧ ss 0 = inl () ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by
  constructor
  · rintro ⟨⟨h_init, h_next⟩, h_inl_n, h_inr⟩
    simp [Automaton.Loop] at h_init
    rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
    · obtain ⟨rfl⟩ := h_n
      specialize h_next 0 (by omega)
      simp [h_init, h_inl_n, Automaton.Loop] at h_next
      obtain ⟨s0, h_s0, s1, h_acc, h_next⟩ := h_next
      use (fun k ↦ if k = 0 then s0 else if k = 1 then s1 else s0)
      simp [h_init, h_acc, h_inl_n, FinRun, h_s0, h_next]
    · obtain ⟨s1, h_s1⟩ := h_inr 1 h_n (by omega)
      have h_next_0 := h_next 0 h
      simp [h_init, ← h_s1, Automaton.Loop] at h_next_0
      obtain ⟨s0, h_s0, h_next_0⟩ := h_next_0
      obtain ⟨sn1, h_sn1⟩ := h_inr (n - 1) (by omega) (by omega)
      have h_next_n1 := h_next (n - 1) (by omega)
      have h_n1 : n - 1 + 1 = n := by omega
      simp [h_n1, h_inl_n, ← h_sn1, Automaton.Loop] at h_next_n1
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
          simp [h_ss_k, h_ss_k1, Automaton.Loop] at h_next_k
          simp [(show k + 1 < n by omega), (show k ≠ 0 by omega), h_k_n, h_next_k]
      · intro k h_k_n h_k_0
        simp [h_k_n, h_k_0, (show k ≠ 0 by omega), h_ss']
  · rintro ⟨ss', ⟨h_init, h_next⟩, h_acc, h_inl_0, h_inl_n, h_inr⟩
    constructor <;> [constructor ; constructor]
    · simp [h_inl_0, Automaton.Loop]
    · intro k h_k_n
      rcases (show k = 0 ∨ k > 0 by omega) with h_k_0 | h_k_0
      · specialize h_next 0 h
        rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
        · obtain ⟨rfl⟩ := h_n
          simp [h_k_0, h_inl_0, Automaton.Loop, h_inl_n]
          use (ss' 0) ; simp [h_init] ; use (ss' 1)
        · specialize h_inr 1 h_n (by omega)
          simp [h_k_0, h_inl_0, Automaton.Loop, h_inr]
          use (ss' 0)
      · specialize h_next k (h_k_n)
        have h_ss_k := h_inr k h_k_n h_k_0
        rcases (show k + 1 < n ∨ k = n - 1 by omega) with h_k_n' | h_k_n'
        · have h_ss_k' := h_inr (k + 1) h_k_n' (by omega)
          simpa [h_ss_k, h_ss_k', Automaton.Loop]
        · obtain ⟨rfl⟩ := h_k_n'
          have h_n1 : n - 1 + 1 = n := by omega
          simp [h_n1] at h_next
          simp [h_n1, h_ss_k, h_inl_n, Automaton.Loop]
          use (ss' n)
    · exact h_inl_n
    · intro k h_k_n h_k_0
      simp [h_inr k h_k_n h_k_0]

theorem automata_loop_fin_run_exists {n : ℕ} {as : ℕ → A} {ss' : ℕ → M.State}
    (h_run' : FinRun M n as ss') (h_acc' : ss' n ∈ acc) :
    ∃ ss, FinRun (M.Loop acc) n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by
  rcases (show n = 0 ∨ n > 0 by omega) with ⟨rfl⟩ | h_n
  · use (fun k ↦ inl ()) ; simp [FinRun, Automaton.Loop]
  let ss k := if k = 0 ∨ k = n then inl () else inr (ss' k)
  suffices h : ∃ ss', FinRun M n as ss' ∧ ss' n ∈ acc ∧ ss 0 = inl () ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) by
    obtain ⟨h_run, h_ss_n, _⟩ := (automata_loop_fin_run h_n).mpr h
    use ss ; simp [h_run, h_ss_n]
    intro k h_k_n h_k_0 ; simp [ss] ; omega
  use ss' ; simp [h_run', h_acc', ss] ; omega

end AutomataLoop

section AcceptedLangLoop

variable {A : Type*} {M : Automaton A} {acc : Set M.State}

theorem accepted_lang_loop_concat :
    ConcatFin (AcceptedLang (M.Loop acc) {inl ()}) (AcceptedLang (M.Loop acc) {inl ()}) ⊆
    AcceptedLang (M.Loop acc) {inl ()} := by
  rintro al ⟨al1, al2, ⟨n1, as1, ⟨ss1, h_run1, h_acc1⟩, h_al1⟩, ⟨n2, as2, ⟨ss2, h_run2, h_acc2⟩, h_al2⟩, rfl⟩
  let as k := if k < n1 then as1 k else as2 (k - n1)
  use (n1 + n2), as ; symm ; constructor
  · simp [ofFn_of_append_ofFn_oFn (xs := as) (show n1 ≤ n1 + n2 by omega), as, h_al1, h_al2]
  let ss k := if k < n1 then ss1 k else ss2 (k - n1)
  use ss ; symm ; constructor
  · simp at h_acc2 ; simp [ss, h_acc2]
  constructor
  · suffices h_0 : ss 0 = inl () by simp [h_0, Automaton.Loop]
    rcases (show n1 = 0 ∨ n1 > 0 by omega) with h_n1 | h_n1 <;> simp [ss, h_n1]
    · exact h_run2.1
    · exact h_run1.1
  intro k h_k
  rcases (show k + 1 < n1 ∨ k + 1 = n1 ∨ k + 1 > n1 by omega) with h_k | h_k | h_k
  · have h_next := h_run1.2 k (by omega)
    simp [as, ss, h_next, h_k, (show k < n1 by omega)]
  · have h_next := h_run1.2 k (by omega)
    suffices h_n1 : ss2 0 = ss1 (k + 1) by simp [as, ss, h_next, h_n1, ← h_k]
    simp [← h_k] at h_acc1
    simp [h_acc1] ; exact h_run2.1
  · have h_next := h_run2.2 (k - n1) (by omega)
    simp [as, ss, h_next, (show ¬ k < n1 by omega), (show ¬ k + 1 < n1 by omega), (show k + 1 - n1 = k - n1 + 1 by omega)]

theorem accepted_lang_loop [Inhabited A] :
    AcceptedLang (M.Loop acc) {inl ()} = IterStar (AcceptedLang M acc) := by
  ext al ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ ; simp [IterStar]
    revert al
    induction' n using Nat.strong_induction_on with n h_ind
    intro al h_al
    let loop k := 0 < k ∧ k < n ∧ ss k = inl ()
    rcases Classical.em (∃ k, loop k) with h_loop | h_loop
    · let m := Nat.findGreatest loop n
      have h_m : loop m := by
        obtain ⟨k, h_loop⟩ := h_loop
        apply Nat.findGreatest_spec (m := k) (by omega) h_loop
      obtain ⟨h_m_0, h_m_n, h_m_inl⟩ := h_m
      let al' := List.ofFn (fun k : Fin m ↦ as k)
      have h_run' := automata_FinRun_imp_FinRun h_m_n h_run
      obtain ⟨j, h_j⟩ := h_ind m h_m_n h_run' (by simp [h_m_inl]) (al') (by simp [al'])
      have h_d : n - m > 0 := by omega
      have h_run'' : FinRun (M.Loop acc) (n - m) (SuffixFrom m as) (SuffixFrom m ss) := by
        constructor
        · simp [Automaton.Loop, SuffixFrom, h_m_inl]
        intro k h_k
        have h_next := h_run.2 (k + m) (by omega)
        simp [SuffixFrom, (show k + 1 + m = k + m + 1 by omega), h_next]
      have h_inl'' : SuffixFrom m ss (n - m) = inl () := by
        simp at h_acc
        simp [SuffixFrom, (show n - m + m = n by omega), h_acc]
      have h_inr'' : ∀ k < n - m, k > 0 → SuffixFrom m ss k ∈ range inr := by
        intro k h_k_d h_k_0
        have h_not_loop : ¬ loop (k + m) := by
          exact Nat.findGreatest_is_greatest (show m < k + m by omega) (by omega)
        simp [loop, -add_pos_iff] at h_not_loop
        obtain ⟨s', h_s'⟩ := not_inl_unit.mp <| h_not_loop (by omega) (by omega)
        simp [SuffixFrom] ; use s' ; simp [h_s']
      obtain ⟨ss'', h_run'', h_acc'', _⟩ := (automata_loop_fin_run h_d).mp ⟨h_run'', h_inl'', h_inr''⟩
      let al'' := List.ofFn (fun k : Fin (n - m) ↦ as (k + m))
      use (j + 1) ; simp [IterFin]
      use al', al'' ; constructorm* _ ∧ _
      · exact h_j
      · use (n - m), (SuffixFrom m as) ; simp [al'', SuffixFrom] ; use ss''
      · simp [h_al, al', al'', ofFn_of_append_ofFn_oFn (show m ≤ n by omega)]
    · rcases (show n = 0 ∨ n > 0 by omega) with h_n | h_n
      · obtain ⟨rfl⟩ := h_n ; simp at h_al
        use 0 ; simp [h_al, IterFin]
      simp [loop] at h_loop
      have h_inr : ∀ k < n, k > 0 → ss k ∈ range inr := by
        intro k h_k_n h_k_0
        obtain ⟨s', h_s'⟩ := not_inl_unit.mp <| h_loop k h_k_0 h_k_n
        use s' ; simp [h_s']
      simp at h_acc
      obtain ⟨ss', h_run', h_acc', _⟩ := (automata_loop_fin_run h_n).mp ⟨h_run, h_acc, h_inr⟩
      use 1 ; simp [IterFin, lang_ConcatFin_epsilon_left]
      use n, as ; simp [h_al]
      use ss'
  · rintro ⟨L, ⟨i, rfl⟩, h_al⟩ ; simp at h_al
    revert al
    induction' i with i h_ind
    · intro al ; simp [IterFin] ; rintro ⟨rfl⟩
      use 0 ; simp
      use (fun k ↦ default), (fun k ↦ inl ()) ; simp [FinRun, Automaton.Loop]
    rintro al ⟨al1, al2, h_al1, h_al2, h_al⟩
    specialize h_ind al1 h_al1
    suffices _ : al2 ∈ AcceptedLang (M.Loop acc) {inl ()} by
      apply accepted_lang_loop_concat ; use al1, al2
    obtain ⟨n2, as2, ⟨ss2', h_run2, h_acc2⟩, h_al2⟩ := h_al2
    obtain ⟨ss2, h_run2, h_acc2, _⟩ := automata_loop_fin_run_exists h_run2 h_acc2
    use n2, as2 ; simp [h_al2]
    use ss2 ; simp [h_run2, h_acc2]

theorem accepted_omega_lang_loop :
    AcceptedOmegaLang (M.Loop acc) {inl ()} = IterOmega (AcceptedLang M acc) := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_acc⟩ ; simp at h_acc
    let φ m := Nat.nth (fun k ↦ ss k = inl ()) m
    have h_inf : {k | ss k = inl ()}.Infinite := by simpa [← Nat.frequently_atTop_iff_infinite]
    have h_mono : StrictMono φ := by exact Nat.nth_strictMono h_inf
    use φ ; simp [h_mono] ; constructor
    · have h_init := h_run.1
      simp [Automaton.Loop] at h_init
      apply Nat.nth_zero_of_zero h_init
    · intro m
      use (φ (m + 1) - φ m), (SuffixFrom (φ m) as) ; constructor
      · have h_mono_m : φ (m + 1) - φ m > 0 := by have := h_mono (show m < m + 1 by omega) ; omega
        let ss1 := SuffixFrom (φ m) ss
        have h_run1 : FinRun (M.Loop acc) (φ (m + 1) - φ m) (SuffixFrom (φ m) as) ss1 := by
          constructor
          · simp [ss1, SuffixFrom, Automaton.Loop]
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
        obtain ⟨ss', h_run', h_acc', _⟩ := (automata_loop_fin_run h_mono_m).mp ⟨h_run1, h_inl, h_inr⟩
        use ss'
      · rw [FinSubseq, List.ofFn_inj] ; ext k
        simp [SuffixFrom]
  · rintro ⟨φ, h_mono, h_0, h_acc⟩
    choose len as' h_acc h_as' using h_acc
    choose ss' h_run h_acc using h_acc
    let seg k := Segment φ k
    let ss k := if k ∈ range φ then inl () else inr (ss' (seg k) (k - φ (seg k)))
    use ss ; constructor <;> [constructor ; skip]
    · have h_0' : ∃ k, φ k = 0 := by use 0
      simp [ss, h_0', Automaton.Loop]
    · intro k
      have h_seg_k : φ (seg k) ≤ k := by exact segment_lower_bound h_mono h_0 k
      have h_seg_k1 : k < φ (seg k + 1) := by exact segment_upper_bound h_mono h_0 k
      have h_mono_k : φ (seg k + 1) - φ (seg k) > 0 := by omega
      suffices h_lhs :
          FinRun (M.Loop acc) (φ (seg k + 1) - φ (seg k)) (SuffixFrom (φ (seg k)) as) (SuffixFrom (φ (seg k)) ss) ∧
          (SuffixFrom (φ (seg k)) ss) (φ (seg k + 1) - φ (seg k)) = inl () ∧
          (∀ j < φ (seg k + 1) - φ (seg k), j > 0 → (SuffixFrom (φ (seg k)) ss) j ∈ range inr) by
        have h_run_k := h_lhs.1.2 (k - φ (seg k)) (show k - φ (seg k) < φ (seg k + 1) - φ (seg k) by omega)
        simp [SuffixFrom, (show k - φ (seg k) + φ (seg k) = k by omega), (show k - φ (seg k) + 1 + φ (seg k) = k + 1 by omega)] at h_run_k
        exact h_run_k
      apply (automata_loop_fin_run h_mono_k).mpr
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

end AcceptedLangLoop
