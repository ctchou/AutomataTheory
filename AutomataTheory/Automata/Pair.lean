/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Hist
import AutomataTheory.Languages.RegLang

open Function Set Filter

section PairLang

variable {A : Type}

def Automaton.PairPath (M : Automaton A) (s s' : M.State) (al : List A) (ss : ℕ → M.State) :=
  ss 0 = s ∧ ss al.length = s' ∧ ∀ k, (h : k < al.length) → ss (k + 1) ∈ M.next (ss k) (al[k]'h)

def Automaton.PairAccPath (M : Automaton A) (acc : Set M.State) (s s' : M.State) (al : List A) (ss : ℕ → M.State) :=
  M.PairPath s s' al ss ∧ ∃ k < al.length + 1, ss k ∈ acc

def Automaton.PairLang (M : Automaton A) (s s' : M.State) : Set (List A) :=
  { al | ∃ ss, M.PairPath s s' al ss }

def Automaton.PairAccLang (M : Automaton A) (acc : Set M.State) (s s' : M.State) : Set (List A) :=
  { al | ∃ ss, M.PairAccPath acc s s' al ss }

variable {M : Automaton.{0, 0} A} {acc : Set M.State}

def Automaton.SingleInit (s : M.State) : Automaton A where
  State := M.State
  init := {s}
  next := M.next

theorem pair_path_fin_run [Inhabited A] {s s' : M.State} {al : List A} {ss : ℕ → M.State} :
    M.PairPath s s' al ss ↔ FinRun (M.SingleInit s) al.length al.ExtendInf ss ∧ ss al.length = s' := by
  constructor
  · rintro ⟨rfl, rfl, h_next⟩
    simp [FinRun, Automaton.SingleInit, List.ExtendInf]
    intro k h_k ; simp [h_k, h_next]
  · rintro ⟨⟨h_init, h_next⟩, rfl⟩
    simp [Automaton.SingleInit] at h_init h_next
    simp [Automaton.PairPath, h_init]
    intro k h_k ; specialize h_next k h_k
    simp [List.ExtendInf, h_k] at h_next ; exact h_next

variable [h_fin : Finite M.State]

theorem pair_lang_regular [Inhabited A] {s s' : M.State} :
    RegLang (M.PairLang s s') := by
  use (M.SingleInit s), {s'} ; constructor
  · assumption
  ext al ; constructor
  · rintro ⟨ss, h_path⟩
    use al.length, al.ExtendInf
    constructor <;> [skip ; simp [List.ExtendInf]]
    use ss ; exact pair_path_fin_run.mp h_path
  · rintro ⟨n, as, ⟨ss, ⟨h_init, h_next⟩, rfl⟩, rfl⟩
    use ss ; apply pair_path_fin_run.mpr
    simp [FinRun, h_init]
    intro k h_k ; simp [List.ExtendInf, h_k, h_next]

theorem pair_acc_lang_regular [Inhabited A] {s s' : M.State} :
    RegLang (M.PairAccLang acc s s') := by
  let M' := (M.SingleInit s).addHist {False} (fun s a ↦ {s.2 ∨ s.1 ∈ acc})
  use M', {p | p.1 = s' ∧ (p.2 ∨ s' ∈ acc) } ; constructor
  · simp [M', Automaton.SingleInit] ; exact Finite.instProd
  ext al ; constructor
  · rintro ⟨ss, h_path, k0, h_k0, h_k0_acc⟩
    use al.length, al.ExtendInf
    constructor <;> [skip ; simp [List.ExtendInf]]
    obtain ⟨h_run, rfl⟩ := pair_path_fin_run.mp h_path
    have h_ne_init : Set.Nonempty {False} := by simp
    have h_ne_next : ∀ (s : (M.SingleInit s).State × Prop) (a : A), Set.Nonempty {s.2 ∨ s.1 ∈ acc} := by simp
    obtain ⟨hist, h_run'⟩ := automata_hist_fin_run_exists h_ne_init h_ne_next h_run
    use (fun k ↦ (ss k, hist k)) ; simp [M', h_run']
    obtain (rfl | h_k0) := show k0 = al.length ∨ k0 < al.length by omega
    · simp [h_k0_acc]
    suffices h : ∀ k > k0, k < al.length + 1 → hist k by simp [h al.length h_k0]
    intro k h_k
    obtain ⟨j, rfl⟩ := show ∃ j, k = k0 + j + 1 by use (k - k0 - 1) ; omega
    clear h_k ; induction' j with j h_ind
    · have h_next := h_run'.2 k0 h_k0
      simp [Automaton.addHist, h_k0_acc] at h_next
      simp [h_next]
    intro h_j
    specialize h_ind (by omega)
    have h_next := h_run'.2 (k0 + j + 1) (by omega)
    simp [Automaton.addHist, h_ind] at h_next
    simp [h_next, (show k0 + (j + 1) + 1 = k0 + j + 1 + 1 by omega)]
  · rintro ⟨n, as, ⟨ss', h_run', rfl, h_acc⟩, rfl⟩
    have h_run := automata_hist_fin_run_proj h_run'
    use (Prod.fst ∘ ss')
    constructor
    · apply pair_path_fin_run.mpr ; simp
      apply automata_FinRun_modulo (hr := h_run)
      · intro k h_k ; simp [List.ExtendInf, h_k]
      · simp
    simp
    obtain (h_acc | h_acc) := h_acc.symm
    · use n ; simp [h_acc]
    by_contra! h_contra
    suffices h : ∀ k < n + 1, ¬ (ss' k).2 by simp [h n (by omega)] at h_acc
    intro k h_k ; induction' k with k h_ind
    · have h_init := h_run'.1
      simp [M', Automaton.addHist] at h_init
      simp [h_init]
    specialize h_ind (by omega)
    specialize h_contra k (by omega)
    have h_next := h_run'.2 k (by omega)
    simp [M', Automaton.addHist, h_ind, h_contra] at h_next
    simp [h_next]

theorem omega_reg_lang_finite_union_form :
    AcceptedOmegaLang M acc = ⋃ s0 ∈ M.init, ⋃ sa ∈ acc, ConcatOmega (M.PairLang s0 sa) (M.PairLang sa sa) := by
  ext as ; simp ; constructor
  · rintro ⟨ss, ⟨h_init, h_next⟩, h_acc⟩
    obtain ⟨sa, h_sa, h_acc⟩ := frequently_in_finite_set.mp h_acc
    use (ss 0) ; simp [h_init]
    use sa ; simp [h_sa]
    have h_inf := Nat.frequently_atTop_iff_infinite.mp h_acc
    let nth_sa := Nat.nth (fun k ↦ ss k = sa)
    have h_nth_sa : ∀ n, ss (nth_sa n) = sa := by exact Nat.nth_mem_of_infinite h_inf
    have h_mono : StrictMono nth_sa := by exact Nat.nth_strictMono h_inf
    use (List.ofFn (fun k : Fin (nth_sa 0) ↦ as k)), (SuffixFrom (nth_sa 0) as)
    simp [← appendListInf_ofFnPrefix_SuffixFrom] ; constructor
    · use ss ; simp [Automaton.PairPath, h_nth_sa, h_next]
    use (fun n ↦ nth_sa n - nth_sa 0) ; simp [SuffixFrom] ; constructor
    · intro m n h_mn ; simp
      have h_nth_mn := h_mono h_mn
      have h_nth_0m := StrictMono.monotone h_mono (show 0 ≤ m by omega)
      have h_nth_0n := StrictMono.monotone h_mono (show 0 ≤ n by omega)
      omega
    intro n
    use (SuffixFrom (nth_sa n) ss)
    have h_nth_0n := StrictMono.monotone h_mono (show 0 ≤ n by omega)
    have h_nth_nn1 := h_mono (show n < n + 1 by omega)
    have h1 : nth_sa (n + 1) - nth_sa 0 - (nth_sa n - nth_sa 0) = nth_sa (n + 1) - nth_sa n := by omega
    have h2 : nth_sa (n + 1) - nth_sa n + nth_sa n = nth_sa (n + 1) := by omega
    simp [Automaton.PairPath, SuffixFrom, h_nth_sa, h1, h2]
    intro k h_k
    specialize h_next (k + nth_sa n)
    have h3 : k + 1 + nth_sa n = k + nth_sa n + 1 := by omega
    have h4 : k + (nth_sa n - nth_sa 0) + nth_sa 0 = k + nth_sa n := by omega
    simp [h_next, h3, h4]
  · rintro ⟨s0, h_s0, sa, h_sa, al0, as1, ⟨ss0, h_path0⟩, ⟨nth_sa, h_mono, h_sa_0, h_path1⟩, rfl⟩
    choose nth_ss h_nth_ss using h_path1
    let seg k := Segment nth_sa (k - al0.length)
    let ss k := if k < al0.length then ss0 k else nth_ss (seg k) (k - nth_sa (seg k) - al0.length)
    use ss ; constructor
    · constructor
      · rcases (show al0.length > 0 ∨ al0.length = 0 by omega) with h_al0 | h_al0
        · simp [ss, h_al0, h_path0.1, h_s0]
        have h_seg_0 : seg 0 = 0 := by simp [seg, segment_zero h_mono h_sa_0]
        simp [ss, h_al0, h_seg_0, (h_nth_ss 0).1, ← h_path0.2.1, h_path0.1, h_s0]
      intro k ; simp [AppendListInf]
      rcases (show k + 1 < al0.length ∨ k + 1 = al0.length ∨ k ≥ al0.length by omega) with h_k | h_k | h_k
      · have h_k' : k < al0.length := by omega
        have h_next := h_path0.2.2 k h_k'
        simp [ss, h_k, h_k', h_next]
      · have h_k' : k < al0.length := by omega
        have h_next := h_path0.2.2 k h_k'
        simp [h_k, h_path0.2.1] at h_next
        simp [ss, h_k, h_k', seg, segment_zero h_mono h_sa_0, (h_nth_ss 0).1, h_next]
      · have h_k' : ¬ k < al0.length := by omega
        have h_k'' : ¬ k + 1 < al0.length := by omega
        have h_lo := segment_lower_bound h_mono h_sa_0 (k - al0.length)
        have h_hi := segment_upper_bound h_mono h_sa_0 (k - al0.length)
        simp [ss, h_k', h_k'', seg]
        have h_next := (h_nth_ss (Segment nth_sa (k - al0.length))).2.2
          <| (k - nth_sa (Segment nth_sa (k - al0.length)) - al0.length)
        simp at h_next
        specialize h_next (by omega)
        have h1 : k - nth_sa (Segment nth_sa (k - al0.length)) - al0.length + nth_sa (Segment nth_sa (k - al0.length))
          = k - al0.length := by omega
        have h2 : k - nth_sa (Segment nth_sa (k - al0.length)) - al0.length + 1
          = k + 1 - nth_sa (Segment nth_sa (k - al0.length)) - al0.length := by omega
        simp [h1, h2] at h_next
        rcases (show k + 1 - al0.length < nth_sa (Segment nth_sa (k - al0.length) + 1) ∨
                     k + 1 - al0.length = nth_sa (Segment nth_sa (k - al0.length) + 1) by omega) with h_k1 | h_k1
        · have h3 : Segment nth_sa (k + 1 - al0.length) = Segment nth_sa (k - al0.length) := by
            exact segment_range_val h_mono (hu := h_k1) (hl := by omega)
          simp [h3, h_next]
        · have h3 : k + 1 - nth_sa (Segment nth_sa (k - al0.length) + 1) - al0.length = 0 := by omega
          have h4 := (h_nth_ss (Segment nth_sa (k - al0.length) + 1)).1
          simp [h_k1, segment_idem h_mono, h3, h4]
          have h5 := (h_nth_ss (Segment nth_sa (k - al0.length))).2.1
          have h6 : k + 1 - al0.length - nth_sa (Segment nth_sa (k - al0.length))
            = k + 1 - nth_sa (Segment nth_sa (k - al0.length)) - al0.length := by omega
          simp [← h_k1, h6] at h5
          simp [h5] at h_next
          exact h_next
    · let φ k := nth_sa k + al0.length
      have h_φ_mono : StrictMono φ := by
        intro m n h_mn ; simp [φ] ; apply h_mono h_mn
      have h_φ_range : range φ ⊆ {k | ss k ∈ acc} := by
        rintro k ⟨n, rfl⟩
        simp [φ, ss, seg, segment_idem h_mono, (h_nth_ss n).1, h_sa]
      apply Nat.frequently_atTop_iff_infinite.mpr
      apply Infinite.mono h_φ_range
      exact strict_mono_infinite h_φ_mono

end PairLang
