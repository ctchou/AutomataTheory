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

theorem pair_lang_fin_subseq {as : ℕ → A} {ss : ℕ → M.State} {m n : ℕ}
    (h_next : ∀ k, ss (k + 1) ∈ M.next (ss k) (as k)) (h_m_n : m ≤ n) :
    FinSubseq as m n ∈ M.PairLang (ss m) (ss n) := by
  use (fun k ↦ ss (k + m))
  simp [Automaton.PairPath, FinSubseq, (show n - m + m = n by omega)]
  intro k h_k ; grind

theorem pair_path_split {s s' : M.State} {al0 al1 : List A} {ss : ℕ → M.State}
    (h : M.PairPath s s' (al0 ++ al1) ss) :
    M.PairPath s (ss al0.length) al0 ss ∧ M.PairPath (ss al0.length) s' al1 (SuffixFrom al0.length ss) := by
  obtain ⟨rfl, rfl, h_next⟩ := h
  constructor
  · simp [Automaton.PairPath]
    grind
  · simp [Automaton.PairPath, SuffixFrom, Nat.add_comm]
    intro k h_k ; specialize h_next (al0.length + k) (by simpa)
    grind

theorem pair_lang_split {s s' : M.State} {al0 al1 : List A}
    (h : al0 ++ al1 ∈ M.PairLang s s') : ∃ t, al0 ∈ M.PairLang s t ∧ al1 ∈ M.PairLang t s' := by
  obtain ⟨ss, h_path⟩ := h
  have ⟨h_path0, h_path1⟩ := pair_path_split h_path
  use (ss al0.length) ; constructor
  · use ss
  · use (SuffixFrom al0.length ss)

theorem pair_acc_lang_split {s s' : M.State} {al0 al1 : List A}
    (h : al0 ++ al1 ∈ M.PairAccLang acc s s') :
    ∃ t, (al0 ∈ M.PairAccLang acc s t ∧ al1 ∈ M.PairLang t s') ∨
         (al0 ∈ M.PairLang s t ∧ al1 ∈ M.PairAccLang acc t s') := by
  obtain ⟨ss, h_path, n, h_n, h_acc⟩ := h
  obtain ⟨h_path0, h_path1⟩ := pair_path_split h_path
  use (ss al0.length)
  rcases Classical.em (n < al0.length + 1) with h_n' | h_n'
  · left ; constructor
    · use ss ; simp [Automaton.PairAccPath, h_path0] ; use n
    · use (SuffixFrom al0.length ss)
  · right ; constructor
    · use ss
    · use (SuffixFrom al0.length ss) ; simp [Automaton.PairAccPath, h_path1]
      use (n - al0.length) ; simp [SuffixFrom]
      grind

theorem pair_path_concat {s s' t: M.State} {al0 al1 : List A} {ss0 ss1 : ℕ → M.State}
    (h0 : M.PairPath s t al0 ss0) (h1 : M.PairPath t s' al1 ss1) :
    M.PairPath s s' (al0 ++ al1) (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length)) := by
  obtain ⟨rfl, rfl, h_next0⟩ := h0
  obtain ⟨h_s1, rfl, h_next1⟩ := h1
  simp [Automaton.PairPath] ; constructor
  · grind
  intro k h_k
  rcases (show k < al0.length ∨ k = al0.length ∨ k > al0.length by omega) with h_k' | h_k' | h_k'
  · grind
  · simp [h_k', ← h_s1]
    grind
  · specialize h_next1 (k - al0.length) (by omega)
    grind

theorem pair_lang_concat {s s' t: M.State} {al0 al1 : List A}
    (h0 : al0 ∈ M.PairLang s t) (h1 : al1 ∈ M.PairLang t s') : al0 ++ al1 ∈ M.PairLang s s' := by
  obtain ⟨ss0, h_path0⟩ := h0
  obtain ⟨ss1, h_path1⟩ := h1
  use (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length))
  exact pair_path_concat h_path0 h_path1

theorem pair_acc_lang_concat_0 {s s' t: M.State} {al0 al1 : List A}
    (h0 : al0 ∈ M.PairAccLang acc s t) (h1 : al1 ∈ M.PairLang t s') : al0 ++ al1 ∈ M.PairAccLang acc s s' := by
  obtain ⟨ss0, h_path0, n, h_n, h_acc⟩ := h0
  obtain ⟨ss1, h_path1⟩ := h1
  use (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length))
  constructor
  · exact pair_path_concat h_path0 h_path1
  · use n ; grind

theorem pair_acc_lang_concat_1 {s s' t: M.State} {al0 al1 : List A}
    (h0 : al0 ∈ M.PairLang s t) (h1 : al1 ∈ M.PairAccLang acc t s') : al0 ++ al1 ∈ M.PairAccLang acc s s' := by
  obtain ⟨ss0, h_path0⟩ := h0
  obtain ⟨ss1, h_path1, n, h_n, h_acc⟩ := h1
  use (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length))
  constructor
  · exact pair_path_concat h_path0 h_path1
  · use (n + al0.length)
    simp [(show n + al0.length < al0.length + al1.length + 1 by omega)]
    rcases (show n > 0 ∨ n = 0 by omega) with h_n' | rfl
    · grind
    · obtain ⟨rfl⟩ := h_path1.1
      simp [h_path0.2.1, h_acc]

def Automaton.SingleInit (s : M.State) : Automaton A where
  State := M.State
  init := {s}
  next := M.next

theorem pair_path_fin_run [Inhabited A] {s s' : M.State} {al : List A} {ss : ℕ → M.State} :
    M.PairPath s s' al ss ↔ (M.SingleInit s).FinRun al.length al.ExtendInf ss ∧ ss al.length = s' := by
  constructor
  · rintro ⟨rfl, rfl, h_next⟩
    simp [Automaton.FinRun, Automaton.SingleInit, List.ExtendInf]
    intro k h_k ; simp [h_k, h_next]
  · rintro ⟨⟨h_init, h_next⟩, rfl⟩
    simp [Automaton.SingleInit] at h_init h_next
    simp [Automaton.PairPath, h_init]
    intro k h_k ; specialize h_next k h_k
    simp [List.ExtendInf, h_k] at h_next ; exact h_next

theorem pair_acc_lang_frequently_from_run {as : ℕ → A} {ss : ℕ → M.State} {φ : ℕ → ℕ}
    (h_next : ∀ k, ss (k + 1) ∈ M.next (ss k) (as k)) (h_acc : ∃ᶠ k in Filter.atTop, ss k ∈ acc) (h_mono : StrictMono φ) :
    ∃ᶠ m in Filter.atTop, FinSubseq as (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss (φ m)) (ss (φ (m + 1))) := by
  have h_acc' := frequently_atTop.mp h_acc
  have h_mono' := frequently_atTop.mp <| Nat.frequently_atTop_iff_infinite.mpr <| strict_mono_infinite h_mono
  apply frequently_atTop.mpr ; intro m
  obtain ⟨k, h_k, h_k_acc⟩ := h_acc' (φ m)
  let n := Segment' φ k
  use n ; constructor
  · exact segment'_lower_val h_mono h_k
  · use (fun k ↦ ss (k + φ n)) ; constructor
    · have : φ n < φ (n + 1) := h_mono (show n < n + 1 by omega)
      simp [Automaton.PairPath, FinSubseq, (show φ (n + 1) - φ n + φ n = φ (n + 1) by omega)]
      intro j h_j
      have := h_next (j + φ n)
      simpa [(show j + 1 + φ n = j + φ n + 1 by omega)]
    · have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le h_mono]
      have h1 : φ 0 ≤ k := by omega
      have : φ n ≤ k := by exact segment'_lower_bound h_mono h1
      use (k - φ n)
      simp [(show k - φ n + φ n = k by omega), h_k_acc, FinSubseq]
      have : k < φ (n + 1) := by exact segment'_upper_bound h_mono h1
      omega

theorem pair_acc_lang_frequently_to_run {φ : ℕ → ℕ} {as : ℕ → A} (ss' : ℕ → M.State)
    (h_mono : StrictMono φ) (h_zero : φ 0 = 0)
    (h_pair : ∀ m, FinSubseq as (φ m) (φ (m + 1)) ∈ M.PairLang (ss' m) (ss' (m + 1)))
    (h_inf : ∃ᶠ m in atTop, FinSubseq as (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss' m) (ss' (m + 1))) :
    ∃ ss : ℕ → M.State, (∀ m, ss (φ m) = ss' m) ∧
      (∀ k, ss (k + 1) ∈ M.next (ss k) (as (k))) ∧ (∃ᶠ k in atTop, ss k ∈ acc) := by
  have h_exists : ∀ m, ∃ ps, M.PairPath (ss' m) (ss' (m + 1)) (FinSubseq as (φ m) (φ (m + 1))) ps ∧
    ( FinSubseq as (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss' m) (ss' (m + 1)) →
      M.PairAccPath acc (ss' m) (ss' (m + 1)) (FinSubseq as (φ m) (φ (m + 1))) ps ) := by
    intro m
    rcases Classical.em (FinSubseq as (φ m) (φ (m + 1)) ∈ M.PairAccLang acc (ss' m) (ss' (m + 1))) with h_acc | h_acc
    <;> simp [h_acc]
    · obtain ⟨ps, h_ps⟩ := h_acc
      use ps ; simp [h_ps, h_ps.1]
    · obtain ⟨ps, h_ps⟩ := h_pair m
      use ps
  choose ps h_ps using h_exists
  use (fun k ↦ ps (Segment φ k) (k - φ (Segment φ k)))
  constructorm* _ ∧ _
  · intro m
    have h0 := (h_ps (Segment φ (φ m))).1.1
    simp [segment_idem h_mono] at h0
    simp [segment_idem h_mono, h0]
  · intro k
    have := segment_lower_bound h_mono h_zero k
    have := segment_upper_bound h_mono h_zero k
    have h_next := (h_ps (Segment φ k)).1.2.2 (k - φ (Segment φ k))
    simp [FinSubseq,
      (show k - φ (Segment φ k) + φ (Segment φ k) = k by omega),
      (show k - φ (Segment φ k) + 1 = k + 1 - φ (Segment φ k) by omega),
      (show k - φ (Segment φ k) < φ (Segment φ k + 1) - φ (Segment φ k) by omega)] at h_next
    rcases (show k + 1 < φ (Segment φ k + 1) ∨ k + 1 = φ (Segment φ k + 1) by omega) with h_k | h_k
    · have h1 := segment_range_val h_mono (by omega) h_k
      simp [h1, h_next]
    · have h1 := (h_ps (Segment φ k)).1.2.1
      simp [FinSubseq] at h1
      simp [h_k, h1] at h_next
      have h2 : Segment φ (k + 1) = Segment φ k + 1 := by simp [h_k, segment_idem h_mono]
      have h3 := (h_ps (Segment φ k + 1)).1.1
      simp [← h_k, h2, h3, h_next]
  · have h_inf' : ∃ᶠ m in atTop, ∃ k < φ (m + 1) - φ m + 1, ps m k ∈ acc := by
      apply Frequently.mono h_inf
      intro m h_m
      obtain ⟨_, k, h_k, h_acc⟩ := (h_ps m).2 h_m
      simp [FinSubseq] at h_k
      use k
    have h_φ_inf := Filter.frequently_atTop'.mp <| Nat.frequently_atTop_iff_infinite.mpr <| strict_mono_infinite h_mono
    apply Filter.frequently_atTop'.mpr
    intro k0
    obtain ⟨k1, h_k1, m1, rfl⟩ := h_φ_inf k0
    obtain ⟨m2, h_m2, k2, h_k2, h_acc⟩ := Filter.frequently_atTop'.mp h_inf' m1
    have := h_mono h_m2
    have : φ m2 < φ (m2 + 1) := by apply h_mono ; omega
    rcases (show k2 < φ (m2 + 1) - φ m2 ∨ k2 = φ (m2 + 1) - φ m2 by omega) with h_k2' | rfl
    · use (k2 + φ m2) ; constructor
      · omega
      have h1 := segment_range_val h_mono (show φ m2 ≤ k2 + φ m2 by omega) (by omega)
      simp [h1, h_acc]
    · use (φ (m2 + 1)) ; constructor
      · omega
      have h2 := (h_ps (m2)).1.2.1
      simp [FinSubseq] at h2
      simp [h2] at h_acc
      simp [segment_idem h_mono, (h_ps (m2 + 1)).1.1, h_acc]

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
    simp [Automaton.FinRun, h_init]
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
    M.AcceptedOmegaLang acc = ⋃ s0 ∈ M.init, ⋃ sa ∈ acc, (M.PairLang s0 sa) * (M.PairLang sa sa)^ω := by
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
    use (fun n ↦ nth_sa n - nth_sa 0) ; simp [FinSubseq, SuffixFrom] ; constructor
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
      intro k ; simp [instAppendListInf, AppendListInf]
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
        simp [FinSubseq] at h_next
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
          simp [FinSubseq, ← h_k1, h6] at h5
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
