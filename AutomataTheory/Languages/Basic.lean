/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences.Segments

/-!
This file contains some basic definitions and theorems about
languages (i.e., subsets of `List A`) and ω-languages (i.e., subsets of `ℕ → A`),
where `A` is the type of "alphabet".
-/

open Function Finset Set List Filter
open scoped Computability

section Languages

variable {A : Type}

/-- Concatenation of two languages, resulting in a language.
-/
def ConcatFin (L0 L1 : Set (List A)) : Set (List A) :=
  { al | ∃ al0 al1, al0 ∈ L0 ∧ al1 ∈ L1 ∧ al0 ++ al1 = al }

/-- Use the infix notation `*` for `ConcatFin`.
-/
instance : Mul (Set (List A)) :=
  { mul := ConcatFin }

/-- Concatenation of a language and an ω-language, resulting in an ω-language.
-/
def ConcatInf (L0 : Set (List A)) (L1 : Set (ℕ → A)) : Set (ℕ → A) :=
  { as | ∃ al0 as1, al0 ∈ L0 ∧ as1 ∈ L1 ∧ as = al0 ++ as1 }

/-- Use the infix notation `*` for `ConcatInf`.
-/
instance : HMul (Set (List A)) (Set (ℕ → A)) (Set (ℕ → A)) :=
  { hMul := ConcatInf }

/-- Concatenation of `n` copies of a languages, resulting in a language.
-/
def IterFin (L : Set (List A)) : ℕ → Set (List A)
  | 0 => {[]}
  | n + 1 => (IterFin L n) * L

/-- Use the infix notation `^` for `IterFin`.
-/
instance instIterFin : HPow (Set (List A)) (ℕ) (Set (List A)) :=
  { hPow := IterFin }

/-- Concatenation of any finitely many copies of a languages, resulting in a language.
A.k.a. Kleene star.
-/
def IterStar (L : Set (List A)) : Set (List A) :=
  ⋃ n : ℕ, L ^ n

/-- Use the postfix notation `∗` for `IterStar`.
-/
instance instIterStar : KStar (Set (List A)) :=
  { kstar := IterStar }

/-- Concatenation of countably infinitely many copies of a languages, resulting in an ω-language.
A.k.a. ω-power.
-/
def IterOmega (L : Set (List A)) : Set (ℕ → A) :=
  { as | ∃ φ : ℕ → ℕ, StrictMono φ ∧ φ 0 = 0 ∧ ∀ m, as ⇊ (φ m) (φ (m + 1)) ∈ L }

/-- Use the postfix notation ^ω` for `IterOmega`.
-/
@[notation_class]
class OmegaPower (α : Type) (β : outParam (Type)) where
  omegaPower : α → β

postfix:1024 "^ω" => OmegaPower.omegaPower

instance instIterOmega : OmegaPower (Set (List A)) (Set (ℕ → A)) :=
  { omegaPower := IterOmega }

/- The ω-limit of a language L is the ω-language of infinite sequences each of which
contains infinitely many prefixes in L.
-/
def OmegaLimit (L : Set (List A)) : Set (ℕ → A) :=
  { as | ∃ᶠ m in atTop, as ⇊ 0 m ∈ L }

/-- Use the postfix notation ↗ω` for `OmegaLimit`.
-/
@[notation_class]
class OmegaLimitCls (α : Type) (β : outParam (Type)) where
  omegaLimit : α → β

postfix:1024 "↗ω" => OmegaLimitCls.omegaLimit

instance instOmegaLimit : OmegaLimitCls (Set (List A)) (Set (ℕ → A)) :=
  { omegaLimit := OmegaLimit }

/- The following are some miscellaneous theorems -/

theorem epsilon_ConcatFin {L : Set (List A)} :
    {[]} * L = L := by
  ext al ; constructor
  · rintro ⟨al1, al2, h_al1, h_al2, h_al⟩
    simp at h_al1 ; simp [h_al1] at h_al ; simpa [← h_al]
  · intro h_al ; use [], al ; simp [h_al]

theorem ConcatFin_epsilon {L : Set (List A)} :
    L * {[]} = L := by
  ext al ; constructor
  · rintro ⟨al1, al2, h_al1, h_al2, h_al⟩
    simp at h_al2 ; simp [h_al2] at h_al ; simpa [← h_al]
  · intro h_al ; use al, [] ; simp [h_al]

theorem ConcatFin_union_distrib {L0 L1 L2 : Set (List A)} :
    L0 * (L1 ∪ L2) = L0 * L1 ∪ L0 * L2 := by
  ext al ; constructor
  · rintro ⟨al0, alu, h_al0, (h_al1 | h_al2), h_al⟩
    · left ; use al0, alu
    · right ; use al0, alu
  · rintro (⟨al0, al1, h_al0, h_al1, h_al⟩ | ⟨al0, al2, h_al0, h_al2, h_al⟩)
    · use al0, al1 ; tauto
    · use al0, al2 ; tauto

theorem empty_ConcatInf {L : Set (ℕ → A)} :
    (∅ : Set (List A)) * L = ∅ := by
  ext as ; simp
  rintro ⟨al, as, h_al, _⟩
  simp at h_al

theorem epsilon_ConcatInf {L : Set (ℕ → A)} :
    ({[]} : Set (List A)) * L = L := by
  ext as ; constructor
  · rintro ⟨al, as, h_al, h_as, rfl⟩ ; simp at h_al
    simp [h_al, h_as, nil_AppendListInf]
  · intro h_as ; use [], as ; simp [h_as, nil_AppendListInf]

theorem ConcatInf_assoc {L0 L0' : Set (List A)} {L1 : Set (ℕ → A)} :
    (L0 * L0') * L1 = L0 * (L0' * L1) := by
  ext as ; constructor
  · rintro ⟨al, as1, ⟨al0, al0', h_al0, h_al0', rfl⟩, h_as1, rfl⟩
    use al0, (al0' ++ as1) ; simp [h_al0, AppendListInf_assoc] ; use al0', as1
  · rintro ⟨al0, as', h_al0, ⟨al0', as1, h_al0', h_as1, rfl⟩, rfl⟩
    rw [← AppendListInf_assoc]
    use (al0 ++ al0'), as1 ; simp [h_as1] ; use al0, al0'

theorem ConcatInf_mono {L0 L0' : Set (List A)} {L1 L1' : Set (ℕ → A)}
    (h0 : L0 ⊆ L0') (h1 : L1 ⊆ L1') :
    L0 * L1 ⊆ L0' * L1' := by
  rintro as ⟨al0, as0, h_al0, h_as0, rfl⟩
  use al0, as0 ; grind

theorem subset_IterStar_IterFin (L : Set (List A)) (n : ℕ) :
    L ^ n ⊆ L∗ := by
  apply subset_iUnion

theorem subset_IterStar_epsilon (L : Set (List A)) :
    {[]} ⊆ L∗ := by
  exact subset_IterStar_IterFin L 0

theorem subset_IterStar_self (L : Set (List A)) :
    L ⊆ L∗ := by
  have := subset_IterStar_IterFin L 1
  simp [instIterFin, IterFin, epsilon_ConcatFin] at this
  exact this

theorem IterFin_seg_exists {L : Set (List A)} {m : ℕ} {al : List A} (h : al ∈ L ^ m) :
    ∃ n ≤ m, ∃ φ : ℕ → ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
      ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L := by
  induction' m with m h_ind generalizing al <;> simp [instIterFin, IterFin] at h
  · use 0 ; simp ; use (fun _ ↦ 0) ; simp [h]
  obtain ⟨al0, al1, h_al0, h_al1, rfl⟩ := h
  obtain ⟨n, h_n, φ, h_mono, h_init, h_last, h_seg⟩ := h_ind h_al0
  rcases Classical.em (al1 = []) with ⟨rfl⟩ | h_al1'
  . use n ; simp [show n ≤ m + 1 by omega] ; use φ
  have := ne_nil_iff_length_pos.mp h_al1'
  use (n + 1) ; simp [(show n + 1 ≤ m + 1 by omega), -extract_eq_drop_take]
  use (fun k ↦ if k < n + 1 then φ k else al0.length + al1.length)
  simp [h_init, -extract_eq_drop_take] ; constructor
  · intro i h_i j h_j h_ij ; simp at h_i h_j
    rcases (show (i < n + 1 ∧ j < n + 1) ∨ (i < n + 1 ∧ j = n + 1) by omega)
      with ⟨h_i', h_j'⟩ | ⟨h_i', h_j'⟩ <;> simp [h_i', h_j']
    · exact h_mono h_i' h_j' h_ij
    · have := StrictMonoOn.monotoneOn h_mono h_i' (show n < n + 1 by omega) (show i ≤ n by omega)
      omega
  · intro k h_k ; rcases (show k < n ∨ n = k by omega) with h_k' | ⟨rfl⟩
    · suffices h1 : (al0 ++ al1).extract (φ k) (φ (k + 1)) = al0.extract (φ k) (φ (k + 1)) by
        simp [h_k, h_k', h1, h_seg, -extract_eq_drop_take]
      have := h_mono h_k (show k + 1 < n + 1 by omega) (by omega)
      have h1 : φ k + (φ (k + 1) - φ k) = φ (k + 1) := by omega
      have h2 : φ (k + 1) ≤ al0.length := by
        have := StrictMonoOn.monotoneOn h_mono (show k + 1 < n + 1 by omega) (show n < n + 1 by omega) (by omega)
        simpa [← h_last]
      simp only [take_drop, h1, take_append_of_le_length h2]
    · simp [h_last, h_al1]

theorem IterStar_seg_exists {L : Set (List A)} {al : List A} (h : al ∈ L∗) :
    ∃ n, ∃ φ : ℕ → ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
      ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L := by
  simp [instIterStar, IterStar, instIterFin] at h
  obtain ⟨m, h_m⟩ := h
  obtain ⟨n, h_n, h_ex⟩ := IterFin_seg_exists h_m
  use n

theorem mem_ConcatInf_IterOmega {L0 L1 : Set (List A)} {as : ℕ → A}
    (h : as ∈ L0 * L1^ω) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      as ⇊ 0 (φ 0) ∈ L0 ∧ ∀ m, as ⇊ (φ m) (φ (m + 1)) ∈ L1 := by
  obtain ⟨al0, as1, h_al0, ⟨φ1, h_mono, h_φ1_0, h_φ1_sub⟩, rfl⟩ := h
  use (fun m ↦ φ1 (m) + al0.length)
  constructorm* _ ∧ _
  · intro m n h_mn ; have := h_mono h_mn ; grind
  · simp [instFinSubseq, FinSubseq, instAppendListInf, AppendListInf, h_φ1_0, h_al0]
  · intro m
    have h1 : φ1 (m + 1) + al0.length - (φ1 m + al0.length) = φ1 (m + 1) - φ1 m := by omega
    specialize h_φ1_sub m
    simpa [instFinSubseq, FinSubseq, ← Nat.add_assoc, appendListInf_elt_skip_list, h1]

theorem ConcatInf_self_IterOmega {L : Set (List A)} :
    L * L^ω = L^ω := by
  ext as ; constructor
  · intro h
    obtain ⟨φ, h_mono, h_init, h_rest⟩ := mem_ConcatInf_IterOmega h
    rcases (show φ 0 = 0 ∨ φ 0 > 0 by omega) with h_φ | h_φ
    · use φ
    use (fun k ↦ if k = 0 then 0 else φ (k - 1)) ; simp ; constructor
    · apply strictMono_nat_of_lt_succ ; intro n
      rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n, h_φ]
      exact h_mono (show n - 1 < n by omega)
    · intro n
      rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n, h_init]
      specialize h_rest (n - 1) ; simp_all [(show n - 1 + 1 = n by omega)]
  · rintro ⟨φ, h_mono, h_init, h_rest⟩
    use (as ⇊ (φ 0) (φ 1)), (as <<< (φ 1))
    simp [h_rest] ; constructor
    · use (fun k ↦ φ (k + 1) - φ 1) ; constructor
      · intro m n h_mn ; simp
        have := h_mono (show m + 1 < n + 1 by omega)
        have := StrictMono.monotone h_mono (show 1 ≤ m + 1 by omega)
        omega
      · simp ; intro n
        have h1 := StrictMono.monotone h_mono (show 1 ≤ n + 1 by omega)
        simp [finSubseq_of_SuffixFrom h1, h_rest]
    · ext k
      rcases (show k < φ 1 - φ 0 ∨ ¬ k < φ 1 - φ 0 by omega) with h_k | h_k <;>
        simp [h_k, instAppendListInf, AppendListInf, instSuffixFrom, SuffixFrom, instFinSubseq, FinSubseq] <;>
        simp [h_init]
      simp [show k - φ 1 + φ 1 = k by omega]

theorem ConcatInf_IterStar_IterOmega {L : Set (List A)} :
    L∗ * L^ω = L^ω := by
  ext as ; constructor
  · rintro ⟨al0, as1, h_al0, h_as1, rfl⟩
    simp [instIterStar, IterStar, instIterFin] at h_al0
    obtain ⟨n, h_al0⟩ := h_al0
    induction' n with n h_ind generalizing al0 as1 <;> simp [IterFin] at h_al0
    · simpa [h_al0, nil_AppendListInf]
    obtain ⟨al1, al2, h_al1, h_al2, rfl⟩ := h_al0
    have h_as2 : al2 ++ as1 ∈ L^ω := by
      rw [← ConcatInf_self_IterOmega] ; use al2,  as1
    specialize h_ind al1 (al2 ++ as1) h_as2 h_al1
    simpa [AppendListInf_assoc]
  · intro h_as ; use [], as
    simp [h_as, nil_AppendListInf]
    apply subset_IterStar_epsilon ; rfl

theorem IterOmega_IterStar {L : Set (List A)} :
    (L∗)^ω = L^ω := by
  ext as ; constructor
  · rintro ⟨φ, h_mono, h_init, h_rest⟩
    have h_rest' := fun m ↦ IterStar_seg_exists <| h_rest m
    choose sz ψ h_monoOn h_beg h_end h_seg using h_rest'
    have h_sz : ∀ n, sz n > 0 := by
      intro n ; by_contra ; have h_contra : sz n = 0 := by omega
      specialize h_beg n ; specialize h_end n
      simp [h_contra, length_FinSubseq] at h_end
      have := h_mono (show n < n + 1 by omega) ; omega
    let ξ n := ∑ i ∈ range n, sz i
    have h_init' : ξ 0 = 0 := by simp [ξ]
    have h_mono' : StrictMono ξ := by
      apply strictMono_nat_of_lt_succ ; intro n
      simp [ξ, Finset.sum_range_succ] ; exact h_sz n
    use (fun k ↦ φ (Segment ξ k) + ψ (Segment ξ k) (k - ξ (Segment ξ k)))
    simp [segment_zero h_mono' h_init', h_beg, h_init]
    suffices h : ∀ k,
        φ (Segment ξ k) + ψ (Segment ξ k) (k - ξ (Segment ξ k)) <
        φ (Segment ξ (k + 1)) + ψ (Segment ξ (k + 1)) (k + 1 - ξ (Segment ξ (k + 1))) ∧
        as⇊ (φ (Segment ξ k) + ψ (Segment ξ k) (k - ξ (Segment ξ k)))
          (φ (Segment ξ (k + 1)) + ψ (Segment ξ (k + 1)) (k + 1 - ξ (Segment ξ (k + 1)))) ∈ L by
      constructor
      · apply strictMono_nat_of_lt_succ ; intro k ; exact (h k).1
      · intro k ; exact (h k).2
    intro k
    have := segment_lower_bound h_mono' h_init' k
    have := segment_upper_bound h_mono' h_init' k
    have h0 : ξ (Segment ξ k + 1) = ξ (Segment ξ k) + sz (Segment ξ k) := by simp [ξ, Finset.sum_range_succ]
    specialize h_seg (Segment ξ k) (k - ξ (Segment ξ k)) (by omega)
    specialize h_end (Segment ξ k)
    simp [length_FinSubseq] at h_end
    have h1 : ψ (Segment ξ k) (k - ξ (Segment ξ k) + 1) ≤ φ (Segment ξ k + 1) - φ (Segment ξ k) := by
      have := StrictMonoOn.monotoneOn (h_monoOn (Segment ξ k))
        (show k - ξ (Segment ξ k) + 1 < sz (Segment ξ k) + 1 by omega)
        (show sz (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (by omega) ; omega
    simp [extract_FinSubseq2' h1] at h_seg
    rcases (show k + 1 < ξ (Segment ξ k + 1) ∨ k + 1 = ξ (Segment ξ k + 1) by omega) with h_k | h_k
    · have h2 := segment_range_val h_mono' (show ξ (Segment ξ k) ≤ k + 1 by omega) (h_k)
      have h3 := h_monoOn (Segment ξ k)
        (show k - ξ (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (show k - ξ (Segment ξ k) + 1 < sz (Segment ξ k) + 1 by omega)
        (show k - ξ (Segment ξ k) < k - ξ (Segment ξ k) + 1 by omega)
      simp [h2, h3, h_seg, (show k + 1 - ξ (Segment ξ k) = k - ξ (Segment ξ k) + 1 by omega)]
    · have := h_mono (show Segment ξ k < Segment ξ k + 1 by omega)
      simp [h_k, h0, h_end, (show k - ξ (Segment ξ k) + 1 = k + 1 - ξ (Segment ξ k) by omega),
        (show φ (Segment ξ k) + (φ (Segment ξ k + 1) - φ (Segment ξ k)) = φ (Segment ξ k + 1) by omega)] at h_seg
      simp [h_k, segment_idem h_mono', h_beg, h_seg]
      have h3 := h_monoOn (Segment ξ k)
        (show k - ξ (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (show sz (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (show k - ξ (Segment ξ k) < sz (Segment ξ k) by omega)
      omega
  · rintro ⟨φ, h_mono, h_init, h_rest⟩
    use φ ; simp [h_mono, h_init] ; intro n
    apply subset_IterStar_IterFin L 1
    simp [instIterFin, IterFin, epsilon_ConcatFin]
    exact h_rest n

end Languages
