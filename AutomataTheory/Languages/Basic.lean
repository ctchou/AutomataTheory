/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences.Basic

/-!
This file contains some basic definitions and theorems about
languages (i.e., subsets of `List A`) and ω-languages (i.e., subsets of `ℕ → A`),
where `A` is the type of "alphabet".
-/

open Function Set Filter

section Languages

variable {A : Type*}

def ConcatFin (L0 L1 : Set (List A)) : Set (List A) :=
  { al | ∃ al0 al1, al0 ∈ L0 ∧ al1 ∈ L1 ∧ al = al0 ++ al1 }

instance : Mul (Set (List A)) :=
  { mul := ConcatFin }

def ConcatInf (L0 : Set (List A)) (L1 : Set (ℕ → A)) : Set (ℕ → A) :=
  { as | ∃ al0 as1, al0 ∈ L0 ∧ as1 ∈ L1 ∧ as = AppendListInf al0 as1 }

def IterFin (L : Set (List A)) : ℕ → Set (List A)
  | 0 => {[]}
  | n + 1 => (IterFin L n) * L

def IterStar (L : Set (List A)) : Set (List A) :=
  ⋃ n : ℕ, IterFin L n

def IterOmega (L : Set (List A)) : Set (ℕ → A) :=
  { as | ∃ φ : ℕ → ℕ, StrictMono φ ∧ φ 0 = 0 ∧ ∀ m, FinSubseq as (φ m) (φ (m + 1)) ∈ L }

def ConcatOmega (L0 L1 : Set (List A)) : Set (ℕ → A) :=
  ConcatInf L0 (IterOmega L1)

theorem lang_ConcatFin_epsilon_left {L : Set (List A)} :
    {[]} * L = L := by
  ext al ; constructor
  · rintro ⟨al1, al2, h_al1, h_al2, h_al⟩
    simp at h_al1 ; simp [h_al1] at h_al ; simpa [h_al]
  · intro h_al ; use [], al ; simp [h_al]

theorem lang_ConcatFin_epsilon_right {L : Set (List A)} :
    L * {[]} = L := by
  ext al ; constructor
  · rintro ⟨al1, al2, h_al1, h_al2, h_al⟩
    simp at h_al2 ; simp [h_al2] at h_al ; simpa [h_al]
  · intro h_al ; use al, [] ; simp [h_al]

theorem lang_ConcatFin_union_distrib_right {L0 L1 L2 : Set (List A)} :
    L0 * (L1 ∪ L2) = L0 * L1 ∪ L0 * L2 := by
  ext al ; constructor
  · rintro ⟨al0, alu, h_al0, (h_al1 | h_al2), h_al⟩
    · left ; use al0, alu
    · right ; use al0, alu
  · rintro (⟨al0, al1, h_al0, h_al1, h_al⟩ | ⟨al0, al2, h_al0, h_al2, h_al⟩)
    · use al0, al1 ; tauto
    · use al0, al2 ; tauto

theorem lang_ConcatInf_empty_left {L : Set (ℕ → A)} :
    ConcatInf ∅ L = ∅ := by
  ext as ; simp
  rintro ⟨al, as, h_al, _⟩
  simp at h_al

theorem congruence_mem_concat_omega_lang {L0 L1 : Set (List A)} {as : ℕ → A}
    (h : as ∈ ConcatOmega L0 L1) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      FinSubseq as 0 (φ 0) ∈ L0 ∧ ∀ m, FinSubseq as (φ m) (φ (m + 1)) ∈ L1 := by
  obtain ⟨al0, as1, h_al0, ⟨φ1, h_mono, h_φ1_0, h_φ1_sub⟩, rfl⟩ := h
  use (fun m ↦ φ1 (m) + al0.length)
  constructorm* _ ∧ _
  · intro m n h_mn
    have := h_mono h_mn
    grind
  · simp [FinSubseq, AppendListInf, h_φ1_0, h_al0]
  · intro m
    have h1 : φ1 (m + 1) + al0.length - (φ1 m + al0.length) = φ1 (m + 1) - φ1 m := by omega
    specialize h_φ1_sub m
    simpa [FinSubseq, ← Nat.add_assoc, appendListInf_elt_skip_list, h1]

end Languages
