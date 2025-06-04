/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib
import AutomataTheory.Sequences

open Function Set Filter

section Languages

variable {A : Type*}

def ConcatFin (L0 L1 : Set (List A)) : Set (List A) :=
  { al | ∃ al0 al1, al0 ∈ L0 ∧ al1 ∈ L1 ∧ al = al0 ++ al1 }

def ConcatInf (L0 : Set (List A)) (L1 : Set (ℕ → A)) : Set (ℕ → A) :=
  { as | ∃ al0 as1, al0 ∈ L0 ∧ as1 ∈ L1 ∧ as = AppendListInf al0 as1 }

def IterFin (L : Set (List A)) : ℕ → Set (List A)
  | 0 => {[]}
  | n + 1 => ConcatFin (IterFin L n) L

def IterStar (L : Set (List A)) : Set (List A) :=
  ⋃ n : ℕ, IterFin L n

def IterOmega (L : Set (List A)) : Set (ℕ → A) :=
  { as | ∃ φ : ℕ → ℕ, StrictMono φ ∧ φ 0 = 0 ∧ ∀ m, List.ofFn (fun k : Fin (φ (m + 1) - φ m) ↦ as (k + φ m)) ∈ L }

theorem lang_ConcatFin_epsilon_right {L : Set (List A)} :
    ConcatFin L {[]} = L := by
  ext al ; constructor
  · rintro ⟨al1, al2, h_al1, h_al2, h_al⟩
    simp at h_al2 ; simp [h_al2] at h_al ; simpa [h_al]
  · intro h_al ; use al, [] ; simp [h_al]

theorem lang_ConcatFin_union_distrib_right {L0 L1 L2 : Set (List A)} :
    ConcatFin L0 (L1 ∪ L2) = ConcatFin L0 L1 ∪ ConcatFin L0 L2 := by
  ext al ; constructor
  · rintro ⟨al0, alu, h_al0, (h_al1 | h_al2), h_al⟩
    · left ; use al0, alu
    · right ; use al0, alu
  · rintro (⟨al0, al1, h_al0, h_al1, h_al⟩ | ⟨al0, al2, h_al0, h_al2, h_al⟩)
    · use al0, al1 ; tauto
    · use al0, al2 ; tauto

end Languages
