/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences.Basic
import AutomataTheory.Languages.Basic

/-!
A congruence is an equivalence relation on finite sequences that is
preserved by concatenation either on the left or on the right or both.
For now, we assume only the right congruence condition.  We will
add the left congruence condition if and when it is needed.
-/

open Function Set

section Congruences

open Classical

class Congruence (A : Type*) extends eq : Setoid (List A) where
--  left_congr : ∀ u v, eq u v → ∀ w, eq (w ++ u) (w ++ v)
  right_congr : ∀ u v, eq u v → ∀ w, eq (u ++ w) (v ++ w)

variable {A : Type*}

def Congruence.QuotType (c : Congruence A) := Quotient c.eq

def Congruence.EqvCls (c : Congruence A) (s : c.QuotType) : Set (List A) :=
  (Quotient.mk c.eq) ⁻¹' {s}

def Congruence.ConcatOmegaLang (c : Congruence A) (s t : c.QuotType) : Set (ℕ → A) :=
  ConcatOmega (c.EqvCls s) (c.EqvCls t)

def Congruence.Saturates (c : Congruence A) (L : Set (ℕ → A)) :=
  ∀ s t : c.QuotType, (c.ConcatOmegaLang s t ∩ L).Nonempty → c.ConcatOmegaLang s t ⊆ L

def Congruence.Ample (c : Congruence A) :=
  ∀ as, ∃ s t : c.QuotType, as ∈ c.ConcatOmegaLang s t

variable {c : Congruence A}

theorem congruence_saturates_compl {L : Set (ℕ → A)}
    (h_sat : c.Saturates L) : c.Saturates Lᶜ := by
  rintro s t ⟨as, h_as, h_as_c⟩ as' h_as'
  by_contra h_contra
  simp at h_contra
  have h_l : (c.ConcatOmegaLang s t ∩ L).Nonempty := by
    use as' ; simp [h_as', h_contra]
  have := h_sat s t h_l h_as
  contradiction

theorem congruence_ample_saturates_union {L : Set (ℕ → A)}
    (h_amp : c.Ample) (h_sat : c.Saturates L) :
    L =  ⋃ s, ⋃ t, if (c.ConcatOmegaLang s t ∩ L).Nonempty then c.ConcatOmegaLang s t else ∅ := by
  ext as ; simp ; constructor
  · intro h_l
    obtain ⟨s, t, h_st⟩ := h_amp as
    use s, t ; simp [h_st]
    use as ; simp [h_st, h_l]
  · rintro ⟨s, t, h_ne, h_as⟩
    exact h_sat s t h_ne h_as

end Congruences
