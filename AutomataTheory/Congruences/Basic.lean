/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences.Basic
import AutomataTheory.Languages.Basic

/-!
A congruence is an equivalence relation (represented by a `Setoid` to allow
easy access to the quotient construction) on finite sequences that is
preserved by concatenation either on the left or on the right or both.
So far we need, and hence will assume, only the right congruence condition.
The left congruence condition is shown in a comment for completeness.
-/

open Function Set

section Congruences

open Classical

class Congruence (A : Type) extends eq : Setoid (List A) where
  right_congr : ∀ u v, eq u v → ∀ w, eq (u ++ w) (v ++ w)
--  left_congr : ∀ u v, eq u v → ∀ w, eq (w ++ u) (w ++ v)

variable {A : Type}

/-- The quotient type of a congruence relation.
-/
def Congruence.QuotType (c : Congruence A) := Quotient c.eq

/-- The equivalence class corresponding to an element of the quotient type.
-/
def Congruence.EqvCls (c : Congruence A) (s : c.QuotType) : Set (List A) :=
  (Quotient.mk c.eq) ⁻¹' {s}

/-- An ω-language of the form `U * V^ω`, where `U` and `V` are equivalence classes of the congruence.
-/
def Congruence.ConcatOmegaLang (c : Congruence A) (s t : c.QuotType) : Set (ℕ → A) :=
  (c.EqvCls s) * (c.EqvCls t)^ω

/-- A congruence "saturates" an ω-language `L` iff whenever U * V^ω and L has a nonempty intersection,
U * V^ω is a subset of L, for any equivalence classes `U` and `V` of the congruence.
-/
def Congruence.Saturates (c : Congruence A) (L : Set (ℕ → A)) :=
  ∀ s t : c.QuotType, (c.ConcatOmegaLang s t ∩ L).Nonempty → c.ConcatOmegaLang s t ⊆ L

/-- A congruence is "ample" iff every infinite word belongs to an ω-language of the form `U * V^ω`,
    where `U` and `V` are equivalence classes of the congruence.
-/
def Congruence.Ample (c : Congruence A) :=
  ∀ as, ∃ s t : c.QuotType, as ∈ c.ConcatOmegaLang s t

variable {c : Congruence A}

/-- If a congruence `c` saturates an ω-language `L`, then `c` saturates the complement of `L` as well.
-/
theorem congruence_saturates_compl {L : Set (ℕ → A)}
    (h_sat : c.Saturates L) : c.Saturates Lᶜ := by
  rintro s t ⟨as, h_as, h_as_c⟩ as' h_as'
  by_contra h_contra
  simp at h_contra
  have h_l : (c.ConcatOmegaLang s t ∩ L).Nonempty := by
    use as' ; simp [h_as', h_contra]
  have := h_sat s t h_l h_as
  contradiction

/-- If a congruence `c` is ample and saturates an ω-language `L`, then `L` is the union of ω-languages
    of the form `U * V^ω`, where `U` and `V` are equivalence classes of `c`.
-/
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

/-- A convenience lemma: Any two words in the same equivalence class of a congruence are congruent.
-/
theorem congruence_same_eqvcls_imp_eq {s : c.QuotType} {u u' : List A}
    (h : u ∈ c.EqvCls s) (h' : u' ∈ c.EqvCls s) : c.eq u u' := by
  apply Quotient.exact
  simp [Congruence.EqvCls] at h h'
  simp [h, h']

end Congruences
