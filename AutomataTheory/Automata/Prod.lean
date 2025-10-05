/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Basic

/-!
The indexed product of automata, which is used to prove the closure of
regular langauges under intersection.  The closure of ω-regular langauges
under intersection requires a more elaborate construction (see AutomataOI2.lean).
Note that the theorems in this file are true even when the alphabet,
state, or index types are infinite.
-/

open Function Set Filter Stream'

namespace Automata

section AutomataProd

variable {I A : Type}

def NA.Prod (M : I → NA A) : NA A where
  State := Π i : I, (M i).State
  init := { s | ∀ i : I, (s i) ∈ (M i).init }
  next := fun s a ↦ { s' | ∀ i : I, (s' i) ∈ (M i).next (s i) a }

variable {M : I → NA A}

theorem na_prod_fin_run {n : ℕ} {as : Stream' A} {ss : Stream' (NA.Prod M).State} :
    (NA.Prod M).FinRun n as ss ↔ ∀ i, (M i).FinRun n as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k h_k ; exact h_next k h_k i
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k h_k i ; exact (h_all i).2 k h_k

theorem na_prod_inf_run {as : Stream' A} {ss : Stream' (NA.Prod M).State} :
    (NA.Prod M).InfRun as ss ↔ ∀ i, (M i).InfRun as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k ; apply h_next
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k i ; exact (h_all i).2 k

end AutomataProd

section AcceptedLangInter

variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))

def NA.Prod_Acc : Set (NA.Prod M).State := { s | ∀ i, (s i) ∈ (acc i) }

/-- The language accepted by the product NA is the intersection of the languages
accepted by the component automata.
-/
theorem acc_lang_inter [Inhabited A] :
    (NA.Prod M).AcceptedLang (NA.Prod_Acc M acc) = ⋂ i : I, (M i).AcceptedLang (acc i) := by
  ext al ; simp [NA.AcceptedLang, NA.FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ i
    use n, as ; simp [h_al]
    use (fun k ↦ ss k i) ; constructor
    · exact na_prod_fin_run.mp h_run i
    · exact h_acc i
  · intro h_all
    have h_all' : ∀ i, ∃ ss_i, (M i).FinRun al.length al.padDefault ss_i ∧ ss_i (al.length) ∈ acc i := by
      intro i ; obtain ⟨n, as, ⟨ss_i, h_run_i, h_acc_i⟩, h_al⟩ := h_all i
      have h_n : n = al.length := by simp [← h_al, length_extract]
      obtain rfl := h_n
      use ss_i ; simp [h_acc_i]
      constructor
      · exact h_run_i.1
      intro k h_k
      have h1 : k < (as.extract 0 al.length).length := by simp [length_extract, h_k]
      have h2 : al.padDefault k = as k := by
        rw [← h_al] ; simp (disch := omega) [padDefault_elt_left, get_extract']
      simp [h2, h_run_i.2 k h_k]
    use al.length, al.padDefault ; simp [extract_padDefault]
    choose ss_i h_ss_i using h_all'
    use (fun k i ↦ ss_i i k) ; constructor
    · apply na_prod_fin_run.mpr
      intro i ; simpa using (h_ss_i i).1
    · intro i ; exact (h_ss_i i).2

end AcceptedLangInter
