/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.AutomataBasic

open Function Set Filter

section AutomataProd

variable {I A : Type*}

def AutomataProd (M : I → Automaton A) : Automaton A where
  State := Π i : I, (M i).State
  init := { s | ∀ i : I, (s i) ∈ (M i).init }
  next := fun s a ↦ { s' | ∀ i : I, (s' i) ∈ (M i).next (s i) a }

variable {M : I → Automaton A}

theorem automata_prod_fin_run {n : ℕ} {as : ℕ → A} {ss : ℕ → (AutomataProd M).State} :
    FinRun (AutomataProd M) n as ss ↔ ∀ i, FinRun (M i) n as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k h_k
      exact h_next k h_k i
  · intro h_all
    constructor
    · intro i
      exact (h_all i).1
    · intro k h_k i
      exact (h_all i).2 k h_k

theorem automata_prod_inf_run {as : ℕ → A} {ss : ℕ → (AutomataProd M).State} :
    InfRun (AutomataProd M) as ss ↔ ∀ i, InfRun (M i) as (fun k ↦ ss k i) := by
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

variable {I A : Type*} (M : I → Automaton A) (acc : (i : I) → Set ((M i).State))

def AutomataProd_Acc : Set (AutomataProd M).State := { s | ∀ i, (s i) ∈ (acc i) }

theorem accepted_lang_inter [Inhabited A] :
    AcceptedLang (AutomataProd M) (AutomataProd_Acc M acc) = ⋂ i : I, AcceptedLang (M i) (acc i) := by
  ext al ; simp [AcceptedLang, FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ i
    use n, as ; simp [h_al]
    use (fun k ↦ ss k i)
    constructor
    · exact automata_prod_fin_run.mp h_run i
    · exact h_acc i
  · intro h_all
    have h_all' : ∀ i, ∃ ss_i, FinRun (M i) al.length (fun k ↦ al[k]!) ss_i ∧ ss_i (al.length) ∈ acc i := by
      intro i
      obtain ⟨n, as, ⟨ss_i, h_run_i, h_acc_i⟩, h_al⟩ := h_all i
      have h_n : n = al.length := by rw [h_al, List.length_ofFn]
      obtain rfl := h_n
      use ss_i ; simp [h_acc_i]
      constructor
      · exact h_run_i.1
      intro k h_k
      have h_run_i_k := h_run_i.2 k h_k
      rw [h_al] ; simpa [h_k]
    use al.length, (fun k ↦ al[k]!) ; simp
    choose ss_i h_ss_i using h_all'
    use (fun k i ↦ ss_i i k)
    constructor
    · apply automata_prod_fin_run.mpr
      intro i
      have := (h_ss_i i).1
      simp at this
      assumption
    · intro i
      exact (h_ss_i i).2

end AcceptedLangInter
