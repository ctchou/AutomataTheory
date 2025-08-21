/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Det

/-!
The indexed product of deterministic automata, which is used to prove the
closure of deterministic Muller acceptance under both intersection and union.
Note that we need to make finiteness assumptions on both the index set and
each automaton's state type.
-/

open Function Set Filter

namespace Automata

section DetAutomataProd

variable {I A : Type}

def DA.Prod (M : I → DA A) : DA A where
  State := Π i : I, (M i).State
  init := fun i ↦  (M i).init
  next := fun s a ↦ fun i ↦ (M i).next (s i) a

variable (M : I → DA A)

theorem da_prod_inf_run (as : ℕ → A) (i : I) :
    (· i) ∘ (DA.Prod M).DetRun as = (M i).DetRun as := by
  ext k ; simp
  induction' k with k h_ind
  · simp [DA.DetRun] ; rfl
  · simp [DA.DetRun, ← h_ind] ; rfl

variable [Finite I] [∀ i, Finite (M i).State]

theorem da_prod_finite :
    Finite (DA.Prod M).State := by
  exact Pi.finite

theorem da_prod_inf_occ (as : ℕ → A) (i : I) :
    (· i) '' (InfOcc ((DA.Prod M).DetRun as)) =
    InfOcc ((· i) ∘ (DA.Prod M).DetRun as) := by
  exact inf_occ_proj

variable (accSet : (i : I) → Set (Set (M i).State))

def DA.MullerAcc_Inter : Set (Set (DA.Prod M).State) :=
  { acc | ∀ i : I, ((· i) '' acc) ∈ (accSet i) }

def DA.MullerAcc_Union : Set (Set (DA.Prod M).State) :=
  { acc | ∃ i : I, ((· i) '' acc) ∈ (accSet i) }

theorem det_muller_accept_inter (as : ℕ → A) :
    (DA.Prod M).MullerAccept (DA.MullerAcc_Inter M accSet) as ↔
    ∀ i : I, (M i).MullerAccept (accSet i) as := by
  simp [DA.MullerAccept, DA.MullerAcc_Inter] ; constructor
  · intro h_acc i ; specialize h_acc i
    simpa [← da_prod_inf_run M as i, ← da_prod_inf_occ M as i]
  · intro h_acc i ; specialize h_acc i
    simpa [da_prod_inf_occ M as i, da_prod_inf_run M as i]

theorem det_muller_accept_union (as : ℕ → A) :
    (DA.Prod M).MullerAccept (DA.MullerAcc_Union M accSet) as ↔
    ∃ i : I, (M i).MullerAccept (accSet i) as := by
  simp [DA.MullerAccept, DA.MullerAcc_Union] ; constructor
  · rintro ⟨i, h_acc⟩ ; use i
    simpa [← da_prod_inf_run M as i, ← da_prod_inf_occ M as i]
  · rintro ⟨i, h_acc⟩ ; use i
    simpa [da_prod_inf_occ M as i, da_prod_inf_run M as i]

end DetAutomataProd
