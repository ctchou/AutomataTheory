/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Det

/-!
The powerset construction that converts a nondeterministic NA
into a deterministic NA.  This construction is used to prove
the closure of regular languages under complementation and works
even when the state type is infinite.
-/

open Function Set Filter

namespace Automata

section AutomataPSet

variable {A : Type}

/-- The states of `M.Pset` is the power set of the states of `M`.
The initial state of `M.Pset` is the set of initial state of `M`.
The next state of `M.Pset` is the set of states reachable by `M`
by consuming the samne input letter.
-/
def NA.PSet (M : NA A) : DA A where
  State := Set M.State
  init := M.init
  next := fun ps a ↦ ⋃ s ∈ ps, M.next s a

variable {M : NA A}

instance : Membership M.State M.PSet.State := by exact { mem := fun s ↦ s }

lemma na_pset_reach_init (as : ℕ → A) :
    M.PSet.DetRun as 0 = M.init := by
  simp [DA.DetRun, NA.PSet]

lemma na_pset_reach_next (as : ℕ → A) (k : ℕ) :
    M.PSet.DetRun as (k + 1) = ⋃ s ∈ M.PSet.DetRun as k, M.next s (as k) := by
  simp [DA.DetRun, NA.PSet]

/-- For any input `as`, running `M.Pset` on `as` ends in the unique state
that is exact the set of states reachable by running `M` on `as`.
-/
theorem na_pset_run (as : ℕ → A) (k : ℕ) :
    M.PSet.DetRun as k = { s : M.State | ∃ ss, M.FinRun k as ss ∧ ss k = s } := by
  induction' k with k h_ind
  · rw [na_pset_reach_init as, Set.ext_iff]
    intro s ; constructor
    · intro h_init
      use (fun k ↦ s) ; simpa [NA.FinRun]
    · rintro ⟨ss, ⟨h_init, h_next⟩, h_s⟩
      simpa [← h_s]
  rw [na_pset_reach_next as k, h_ind, Set.ext_iff]
  intro s ; constructor <;> simp
  · rintro s' ⟨ss, ⟨h_init, h_next⟩, h_s'⟩ h_s
    use (fun j ↦ if j < k + 1 then ss j else s)
    simp ; constructor
    · simpa
    intro j h_j
    rcases (by omega : j < k ∨ j = k) with h_j' | h_j'
    · simp [h_j, h_j'] ; exact h_next j h_j'
    · simpa [h_j', h_s']
  · rintro ss ⟨h_init, h_next⟩ h_s
    use (ss k)
    simp [← h_s, h_next k (by omega)]
    use ss ; simp ; constructor
    · exact h_init
    intro j h_j
    exact h_next j (by omega)

end AutomataPSet

section AcceptedLangPSet

variable {A : Type} (M : NA A) (acc : Set M.State)

def NA.PSet_Acc : Set (Set M.State) := { sset | ∃ s ∈ sset, s ∈ acc }

/-- The language accepted by `M.Pset` is the same as that accepted by `M`,
where the accepting states of `M.Pset` are those that contains at least one
accepting state of `M`.
-/
theorem acc_lang_pset :
    M.PSet.toNA.AcceptedLang (M.PSet_Acc acc) = M.AcceptedLang acc := by
  ext al ; simp only [NA.AcceptedLang, NA.FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss', h_run', h_acc'⟩, h_al⟩
    have h_sn' := da_fin_run_unique h_run' n (by omega)
    rw [na_pset_run] at h_sn'
    simp [h_sn', NA.PSet_Acc] at h_acc'
    obtain ⟨sn, ⟨ss, h_run, h_sn⟩, h_acc⟩ := h_acc'
    use n, as ; simp [h_al]
    use ss ; simp [h_run, h_sn, h_acc]
  · rintro ⟨n, as, ⟨ss, h_run, h_sn⟩, h_al⟩
    use n, as ; simp [h_al]
    use (M.PSet.DetRun as) ; constructor
    · apply da_fin_run_exists
    · rw [na_pset_run, NA.PSet_Acc]
      use (ss n) ; simp [h_sn] ; use ss

end AcceptedLangPSet
