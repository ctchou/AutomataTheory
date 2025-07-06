/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.AutomataDet

/-!
The powerset construction that converts a nondeterministic automaton
into a deterministic automaton.  This construction is used to prove
the closure of regular languages under complementation and works
even when the state type is infinite.
-/

open Function Set Filter

section AutomataPSet

variable {A : Type*}

def AutomataPSet (M : Automaton A) : DetAutomaton A where
  State := Set M.State
  init := M.init
  next := fun ps a ↦ ⋃ s ∈ ps, M.next s a

variable {M : Automaton A}

instance : Membership M.State (AutomataPSet M).State := by exact { mem := fun s ↦ s }

theorem automata_pset_reach_init (as : ℕ → A) :
    MakeDetRun (AutomataPSet M) as 0 = M.init := by
  simp [MakeDetRun, AutomataPSet]

theorem automata_pset_reach_next (as : ℕ → A) (k : ℕ) :
    MakeDetRun (AutomataPSet M) as (k + 1) = ⋃ s ∈ MakeDetRun (AutomataPSet M) as k, M.next s (as k) := by
  simp [MakeDetRun, AutomataPSet]

theorem automata_pset_run (as : ℕ → A) (k : ℕ) :
    MakeDetRun (AutomataPSet M) as k = { s : M.State | ∃ ss, FinRun M k as ss ∧ ss k = s } := by
  induction' k with k h_ind
  · rw [automata_pset_reach_init as, Set.ext_iff]
    intro s ; constructor
    · intro h_init
      use (fun k ↦ s) ; simpa [FinRun]
    · rintro ⟨ss, ⟨h_init, h_next⟩, h_s⟩
      simpa [← h_s]
  rw [automata_pset_reach_next as k, h_ind, Set.ext_iff]
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

section AcceptedLangPSet

variable {A : Type*} (M : Automaton A) (acc : Set M.State)

def AutomataPSet_Acc : Set (Set M.State) := { sset | ∃ s ∈ sset, s ∈ acc }

theorem accepted_lang_pset :
    AcceptedLang (AutomataPSet M).toAutomaton (AutomataPSet_Acc M acc) = AcceptedLang M acc := by
  ext al ; simp only [AcceptedLang, FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss', h_run', h_acc'⟩, h_al⟩
    have h_sn' := det_automata_fin_run_unique h_run' n (by omega)
    rw [automata_pset_run] at h_sn'
    simp [h_sn', AutomataPSet_Acc] at h_acc'
    obtain ⟨sn, ⟨ss, h_run, h_sn⟩, h_acc⟩ := h_acc'
    use n, as ; simp [h_al]
    use ss ; simp [h_run, h_sn, h_acc]
  · rintro ⟨n, as, ⟨ss, h_run, h_sn⟩, h_al⟩
    use n, as ; simp [h_al]
    use (MakeDetRun (AutomataPSet M) as) ; constructor
    · apply det_automata_fin_run_exists
    · rw [automata_pset_run, AutomataPSet_Acc]
      use (ss n) ; simp [h_sn] ; use ss

end AcceptedLangPSet

end AutomataPSet
