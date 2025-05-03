/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Basic
import AutomataTheory.AutomataDet

open BigOperators Function Set Filter Option

section AutomataPSet

open Classical

variable {A : Type*}

def AutomataPSet (M : Automata A) : DetAutomata A where
  State := Set M.State
  init := {M.init}
  next := fun ps a ↦ { ⋃ s ∈ ps, M.next s a }
  get_init := M.init
  get_next := fun ps a ↦ ⋃ s ∈ ps, M.next s a
  det_init := by simp
  det_next := by simp

variable (M : Automata A)

instance : Membership M.State (AutomataPSet M).State := by exact { mem := fun s ↦ s }

theorem automata_pset_reach_init (n : ℕ) (as : Fin n → A) :
    MakeFinRun (AutomataPSet M) n as 0 = M.init := by
  simp [MakeFinRun, AutomataPSet]

theorem automata_pset_reach_next (n : ℕ) (as : Fin n → A) (k : ℕ) (h : k < n) :
    MakeFinRun (AutomataPSet M) n as ↑(k + 1) = ⋃ s ∈ MakeFinRun (AutomataPSet M) n as k, M.next s (as ⟨k, h⟩) := by
  rw [MakeFinRun]
  have h_k : ↑(k + 1) > (0 : Fin (n + 1)) := by
    have h_0 : (0 : Fin (n + 1)) = ↑(0 : ℕ) := by simp [Fin.ext_iff]
    rw [h_0] ; refine Fin.natCast_strictMono h ?_ ; omega
  simp only [h_k, dite_true] ; simp
  congr ; simp [Fin.ext_iff] ; omega

def OptFinRun (n : ℕ) (as' : ℕ → Option A) (ss' : ℕ → Option M.State) :=
  (∃ s0 ∈ M.init, ss' 0 = some s0) ∧
  (∀ k < n, ∃ sk ak sk_1, sk_1 ∈ M.next sk ak ∧ ss' k = some sk ∧ as' k = some ak ∧ ss' (k + 1) = some sk_1)

theorem automata_pset_opt_fin_run (n : ℕ) (as : Fin n → A) (k : ℕ) (h : k < n + 1) :
    MakeFinRun (AutomataPSet M) n as k =
    { s : M.State | ∃ ss', OptFinRun M k (fun j ↦ if h : j < n then as ⟨j, h⟩ else none) ss' ∧ ss' k = some s } := by
  induction' k with k h_ind
  · simp [automata_pset_reach_init M n as]
    rw [Set.ext_iff]
    intro s0 ; simp only [mem_setOf_eq] ; constructor
    · intro h_s0
      let ss' := fun j ↦ if j = 0 then some s0 else none
      use ss' ; simpa [ss', OptFinRun]
    · rintro ⟨ss', h_run, h_s0⟩
      obtain ⟨s0', h_init, h_s0'⟩ := h_run.1
      have : s0' = s0 := by rw [← some_inj, ← h_s0, ← h_s0']
      obtain ⟨rfl⟩ := this
      assumption
  have h_k : k < n := by omega
  rw [automata_pset_reach_next M n as k (by omega), h_ind (by omega), Set.ext_iff]
  intro sk_1
  simp only [mem_iUnion, exists_prop, mem_setOf_eq] ; constructor
  · rintro ⟨sk, ⟨ss', h_run, h_sk⟩, h_sk_next⟩
    let ss'' := fun j ↦ if j < k + 1 then ss' j else if j = k + 1 then some sk_1 else none
    use ss'' ; simp [ss''] ; constructor
    · obtain ⟨s0, _⟩ := h_run.1
      use s0
      simp ; tauto
    · intro j h_j
      have h_j_n : j < n := by omega
      rcases (by omega : j < k ∨ j = k) with h_j' | h_j'
      · obtain ⟨sj, aj, sj_1, h_step⟩ := h_run.2 j h_j'
        simp [h_j_n] at h_step
        use sj, aj, sj_1
        simp [h_j, h_j'] ; tauto
      · use sk, (as ⟨k, by omega⟩), sk_1
        simp [h_j'] ; tauto
  · rintro ⟨ss', h_run, h_sk_1⟩
    obtain ⟨sk, ak, sk_1', h_sk_next', h_sk, h_ak, h_sk_1'⟩ := h_run.2 k (by omega)
    simp [h_k] at h_ak
    use sk
    have : sk_1' = sk_1 := by rw [← some_inj, ← h_sk_1, ← h_sk_1']
    obtain ⟨rfl⟩ := this
    constructor
    · use ss' ; simp [h_sk]
      constructor
      · exact h_run.1
      · intro j h_j
        exact h_run.2 j (by omega)
    · simpa [h_ak]

theorem automata_pset_fin_run (n : ℕ) (as : Fin n → A) :
    MakeFinRun (AutomataPSet M) n as n = { s : M.State | ∃ ss, FinRun M n as ss ∧ ss n = s } := by
  rw [automata_pset_opt_fin_run M n as n (by omega), Set.ext_iff]
  intro s ; constructor
  · rintro ⟨ss', h_run, h_s⟩
    have h_some : ∀ k < n + 1, ∃ s, ss' k = some s := by
      intro k h_k
      rcases (by omega : k = 0 ∨ 0 < k) with h_k' | h_k'
      · obtain ⟨s0, _, h_s0⟩ := h_run.1
        use s0 ; simpa [h_k']
      obtain ⟨_, _, sk, _, _, _, h_sk⟩ := h_run.2 (k - 1) (by omega)
      use sk ; simp [← h_sk] ; congr ; omega
    choose ss h_ss using h_some
    use (fun k ↦ ss k (k.isLt)) ; constructor
    · constructor
      · obtain ⟨s0, h_init, h_s0⟩ := h_run.1
        rw [h_ss 0 (by omega), some_inj] at h_s0
        simpa [h_s0]
      simp
      intro k
      obtain ⟨sk, ak, sk', h_step, h_sk, h_ak, h_sk'⟩ := h_run.2 k (by omega)
      simp at h_ak
      rw [h_ss k (by omega), some_inj] at h_sk
      rw [h_ss (k + 1) (by omega), some_inj] at h_sk'
      simpa [h_ak, h_sk, h_sk']
    · rw [h_ss n (by omega), some_inj] at h_s
      simpa
  · rintro ⟨ss, h_run, h_s⟩
    let ss' := fun k ↦ if h : k < n + 1 then some (ss ⟨k, h⟩) else none
    have h_n : n < n + 1 := by omega
    use ss' ; constructor
    · constructor
      · use (ss 0) ; simp [h_run.1, ss']
      · intro k h_k
        have h_k' : k < n + 1 := by omega
        use (ss k), (as ⟨k, h_k⟩), (ss (k + 1))
        have h_step := h_run.2 ⟨k, by omega⟩
        simp at h_step
        simp [ss', h_k, h_k', h_step]
        constructor <;> congr
        · rw [Nat.mod_eq_of_lt h_k']
        · rw [Nat.mod_eq_of_lt h_k',
              Nat.mod_eq_of_lt (by omega : 1 < n + 1),
              Nat.mod_eq_of_lt (by omega : k + 1 < n + 1)]
    · simp [ss', ← h_s] ; congr

end AutomataPSet
