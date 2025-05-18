/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.OfFn
import Mathlib.Order.Filter.AtTopBot.Basic
import AutomataTheory.Sequences

open BigOperators Function Set Filter

section AutomatonDefinition

class Automaton (A : Type*) where
  State : Type*
  init : Set State
  next : State → A → Set State

end AutomatonDefinition

section AutomataFiniteRuns

variable {A : Type*}

def FinRun (M : Automaton A) (n : ℕ) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k < n, ss (k + 1) ∈ M.next (ss k) (as k)

def FinAccept (M : Automaton A) (acc : Set M.State) (n : ℕ) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, FinRun M n as ss ∧ ss n ∈ acc

def AcceptedLang (M : Automaton A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ n as, FinAccept M acc n as ∧ al = List.ofFn (fun k : Fin n ↦ as k) }

/- It may seem strange that we use infinite sequences (namely, functions of types ℕ → *)
in the definitions about finite runs above.  In the following we give alternative
definitions using finite sequences (namely, functions of types `Fin n` → *) and show
that they are in fact equivalent to the definitions above, except that we occasionally
need to assume that the type `A` is inhabited.  This additional assumption is quite
acceptable because the theory of automata would not be very interesting anyway if
the type `A` is empty.  We prefer the definitions above because ℕ is much easier to
work with than `Fin` types.  One way to think of the above definitions is that we
view a finite sequence as the equivalence class of all infinite sequences that share
that finite sequence as a prefix and the definitions refer to finite sequences via
their infinite-sequence representatives. -/

def FinRun' (M : Automaton A) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : Fin n, ss k.succ ∈ M.next (ss k) (as k)

def FinAccept' (M : Automaton A) (acc : Set M.State) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → M.State, FinRun' M n as ss ∧ ss ⟨n, by omega⟩ ∈ acc

variable {M : Automaton A} {acc : Set M.State}

theorem automata_FinRun'_of_FinRun {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : FinRun M n as ss) : FinRun' M n (fun k ↦ as k) (fun k ↦ ss k) := by
  constructor
  · simp ; exact h.1
  rintro ⟨k, h_k⟩
  simp [Nat.mod_eq_of_lt (by omega : k < n + 1)]
  exact h.2 k h_k

theorem automata_FinRun_of_FinRun' [Inhabited A] {n : ℕ} {as : Fin n → A} {ss : Fin (n + 1) → M.State}
    (h : FinRun' M n as ss) : FinRun M n (AppendFinInf as (const ℕ default)) (AppendFinInf ss (const ℕ (ss 0))) := by
  constructor
  · simp [AppendFinInf] ; exact h.1
  intro k h_k
  have h_k1 : k < n + 1 := by omega
  have h_k2 : (↑k : Fin (n + 1)) = ⟨k, h_k1⟩:= by simp [@Fin.eq_mk_iff_val_eq] ; omega
  have h_step := h.2 ⟨k, h_k⟩
  simp [h_k2] at h_step
  simpa [AppendFinInf, h_k, h_k1]

theorem automata_FinAccept'_of_FinAccept {n : ℕ} {as : ℕ → A}
    (h : FinAccept M acc n as) : FinAccept' M acc n (fun k ↦ as k) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (fun k ↦ ss k)
  constructor
  · exact automata_FinRun'_of_FinRun h_run
  simpa

theorem automata_FinAccept_of_FinAccept' [Inhabited A] {n : ℕ} {as : Fin n → A}
    (h : FinAccept' M acc n as) : FinAccept M acc n (AppendFinInf as (const ℕ default)) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (AppendFinInf ss (const ℕ (ss 0)))
  constructor
  · exact automata_FinRun_of_FinRun' h_run
  simpa [AppendFinInf]

theorem automata_AcceptedLang_of_FinAccept' [Inhabited A] :
    AcceptedLang M acc = { al | ∃ n as, FinAccept' M acc n as ∧ al = List.ofFn as } := by
  rw [AcceptedLang, Set.ext_iff] ; intro al ; constructor
  · rintro ⟨n, as, h_acc, h_al⟩
    use n, (fun k : Fin n ↦ as k)
    constructor
    · exact automata_FinAccept'_of_FinAccept h_acc
    · exact h_al
  · rintro ⟨n, as, h_acc, h_al⟩
    use n, (AppendFinInf as (const ℕ default))
    constructor
    · exact automata_FinAccept_of_FinAccept' h_acc
    · simpa [AppendFinInf]

end AutomataFiniteRuns

section AutomataInfiniteRuns

variable {A : Type*}

def InfRun (M : Automaton A) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : ℕ, ss (k + 1) ∈ M.next (ss k) (as k)

def BuchiAccept (M : Automaton A) (acc : Set M.State) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ᶠ k in atTop, ss k ∈ acc

def MullerAccept (M : Automaton A) (accSet : Set (Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ acc ∈ accSet, ∀ s, s ∈ acc ↔ (∃ᶠ k in atTop, ss k = s)

def RabinAccept (M : Automaton A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) ∧ (∀ᶠ k in atTop, ss k ∉ pair.2)

def StreettAccept (M : Automaton A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∀ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) → (∃ᶠ k in atTop, ss k ∈ pair.2)

def AcceptedOmegaLang (M : Automaton A) (acc : Set M.State) : Set (ℕ → A) :=
  { as | BuchiAccept M acc as }

end AutomataInfiniteRuns

section AutomataBasicResults

variable {A : Type*} {M : Automaton A}

theorem automata_FinRun_FixSuffix [Inhabited A] {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : FinRun M n as ss) : FinRun M n (FixSuffix n as default) (FixSuffix (n + 1) ss (ss 0)) := by
  rcases h with ⟨h_init, h_next⟩
  constructor
  · simpa [FixSuffix]
  intro k h_k
  simp [FixSuffix, h_k, (by omega : k < n + 1)]
  exact h_next k h_k

theorem automata_InfRun_iff_FinRun {as : ℕ → A} {ss : ℕ → M.State} :
    InfRun M as ss ↔ ∀ n, FinRun M n as ss := by
  constructor
  · rintro ⟨h_init, h_next⟩ n
    constructor
    · exact h_init
    intro k h_k
    exact h_next k
  · intro h_run
    constructor
    · exact (h_run 0).1
    intro k
    apply (h_run (k + 1)).2 k ; omega

theorem accepted_lang_acc_union {acc0 acc1 : Set M.State} :
    AcceptedLang M (acc0 ∪ acc1) = AcceptedLang M acc0 ∪ AcceptedLang M acc1 := by
  ext al ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, (h_acc0 | h_acc1)⟩, h_al⟩
    · left ; use n, as ; simp [h_al] ; use ss
    · right ; use n, as ; simp [h_al] ; use ss
  · rintro (⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ | ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩)
    · use n, as ; simp [h_al] ; use ss ; simp [h_run, h_acc]
    · use n, as ; simp [h_al] ; use ss ; simp [h_run, h_acc]

end AutomataBasicResults
