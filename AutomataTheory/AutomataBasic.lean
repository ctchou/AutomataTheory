/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.OfFn
import Mathlib.Order.Filter.AtTopBot.Basic

open BigOperators Function Set Filter

section AutomataDefinition

class Automaton (A : Type*) where
  State : Type*
  init : Set State
  next : State → A → Set State

end AutomataDefinition

section AutomataFiniteRuns

variable {A : Type*}

def FinRun (M : Automaton A) (n : ℕ) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k < n, ss (k + 1) ∈ M.next (ss k) (as k)

def FinAccept (M : Automaton A) (acc : Set M.State) (n : ℕ) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, FinRun M n as ss ∧ ss n ∈ acc

def AcceptedLang (M : Automaton A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ n as, FinAccept M acc n as ∧ al = List.ofFn (fun k : Fin n ↦ as k) }

/-- It may seem strange that we use infinite sequences (namely, functions of type ℕ → *)
in the definitions about finite runs above.  In the following we give alternative
definitions using finite sequences (namely, functions of type `Fin n` → *) and show that
they are in fact equivalent to the definitions above, modulo the minor assumption that
the type `A` is inhabited.  (The theory of automata would not be very interesting anyway
if the type `A` is empty.)  We prefer the definitions above because ℕ is much easier to
work with than `Fin` types. -/

def FinRun' (M : Automaton A) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : Fin n, ss k.succ ∈ M.next (ss k) (as k)

def FinAccept' (M : Automaton A) (acc : Set M.State) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → M.State, FinRun' M n as ss ∧ ss ⟨n, by omega⟩ ∈ acc

variable {M : Automaton A} {acc : Set M.State}

def appendFunInf {X : Type*} {n : ℕ} (xs : Fin n → X) (xs' : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < n then xs ⟨k, h⟩ else xs' (n + k)

theorem FinRun'_of_FinRun {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : FinRun M n as ss) : FinRun' M n (fun k ↦ as k) (fun k ↦ ss k) := by
  constructor
  · simp ; exact h.1
  rintro ⟨k, h_k⟩
  simp [Nat.mod_eq_of_lt (by omega : k < n + 1)]
  exact h.2 k h_k

theorem FinRun_of_FinRun' [Inhabited A] {n : ℕ} {as : Fin n → A} {ss : Fin (n + 1) → M.State}
    (h : FinRun' M n as ss) : FinRun M n (appendFunInf as (const ℕ default)) (appendFunInf ss (const ℕ (ss 0))) := by
  constructor
  · simp [appendFunInf] ; exact h.1
  intro k h_k
  have h_k1 : k < n + 1 := by omega
  have h_k2 : (↑k : Fin (n + 1)) = ⟨k, h_k1⟩:= by simp [@Fin.eq_mk_iff_val_eq] ; omega
  have h_step := h.2 ⟨k, h_k⟩
  simp [h_k2] at h_step
  simpa [appendFunInf, h_k, h_k1]

theorem FinAccept'_of_FinAccept {n : ℕ} {as : ℕ → A}
    (h : FinAccept M acc n as) : FinAccept' M acc n (fun k ↦ as k) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (fun k ↦ ss k)
  constructor
  · exact FinRun'_of_FinRun h_run
  simpa

theorem FinAccept_of_FinAccept' [Inhabited A] {n : ℕ} {as : Fin n → A}
    (h : FinAccept' M acc n as) : FinAccept M acc n (appendFunInf as (const ℕ default)) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (appendFunInf ss (const ℕ (ss 0)))
  constructor
  · exact FinRun_of_FinRun' h_run
  simpa [appendFunInf]

theorem AcceptedLang_of_FinAccept' [Inhabited A] :
    AcceptedLang M acc = { al | ∃ n as, FinAccept' M acc n as ∧ al = List.ofFn as } := by
  rw [AcceptedLang, Set.ext_iff] ; intro al ; constructor
  · rintro ⟨n, as, h_acc, h_al⟩
    use n, (fun k : Fin n ↦ as k)
    constructor
    · exact FinAccept'_of_FinAccept h_acc
    · exact h_al
  · rintro ⟨n, as, h_acc, h_al⟩
    use n, (appendFunInf as (const ℕ default))
    constructor
    · exact FinAccept_of_FinAccept' h_acc
    · simpa [appendFunInf]

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
