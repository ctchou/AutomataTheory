/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences.Basic

/-!
Basic definitions and theorems about automata and the acceptance of
languages and (ω-)languages by automata.
-/

open Function Set Filter

namespace Automata

section AutomataDefinition

/- Some remarks about the definition of the `Automata.NA` class are in order:
* `NA` means "nondeterministic automaton".
  There is a separate `Automata.DA` class for deterministic automata.
* Note that the accepting states are not included as a part of an automaton.
  This design choice is delibeate and motivated by two facts:
  (1) There are multiple types of acceptance conditions for automata on infinite words.
  (2) Sometimes automata constructions need to treat the accepting states differently
      depending whether the automaton "runs" on finite or infinite words.
* But the state type of an automaton is included as a part of an automaton.
  This bundled design allows us to define constructions on automata more conveniently.
* The alphabet type `A` appears as a parameter because most of the automata theory
  being formalized concerns automata on a single fixed alphabet type.
* The ε transition is not included.  It is actually possible to prove the closure of
  regular languages under concatenation and Kleene star without using the ε transition.
* No finiteness assumption is made about the state type, for the properties of
  almost all automata constructions can be proved without that assumptions.
  The finite-state assumption will be made only when necessary and always explicitly.
-/
class NA (A : Type) where
  State : Type
  init : Set State
  next : State → A → Set State

end AutomataDefinition

section AutomataFiniteRuns

variable {A : Type}

/-- A finite run of an automaton.
-/
def NA.FinRun (M : NA A) (n : ℕ) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k < n, ss (k + 1) ∈ M.next (ss k) (as k)

/-- The acceptance condition for finite runs.
-/
def NA.FinAccept (M : NA A) (acc : Set M.State) (n : ℕ) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, M.FinRun n as ss ∧ ss n ∈ acc

/-- The language accepted by an automaton.
-/
def NA.AcceptedLang (M : NA A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ n as, M.FinAccept acc n as ∧ al = List.ofFn (fun k : Fin n ↦ as k) }

/-- It may seem strange that we use infinite sequences (namely, functions of types ℕ → *)
in the definitions about finite runs above.  In the following we give alternative
definitions using finite sequences (namely, functions of types `Fin n` → *) and show
that they are in fact equivalent to the definitions above, except that we occasionally
need to assume that the alphabet type `A` is inhabited.  This additional assumption is
quite acceptable because the theory of automata would not be very interesting anyway if
the alphabet type `A` is empty.  We prefer the definitions above because ℕ is much easier
to work with than `Fin` types, for two reasons.  First, we don't need to map between
`Fin` types of different sizes and between `Fin` types and ℕ.  Second, the powerful
`omega` tactic can be used to blast away virtually all simple proof obgligations
concerning sequence indices, which is a technique not available when working with
`Fin` types.  One way to think of the above definitions is that we view a finite
sequence as the equivalence class of all infinite sequences that share that finite
sequence as a prefix and the definitions "talk about" finite sequences via their
infinite-sequence representatives.
-/
def NA.FinRun' (M : NA A) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : Fin n, ss k.succ ∈ M.next (ss k.castSucc) (as k)

def NA.FinAccept' (M : NA A) (acc : Set M.State) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → M.State, M.FinRun' n as ss ∧ ss ⟨n, by omega⟩ ∈ acc

variable {M : NA A} {acc : Set M.State}

theorem na_FinRun'_of_FinRun {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : M.FinRun n as ss) : M.FinRun' n (fun k ↦ as k) (fun k ↦ ss k) := by
  constructor
  · simp ; exact h.1
  rintro ⟨k, h_k⟩
  simp
  exact h.2 k h_k

theorem na_FinRun_of_FinRun' [Inhabited A] {n : ℕ} {as : Fin n → A} {ss : Fin (n + 1) → M.State}
    (h : M.FinRun' n as ss) : M.FinRun n (as ++ (const ℕ (default : A))) (ss ++ (const ℕ (ss 0))) := by
  constructor
  · simp [instAppendFinInf, AppendFinInf] ; exact h.1
  intro k h_k
  have h_step := h.2 ⟨k, h_k⟩
  simp at h_step
  simpa [instAppendFinInf, AppendFinInf, h_k, (show k < n + 1 by omega)]

theorem na_FinAccept'_of_FinAccept {n : ℕ} {as : ℕ → A}
    (h : M.FinAccept acc n as) : M.FinAccept' acc n (fun k ↦ as k) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (fun k ↦ ss k)
  constructor
  · exact na_FinRun'_of_FinRun h_run
  simpa

theorem na_FinAccept_of_FinAccept' [Inhabited A] {n : ℕ} {as : Fin n → A}
    (h : M.FinAccept' acc n as) : M.FinAccept acc n (as ++ (const ℕ (default : A))) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (ss ++ (const ℕ (ss 0)))
  constructor
  · exact na_FinRun_of_FinRun' h_run
  simpa [instAppendFinInf, AppendFinInf]

/-- The following theorem shows that under the assumption that the alphabet type `A`
is inhabited, the definitions using infinite sequences and those using finite sequences
actually define the same notion of the accepted language of an automaton.
-/
theorem na_AcceptedLang_of_FinAccept' [Inhabited A] :
    M.AcceptedLang acc = { al | ∃ n as, M.FinAccept' acc n as ∧ al = List.ofFn as } := by
  rw [NA.AcceptedLang, Set.ext_iff] ; intro al ; constructor
  · rintro ⟨n, as, h_acc, h_al⟩
    use n, (fun k : Fin n ↦ as k)
    constructor
    · exact na_FinAccept'_of_FinAccept h_acc
    · exact h_al
  · rintro ⟨n, as, h_acc, h_al⟩
    use n, (as ++ (const ℕ (default : A)))
    constructor
    · exact na_FinAccept_of_FinAccept' h_acc
    · simpa [instAppendFinInf, AppendFinInf]

end AutomataFiniteRuns

section AutomataInfiniteRuns

variable {A : Type}

/-- An infinite run of an automaton.
-/
def NA.InfRun (M : NA A) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : ℕ, ss (k + 1) ∈ M.next (ss k) (as k)

/-- The Büchi acceptance condition is the main one we use.
But the Muller, Rabin, and Streett acceptance condtions are also
included for completeness and future use.
-/
def NA.BuchiAccept (M : NA A) (acc : Set M.State) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, M.InfRun as ss ∧ ∃ᶠ k in atTop, ss k ∈ acc

def NA.MullerAccept (M : NA A) (accSet : Set (Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, M.InfRun as ss ∧ ∃ acc ∈ accSet, ∀ s, s ∈ acc ↔ (∃ᶠ k in atTop, ss k = s)

def NA.RabinAccept (M : NA A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, M.InfRun as ss ∧ ∃ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) ∧ (∀ᶠ k in atTop, ss k ∉ pair.2)

def NA.StreettAccept (M : NA A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, M.InfRun as ss ∧ ∀ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) → (∃ᶠ k in atTop, ss k ∈ pair.2)

/-- The ω-language accepted by an automaton, using the Buchi acceptance condition.
-/
def NA.AcceptedOmegaLang (M : NA A) (acc : Set M.State) : Set (ℕ → A) :=
  { as | M.BuchiAccept acc as }

end AutomataInfiniteRuns

section AutomataBasicResults

variable {A : Type} {M : NA A}

theorem na_FinRun_FixSuffix [Inhabited A] {n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (h : M.FinRun n as ss) : M.FinRun n (FixSuffix as n default) (FixSuffix ss (n + 1) (ss 0)) := by
  rcases h with ⟨h_init, h_next⟩
  constructor
  · simpa [FixSuffix]
  intro k h_k
  simp [FixSuffix, h_k, (by omega : k < n + 1)]
  exact h_next k h_k

theorem na_FinRun_modulo {n : ℕ} {as as' : ℕ → A} {ss ss' : ℕ → M.State}
    (ha : ∀ k < n, as k = as' k) (hs : ∀ k < n + 1, ss k = ss' k) (hr : M.FinRun n as ss) : M.FinRun n as' ss' := by
  rcases hr with ⟨h_init, h_next⟩ ; constructor
  · simpa [← hs]
  intro k h_k ; specialize h_next k h_k
  simpa [← ha k h_k, ← hs k (by omega), ← hs (k + 1) (by omega)]

theorem na_FinRun_imp_FinRun {m n : ℕ} {as : ℕ → A} {ss : ℕ → M.State}
    (hmn : m < n) (hr : M.FinRun n as ss) : M.FinRun m as ss :=
  ⟨hr.1, (hr.2 · <| ·.trans hmn)⟩

theorem na_InfRun_iff_FinRun {as : ℕ → A} {ss : ℕ → M.State} :
    M.InfRun as ss ↔ ∀ n, M.FinRun n as ss := by
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

theorem acc_lang_acc_union {acc0 acc1 : Set M.State} :
    M.AcceptedLang (acc0 ∪ acc1) = M.AcceptedLang acc0 ∪ M.AcceptedLang acc1 := by
  ext al ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, (h_acc0 | h_acc1)⟩, h_al⟩
    · left ; use n, as ; simp [h_al] ; use ss
    · right ; use n, as ; simp [h_al] ; use ss
  · rintro (⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ | ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩)
    · use n, as ; simp [h_al] ; use ss ; simp [h_run, h_acc]
    · use n, as ; simp [h_al] ; use ss ; simp [h_run, h_acc]

end AutomataBasicResults
