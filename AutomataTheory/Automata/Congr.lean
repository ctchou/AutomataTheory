/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Congruences.Basic
import AutomataTheory.Automata.Det

/-!
The deterministic automaton corresponding to a right congruence relation.
Note that the theorems in this file do not require that the congruence
relation is of finite index.
-/

open Function Set

section AutomataCongr

variable {A : Type}

/-- The states of `c.toDA` are the equivalence classes of the congruence `c`.
Its initial state is `⟦ [] ⟧` and its transition function appends the input
letter `a` at the end of any representative in the state.
The right congruence condition guarantees that it doesn't matter which
representative is chosen.
-/
def Congruence.toDA (c : Congruence A) : Automata.DA A where
  State := c.QuotType
  init := ⟦ [] ⟧
  next := fun s a ↦ Quotient.lift (fun u ↦ ⟦ u ++ [a] ⟧) ( by
    intro u v h_eq ; simp [Congruence.QuotType]
    exact Congruence.right_congr u v h_eq [a]
  ) s

variable {c : Congruence A}

/-- Running `c.toDA` on input `as` ends in state `⟦ as ⟧`.
-/
theorem automaton_congr_run (as : ℕ → A) (n : ℕ) :
    c.toDA.DetRun as n = ⟦ as ⇊ 0 n ⟧ := by
  induction' n with n h_ind
  · simp [Automata.DA.DetRun, Congruence.toDA, extract_nil]
  simp only [Automata.DA.DetRun, h_ind]
  simp only [Congruence.toDA, Quotient.lift_mk]
  simp [extract_succ_right]

/-- The language accepted by `c.toDA` with a unique accepting state `s`
is exactly the equivalence class of `s`.
-/
theorem acc_lang_congr [Inhabited A] (s : c.toDA.State) :
    c.toDA.toNA.AcceptedLang {s} = c.EqvCls s := by
  ext al ; simp [Automata.NA.AcceptedLang, Automata.NA.FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, rfl⟩, rfl⟩
    have h_ss_n := Automata.da_fin_run_unique h_run n (by omega)
    simp [h_ss_n, automaton_congr_run, Congruence.EqvCls]
  · rintro ⟨rfl⟩
    use al.length, al.padDefault ; simp [extract_padDefault]
    use (c.toDA.DetRun al.padDefault) ; constructor
    · exact Automata.da_fin_run_exists al.length al.padDefault
    · simp [automaton_congr_run, extract_padDefault]

end AutomataCongr
