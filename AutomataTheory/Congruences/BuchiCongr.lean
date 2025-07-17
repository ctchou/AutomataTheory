/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Automata.Pair

/-!
The theory of an automaton-based congruence used by J.R. Büchi to
prove the closure of ω-regular langauges under complementation.
-/

open Function Set

section BuchiCongr

variable {A : Type}

def Automaton.BuchiCongr (M : Automaton A) (acc : Set M.State) : Congruence A where
  eq.r u v := ∀ s s' : M.State,
    (u ∈ M.PairLang s s' ↔ v ∈ M.PairLang s s') ∧ (u ∈ M.PairAccLang acc s s' ↔ v ∈ M.PairAccLang acc s s')
  eq.iseqv.refl := by simp
  eq.iseqv.symm := by intro u v h s s' ; simp_all only [and_self]
  eq.iseqv.trans := by intro u v w h1 h2 s s' ; simp_all only [and_self]
  right_congr := by
    intro u v h w s s'
    constructor <;> [constructor ; constructor] <;> intro h'
    · obtain ⟨t, h_u, h_w⟩ := pair_lang_split h'
      have h_v := (h s t).1.mp h_u
      exact pair_lang_concat h_v h_w
    · obtain ⟨t, h_v, h_w⟩ := pair_lang_split h'
      have h_u := (h s t).1.mpr h_v
      exact pair_lang_concat h_u h_w
    · obtain ⟨t, (⟨h_u, h_w⟩ | ⟨h_u, h_w⟩)⟩ := pair_acc_lang_split h'
      · have h_v := (h s t).2.mp h_u
        exact pair_acc_lang_concat_0 h_v h_w
      · have h_v := (h s t).1.mp h_u
        exact pair_acc_lang_concat_1 h_v h_w
    · obtain ⟨t, (⟨h_v, h_w⟩ | ⟨h_v, h_w⟩)⟩ := pair_acc_lang_split h'
      · have h_u := (h s t).2.mpr h_v
        exact pair_acc_lang_concat_0 h_u h_w
      · have h_u := (h s t).1.mpr h_v
        exact pair_acc_lang_concat_1 h_u h_w

end BuchiCongr
