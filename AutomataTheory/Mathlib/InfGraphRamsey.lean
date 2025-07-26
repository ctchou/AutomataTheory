/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib

/-!
This file proves a Ramsey theorem about infinite graphs.
This result really should be in Mathlib, but it is not.
-/

open Function Set

section InfGraphRamsey

theorem inf_graph_ramsey {C : Type*} [Finite C] (color : (t : Finset ℕ) → (t.card = 2) → C) :
    ∃ c : C, ∃ s : Set ℕ, s.Infinite ∧ ∀ t : Finset ℕ, (h : t.card = 2) → t.toSet ⊆ s → color t h = c := by
  sorry

end InfGraphRamsey
