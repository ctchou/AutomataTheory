/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Sequences

/-!
A congruence is an equivalence relation on finite sequences that is
preserved by concatenation either on the left or on the right or both.
For now, we assume only the right congruence condition.  We will
add the left congruence condition if and when it is needed.
-/

section Congruences

class Congruence (A : Type*) extends eq : Setoid (List A) where
--  left_congr : ∀ u v, eq u v → ∀ w, eq (w ++ u) (w ++ v)
  right_congr : ∀ u v, eq u v → ∀ w, eq (u ++ w) (v ++ w)

end Congruences
