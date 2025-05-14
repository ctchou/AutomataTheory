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

section Languages

variable {A : Type*}

def ConcatFin (L0 L1 : Set (List A)) : Set (List A) :=
  { al | ∃ al0 al1, al0 ∈ L0 ∧ al1 ∈ L1 ∧ al = al0 ++ al1 }

def ConcatInf (L0 : Set (List A)) (L1 : Set (ℕ → A)) : Set (ℕ → A) :=
  { as | ∃ al0 as1, al0 ∈ L0 ∧ as1 ∈ L1 ∧ as = AppendListInf al0 as1 }

end Languages
