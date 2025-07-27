/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice

/-!
This file proves a Ramsey theorem on infinite graphs.
This result really should be in Mathlib, but it is not.
-/

open Function Set

section InfGraphRamsey

open Classical

lemma pigeonhole_principle {X Y : Type*} [Finite Y] (f : X → Y) {s : Set X} (h_inf : s.Infinite) :
    ∃ y, ∃ t, t.Infinite ∧ t ⊆ s ∧ ∀ x ∈ t, f x = y := by
  have := h_inf.to_subtype
  obtain ⟨y, h_inf'⟩ := Finite.exists_infinite_fiber (s.restrict f)
  have h_inf_iff := Equiv.infinite_iff <| Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (fun x ↦ f x = y)
  simp [coe_eq_subtype, h_inf_iff] at h_inf'
  have h_inf'' := (infinite_coe_iff (s := { x | x ∈ s ∧ f x = y })).mp h_inf'
  use y, {x | x ∈ s ∧ f x = y}
  simpa

variable {Color Vertex : Type*} [Finite Color]
abbrev Edge := Finset Vertex
variable (color : (e : Edge) → Color)

structure InfVSet (Vertex : Type*) where
  set : Set Vertex
  inf : set.Infinite

structure Selection (Color Vertex : Type*) where
  vs : InfVSet Vertex
  v : Vertex
  c : Color

def selection_prop (ivs : InfVSet Vertex) (S : Selection Color Vertex) : Prop :=
  S.vs.set ⊆ ivs.set ∧ S.v ∈ ivs.set \ S.vs.set ∧ ∀ u ∈ S.vs.set, color {S.v, u} = S.c

lemma selection_exists (ivs : InfVSet Vertex) :
    ∃ S : Selection Color Vertex, selection_prop color ivs S := by
  obtain ⟨v, h_v⟩ := Set.Infinite.nonempty ivs.inf
  let f u := color {v, u}
  obtain ⟨c, vs, h_inf, h_vs, h_col⟩ := pigeonhole_principle f <| Set.Infinite.diff ivs.inf (finite_singleton v)
  simp [subset_diff] at h_vs
  obtain ⟨h_vs, h_v'⟩ := h_vs
  let ivs' := InfVSet.mk vs h_inf
  use {vs := ivs', v := v, c := c}
  simp [selection_prop, ivs', h_vs, h_v, h_v']
  exact h_col

variable [Infinite Vertex]

noncomputable def selection_seq : ℕ → Selection Color Vertex
  | 0 => choose (selection_exists color (InfVSet.mk univ infinite_univ))
  | n + 1 => choose (selection_exists color (selection_seq n).vs)

lemma selection_seq_prop' (n : ℕ) :
    ∃ ivs : InfVSet Vertex, selection_prop color ivs (selection_seq color n) ∧
      (ivs.set = ⋂ m < n, (selection_seq color m).vs.set) := by
  induction' n with n h_ind
  . use (InfVSet.mk univ infinite_univ) ; simp
    exact choose_spec (selection_exists color (InfVSet.mk univ infinite_univ))
  obtain ⟨ivs, h_ivs, h_eq⟩ := h_ind
  use (selection_seq color n).vs ; constructor
  · exact choose_spec (selection_exists color (selection_seq color n).vs)
  · simp [(show ∀ m, m < n + 1 ↔ m < n ∨ m = n by omega),
      iInter_or, iInter_inter_distrib, iInter_iInter_eq_left, ← h_eq]
    exact h_ivs.1

lemma selection_seq_prop :
    ∃ vs : ℕ → Set Vertex, ∃ v : ℕ → Vertex, ∃ c : ℕ → Color,
    ∀ n, vs n ⊆ (⋂ m < n, vs m) ∧ v n ∈ (⋂ m < n, vs m) \ (vs n) ∧ ∀ u ∈ vs n, color {v n, u} = c n := by
  use (fun k ↦ (selection_seq color k).vs.set)
  use (fun k ↦ (selection_seq color k).v)
  use (fun k ↦ (selection_seq color k).c)
  intro n
  obtain ⟨ivs, h_ivs, h_eq⟩ := selection_seq_prop' color n
  rw [← h_eq]
  exact h_ivs

theorem inf_graph_ramsey :
    ∃ c : Color, ∃ s : Set Vertex, s.Infinite ∧ ∀ e : Edge, e.card = 2 → e.toSet ⊆ s → color e = c := by
  obtain ⟨vs, v, c, h_sel⟩ := selection_seq_prop color
  simp only [forall_and] at h_sel
  obtain ⟨h_vs, h_v, h_c⟩ := h_sel
  have h_lem1 : ∀ m n, m < n → v n ∈ vs m := by
    intro m n h_m_n
    suffices h1 : (⋂ m < n, vs m) ⊆ vs m by aesop
    exact biInter_subset_of_mem h_m_n
  obtain ⟨c', s', h_s'_inf, h_s'_col⟩ : ∃ c' : Color, ∃ s' : Set ℕ, s'.Infinite ∧ ∀ n ∈ s', c n = c' := by
    obtain ⟨c', s', h_s'_inf, _, h_s'col⟩ := pigeonhole_principle c infinite_univ
    use c', s'
  use c', (v '' s')
  have h_v_inj : Injective v := by
    intro m n h_v_eq
    by_contra h_contra
    wlog h : m < n generalizing m n with h'
    · exact h' h_v_eq.symm (by omega) (by omega)
    have := h_lem1 m n h
    have := h_v m
    aesop
  constructor
  · exact Infinite.image (injOn_of_injective h_v_inj (s := s')) h_s'_inf
  simp only [Finset.card_eq_two]
  rintro e ⟨v1, v2, h_ne, rfl⟩
  simp [pair_subset_iff]
  rintro m h_m rfl n h_n rfl
  have h_ne' : m ≠ n := by by_contra h_contra ; simp [h_contra] at h_ne
  wlog h : m < n generalizing m n with h'
  · rw [Finset.pair_comm]
    exact h' n h_n m h_m h_ne.symm h_ne'.symm (by omega)
  simp [h_c m (v n) (h_lem1 m n h), h_s'_col m h_m]

end InfGraphRamsey
