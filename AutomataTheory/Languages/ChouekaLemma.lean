/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import AutomataTheory.Languages.RegLang
import AutomataTheory.Mathlib.InfGraphRamsey

/-!
This file proves the "basic lemma" in section 5 of Choueka's paper
(see README for the reference).
-/

open Function Set List Filter
open scoped Computability

open Classical

namespace Automata

section ChouekaLemma

variable {A : Type}

/-- The Choueka language of a deterministic automaton `M` with an accepting set `acc`.
The language accepted by `(M, acc)` is meant to be `V∗` for some regular language `V`.
It will be shown that the Choueka language is regular and satisfies the equation:
V^ω = V∗ * (M.ChouekaLang acc)↗ω
-/
def DA.ChouekaLang (M : DA A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ m, 0 < m ∧ m < al.length ∧
    M.RunOn (al.extract 0 m) ∈ acc ∧ M.RunOn (al.extract m al.length) = M.RunOn al ∧
    ∀ k, m < k → k < al.length → ¬ M.RunOn (al.extract m k) = M.RunOn (al.extract 0 k) }

/-- A technical lemma for use in the next theorem.
-/
lemma greater_subseq_lemma (φ φ' : ℕ → ℕ) (hi : Injective φ') :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, φ (σ n) < φ' (σ (n + 1)) := by
  have h_step : ∀ n, ∃ m > n, φ n < φ' m := by
    intro n
    have h_inf : {m | m > n}.Infinite := by
      apply infinite_of_forall_exists_gt ; intro k
      use (k + n + 1) ; simp ; omega
    have h_inf' := Infinite.image (injOn_of_injective hi) h_inf
    have h_fin : {m | m ≤ φ n}.Finite := by exact finite_le_nat (φ n)
    obtain ⟨k, ⟨m, h_m, rfl⟩, h_m'⟩ := Infinite.exists_notMem_finite h_inf' h_fin
    simp at h_m h_m' ; use m
  choose f h_f h_φ using h_step
  use (fun k ↦ f^[k] 0) ; constructor
  · apply strictMono_nat_of_lt_succ ; simp [iterate_succ_apply', h_f]
  · simp [iterate_succ_apply', h_φ]

/-- The ω-limit of the Choueka language of `M` is a subset of the ω-power of the language of `M`.
Note that this theorem does not need to assume that `M` is finite-state.
-/
theorem choueka_lang_omega_limit_subset_omega_power [Inhabited A] {M : DA A} {acc : Set M.State} :
    (M.ChouekaLang acc)↗ω ⊆ (M.toNA.AcceptedLang acc)^ω := by
  intro as ; simp [instOmegaLimit, OmegaLimit, frequently_iff_strict_mono]
  intro φ h_φ_mono h_prefix
  have h_m_ex : ∀ n, ∃ m, 0 < m ∧ m < φ n ∧
      M.RunOn (as ⇊ 0 m) ∈ acc ∧ M.RunOn (as ⇊ m (φ n)) = M.RunOn (as ⇊ 0 (φ n)) ∧
      ∀ k, m < k → k < φ n → M.RunOn (as ⇊ m k) ≠ M.RunOn (as ⇊ 0 k) := by
    intro n
    obtain ⟨m, h_m0, h_m1, h_acc, h_run, h_run'⟩ := h_prefix n
    simp [length_FinSubseq] at h_m1
    simp [-extract_eq_drop_take, extract_FinSubseq2 (show m ≤ φ n by omega)] at h_acc
    simp [-extract_eq_drop_take, extract_FinSubseq1] at h_run
    use m ; simp [h_m0, h_m1, h_acc, h_run]
    intro k h_k h_k'
    specialize h_run' k h_k (by simp [length_FinSubseq, h_k'])
    simp [-extract_eq_drop_take, extract_FinSubseq2 (show k ≤ φ n by omega)] at h_run'
    exact h_run'
  choose φ' h_φ'_0 h_φ'_n h_acc h_run h_run' using h_m_ex
  have h_inj : Injective φ' := by
    intro n1 n2 h_φ' ; by_contra h_contra
    wlog h : n1 < n2 generalizing n1 n2 with h'
    · exact h' h_φ'.symm (by omega) (by omega)
    have := h_φ_mono h ; have := h_φ'_n n1 ; have := h_run n1
    have := h_run' n2 (φ n1) (by omega) (by omega)
    simp_all
  obtain ⟨σ, h_σ_mono, h_φ_φ'⟩ := greater_subseq_lemma φ φ' h_inj
  use (fun k ↦ if k = 0 then 0 else φ' (σ (k - 1))) ; simp ; constructor
  · apply strictMono_nat_of_lt_succ ; intro n
    rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n]
    · exact h_φ'_0 (σ 0)
    have := h_φ'_n (σ (n - 1))
    have := h_φ_φ' (n - 1)
    grind
  · intro n
    simp [da_acc_lang_iff_run_acc]
    rcases (show n = 0 ∨ ¬ n = 0 by omega) with h_n | h_n <;> simp [h_n]
    · exact h_acc (σ 0)
    have h1 := h_φ'_n (σ (n - 1))
    have h2 := h_φ_φ' (n - 1) ; simp [show n - 1 + 1 = n by omega] at h2
    have h3 := finSubseq_append_finSubseq as (show φ' (σ (n - 1)) ≤ φ (σ (n - 1)) by omega)
      (show φ (σ (n - 1)) ≤ φ' (σ n) by omega)
    have h4 := h_run (σ (n - 1)) ; simp [DA.RunOn] at h4
    simp [← h3, DA.RunOn, da_run_from_on_append, h4]
    have h5 := finSubseq_append_finSubseq as (show 0 ≤ φ (σ (n - 1)) by omega)
      (show φ (σ (n - 1)) ≤ φ' (σ n) by omega)
    simp [← da_run_from_on_append, h5]
    exact h_acc (σ n)

/-- This lemma derives a form of the Ramsey theorem suitable for use in the next theorem.
-/
lemma ramsey_lemma {C : Type} {cs : Set C} {φ : ℕ → ℕ} {col : ℕ → ℕ → C}
    (h_fin : cs.Finite) (h_mono : StrictMono φ) (h_col : ∀ i j, i < j → col (φ i) (φ j) ∈ cs) :
    ∃ c ∈ cs, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i j, i < j → col (φ (σ i)) (φ (σ j)) = c := by
  let Vertex := ↑(Set.range φ)
  have : Infinite Vertex := by refine Infinite.to_subtype (strict_mono_infinite h_mono)
  let Color := {c // c ∈ cs}
  have : Finite Color := by exact h_fin
  have φ' := Equiv.ofInjective φ <| StrictMono.injective h_mono
  let color (e : Finset Vertex) : Color :=
    let ns := e.image φ'.invFun
    if h_2 : ns.card = 2 then
      have h_ne : ns.Nonempty := by apply Finset.card_ne_zero.mp ; simp [h_2]
      ⟨col (φ (ns.min' h_ne)) (φ (ns.max' h_ne)), by
        obtain ⟨x, y, h_xy, h_ns⟩ := Finset.card_eq_two.mp h_2
        simp [h_ns, h_col (min x y) (max x y) (by simp [h_xy.symm])]⟩
    else ⟨col (φ 0) (φ 1), by exact h_col 0 1 (by omega)⟩
  obtain ⟨c, vs, h_inf_vs, h_col_vs⟩ := inf_graph_ramsey color
  use ↑c ; constructor
  · exact Subtype.coe_prop c
  let ns := φ' ⁻¹' vs
  have h_inf_ns : ns.Infinite := by
    apply Infinite.preimage h_inf_vs
    exact subset_range_of_surjective φ'.surjective vs
  obtain ⟨σ, h_mono_σ, h_ns⟩ := infinite_strict_mono h_inf_ns
  use σ ; simp [h_mono_σ] ; intro i j h_ij
  obtain ⟨rfl⟩ := h_col_vs {φ' (σ i), φ' (σ j)} (by
    apply Finset.card_pair ; by_contra h_contra
    have := StrictMono.injective h_mono_σ <| φ'.injective h_contra ; omega
  ) (by
    simp [insert_subset_iff] ; constructor
    · have h_i : σ i ∈ ns := by simp [← h_ns]
      unfold ns at h_i ; rwa [← mem_preimage]
    · have h_j : σ j ∈ ns := by simp [← h_ns]
      unfold ns at h_j ; rwa [← mem_preimage])
  have h_2 : Finset.card {σ i, σ j} = 2 := by
    apply Finset.card_pair ; by_contra h_contra
    have := StrictMono.injective h_mono_σ h_contra ; omega
  have h_ij_σ := h_mono_σ h_ij
  simp [color, h_2, min_eq_left_of_lt h_ij_σ, max_eq_right_of_lt h_ij_σ]

/-- If the language accepted by `M` is of the form `V∗`, then `V^ω ⊆ V∗ * (M.ChouekaLang acc)↗ω`.
Note that this theorem does need to assume that `M` is finite-state.
-/
theorem choueka_lang_omega_power_subset_omega_limit [Inhabited A]
    {M : DA A} [Finite M.State] {acc : Set M.State}
    {V : Set (List A)} (h_lang : M.toNA.AcceptedLang acc = V∗) :
    V^ω ⊆ V∗ * (M.ChouekaLang acc)↗ω := by
  rintro as ⟨φ, h_φ_mono, h_φ_0, h_φ_V⟩
  have h_kstar : ∀ i j, i ≤ j → (as⇊ (φ i) (φ (j))) ∈ V∗ := by
    intro i j h_ij ; simp [instIterStar, IterStar]
    use (j - i) ; generalize h_n : j - i = n
    induction' n with n h_ind generalizing i j <;> simp [instIterFin, IterFin]
    · simp [empty_FinSubseq, (show i = j by omega)]
    use (as ⇊ (φ i) (φ (j - 1))), (as ⇊ (φ (j - 1)) (φ j)) ; constructorm* _ ∧ _
    · exact h_ind i (j - 1) (by omega) (by omega)
    · specialize h_φ_V (j - 1)
      simp [(show j - 1 + 1 = j by omega)] at h_φ_V
      exact h_φ_V
    · apply finSubseq_append_finSubseq <;>
        apply StrictMono.monotone h_φ_mono <;> omega
  let color (i j : ℕ) : M.State := M.RunOn (as ⇊ i j)
  have h_color : ∀ i j, i < j → color (φ i) (φ j) ∈ acc := by
    intro i j h_ij ; simp [color, ← da_acc_lang_iff_run_acc, h_lang]
    apply h_kstar ; omega
  obtain ⟨s, h_acc, σ, h_σ_mono, h_σ_color⟩ := ramsey_lemma (acc.toFinite) h_φ_mono h_color
  simp [color] at h_σ_color
  use (as ⇊ 0 (φ (σ 0))), (as <<< (φ (σ 0)))
  simp [appendListInf_FinSubseq_SuffixFrom] ; constructor
  · specialize h_kstar 0 (σ 0) (by omega)
    simp [h_φ_0] at h_kstar
    exact h_kstar
  apply frequently_iff_strict_mono.mpr
  simp [suffixFrom_FinSubseq0]
  let p k j := φ (σ k) < j ∧ j ≤ φ (σ (k + 1)) ∧ M.RunOn (as ⇊ (φ (σ k)) j) = M.RunOn (as ⇊ (φ (σ 0)) j)
  have h_p_ex : ∀ k, ∃ j, p k j := by
    intro k ; use (φ (σ (k + 1)))
    simp [p, h_φ_mono <| h_σ_mono (show k < k + 1 by omega)]
    have := h_σ_color k (k + 1) (by omega)
    have := h_σ_color 0 (k + 1) (by omega)
    simp_all
  let ξ k := Nat.find (h_p_ex k)
  have h_ξ_spec : ∀ k, p k (ξ k) := by intro k ; exact Nat.find_spec (h_p_ex k)
  have h_ξ_min : ∀ k j, j < ξ k → ¬ p k j := by intro k j h_j ; exact Nat.find_min (h_p_ex k) h_j
  use (fun k ↦ ξ (k + 1) - φ (σ 0)) ; constructor
  · intro j k h_jk ; simp
    obtain ⟨_, _, _⟩ := h_ξ_spec (j + 1)
    obtain ⟨_, _, _⟩ := h_ξ_spec (k + 1)
    have := h_φ_mono <| h_σ_mono (show 0 < j + 1 by omega)
    have := StrictMono.monotone h_φ_mono <| StrictMono.monotone h_σ_mono (show j + 1 + 1 ≤ k + 1 by omega)
    omega
  intro k ; use (φ (σ (k + 1)) - φ (σ 0))
  have h_k1_0 := h_φ_mono <| h_σ_mono (show 0 < k + 1 by omega)
  obtain ⟨h_k1_ξ, h_k1_ξ', h_k1_run⟩ := h_ξ_spec (k + 1)
  have h1 : φ (σ (k + 1)) - φ (σ 0) < ξ (k + 1) - φ (σ 0) := by omega
  have h2 : φ (σ 0) + (ξ (k + 1) - φ (σ 0)) = ξ (k + 1) := by omega
  have h3 : φ (σ 0) + (φ (σ (k + 1)) - φ (σ 0)) = φ (σ (k + 1)) := by omega
  simp [-extract_eq_drop_take, length_FinSubseq, h_k1_0, h1]
  rw [h2]
  simp [-extract_eq_drop_take, extract_FinSubseq2' (le_of_lt h1), extract_FinSubseq2']
  rw [h2, h3]
  simp [-extract_eq_drop_take, h_k1_run, h_σ_color 0 (k + 1) (by omega), h_acc]
  intro j h_j1 h_j2
  have h_j_min := h_ξ_min (k + 1) (φ (σ 0) + j) (by omega)
  simp [p] at h_j_min
  specialize h_j_min (by omega) (by omega)
  simp [-extract_eq_drop_take, extract_FinSubseq2' (le_of_lt h_j2), h3, h_j_min]

/-- If the language accepted by `M` is of the form `V∗`, then `V^ω = V∗ * (M.ChouekaLang acc)↗ω`.
Note that this theorem does need to assume that `M` is finite-state.
-/
theorem choueka_lang_omega_power_eq_omega_limit [Inhabited A]
    {M : DA A} [Finite M.State] {acc : Set M.State}
    {V : Set (List A)} (h_lang : M.toNA.AcceptedLang acc = V∗) :
    V^ω = V∗ * (M.ChouekaLang acc)↗ω := by
  apply Subset.antisymm
  · apply choueka_lang_omega_power_subset_omega_limit h_lang
  · have h1 : (M.ChouekaLang acc)↗ω ⊆ (V∗)^ω := by
      rw [← h_lang] ; apply choueka_lang_omega_limit_subset_omega_power
    have h2 : V∗ * (M.ChouekaLang acc)↗ω ⊆ V∗ * (V∗)^ω := by
      exact ConcatInf_mono (by simp) h1
    rw [IterOmega_IterStar, ConcatInf_IterStar_IterOmega] at h2
    exact h2

/-- The following lemmas are used to prove that the Choueka language is regular.
-/
lemma choueka_lang_decomp_lemma {M : DA A} {acc : Set M.State} :
    M.ChouekaLang acc =
    ⋃ s ∈ acc, { al | al ≠ [] ∧ M.RunOn al = s } *
      ( { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } ∩
        ( { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } * {[]}ᶜ )ᶜ ) := by
  ext al ; simp [DA.ChouekaLang, -extract_eq_drop_take] ; constructor
  · rintro ⟨m, h_m0, h_m1, h_acc, h_run, h_run'⟩
    use (M.RunOn (al.extract 0 m)) ; simp [h_acc, -extract_eq_drop_take]
    use (al.extract 0 m), (al.extract m al.length)
    have h1 := length_pos_iff.mp (show 0 < al.length by omega)
    have h2 : al.extract 0 m ++ al.extract m = al := by
      ext k a ; rcases (show k < m ∨ ¬ k < m by omega) with h_k | h_k <;>
        simp (disch := omega) [getElem?_append, getElem?_take, h_k] ; grind
    simp [-extract_eq_drop_take, h_m1, h1, h2,
      (show ¬ m = 0 by omega), (show ¬ al.length - m = 0 by omega)]
    constructor
    · simpa [-extract_eq_drop_take, DA.RunOn, ← da_run_from_on_append, h2]
    · rintro ⟨al1, al2, ⟨h_al1, h_run1⟩, h_al2, h_alm⟩
      have := length_pos_iff.mpr h_al1
      have := length_pos_iff.mpr h_al2
      have : m + al1.length + al2.length = al.length := by
        rw [← h2, ← h_alm] ; simp [length_append, add_assoc] ; omega
      simp [-extract_eq_drop_take, DA.RunOn, ← da_run_from_on_append] at h_run1
      specialize h_run' (m + al1.length) (by omega) (by omega)
      have h3 : al.extract m (m + al1.length) = al1 := by
        rw [← h2, ← h_alm] ; ext k a
        rcases (show k < al1.length ∨ ¬ k < al1.length by omega) with h_k | h_k <;>
          simp [getElem?_append, getElem?_drop, h_k]
        simp [(show m + k - min m al.length = k by omega), h_k]
      have h4 : al.extract 0 (m + al1.length) = al.extract 0 m ++ al1 := by
        rw [← h2, ← h_alm] ; ext k a
        rcases (show k < m ∨ (¬ k < m ∧ k < m + al1.length) ∨ ¬ k < m + al1.length by omega) with h_k | h_k | h_k <;>
          simp (disch := omega) [getElem?_append, getElem?_take, h_k]
        · simp [(show k - m < al1.length by omega)]
        · simp [(show ¬ k < m by omega)]
      rw [DA.RunOn, h3, h4] at h_run'
      contradiction
  · rintro ⟨s, h_al1_acc, al1, al2, ⟨h_al1_ne, rfl⟩, ⟨⟨h_al2_ne, h_al2_run⟩, h_al2'⟩, rfl⟩
    use al1.length
    have h_al1_pos := length_pos_iff.mpr h_al1_ne
    have h_al2_pos := length_pos_iff.mpr h_al2_ne
    have h1 : (al1 ++ al2).extract 0 al1.length = al1 := by simp
    have h2 : (al1 ++ al2).extract al1.length (al1.length + al2.length) = al2 := by simp
    simp (disch := omega) [-extract_eq_drop_take, length_append, h_al1_pos, h_al2_pos, h1, h_al1_acc]
    constructor
    · simp [h2, DA.RunOn, da_run_from_on_append] ; exact h_al2_run
    intro k h_k1 h_k2 h_contra
    suffices _ : al2 ∈ {al | (al = [] → False) ∧ M.RunOn al = M.RunFromOn (M.RunOn al1) al} * {[]}ᶜ by
      contradiction
    use al2.extract 0 (k - al1.length), al2.extract (k - al1.length) al2.length
    simp [-extract_eq_drop_take, h_al2_ne, (show ¬ k - al1.length = 0 by omega),
      (show ¬al2.length - (k - al1.length) = 0 ∧ k - al1.length < al2.length by omega)]
    constructor
    · have h3 : (al1 ++ al2).extract al1.length k = al2.extract 0 (k - al1.length) := by simp
      have h4 : (al1 ++ al2).extract 0 k = al1 ++ al2.extract 0 (k - al1.length) := by simp [take_append] ; omega
      simp [-extract_eq_drop_take, h3, h4, DA.RunOn, da_run_from_on_append] at h_contra
      exact h_contra
    · ext j a
      rcases (show j < k - al1.length ∨ ¬ j < k - al1.length by omega) with h_j | h_j <;>
        simp (disch := omega) [getElem?_append, getElem?_take, getElem?_drop, h_j]
      simp [List.getElem?_eq_some_iff] ; omega

lemma choueka_lang_reg_lemma_1 [Inhabited A] {M : DA A} [Finite M.State] (s : M.State) :
    RegLang { al | M.RunOn al = s } := by
  use M.toNA, {s} ; constructor
  · simpa [DA.toNA]
  ext al ; simp [da_acc_lang_iff_run_acc]

lemma choueka_lang_reg_lemma_2 [Inhabited A] {M : DA A} [Finite M.State] (s t : M.State) :
    RegLang { al | M.RunFromOn s al = t } := by
  use (DA.mk (A := A) M.State s M.next).toNA, {t} ; constructor
  · simpa [DA.toNA]
  ext al ; simp [da_acc_lang_iff_run_acc, DA.RunOn, DA.RunFromOn]

lemma choueka_lang_reg_lemma_3 [Inhabited A] {M : DA A} [Finite M.State] (s : M.State) :
    RegLang { al | al ≠ [] ∧ M.RunOn al = s } := by
  have h1 : { al | al ≠ [] ∧ M.RunOn al = s } = {[]}ᶜ ∩ { al | M.RunOn al = s } := by grind
  rw [h1] ; apply reg_lang_inter
  · apply reg_lang_compl ; exact reg_lang_epsilon
  · apply choueka_lang_reg_lemma_1

lemma choueka_lang_reg_lemma_4 [Inhabited A] {M : DA A} [Finite M.State] (s : M.State) :
    RegLang { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } := by
  have h1 : { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } =
      {[]}ᶜ ∩ ⋃ t, { al | M.RunOn al = t } ∩ { al | M.RunFromOn s al = t } := by aesop
  rw [h1] ; apply reg_lang_inter
  · apply reg_lang_compl ; exact reg_lang_epsilon
  · rw [← biUnion_univ] ; apply reg_lang_biUnion
    intro t _ ; apply reg_lang_inter
    · apply choueka_lang_reg_lemma_1
    · apply choueka_lang_reg_lemma_2

/-- The Choueka language of a finite-state deterministic automaton is regular.
-/
theorem choueka_lang_regular [Inhabited A] {M : DA A} [Finite M.State] {acc : Set M.State} :
    RegLang (M.ChouekaLang acc) := by
  rw [choueka_lang_decomp_lemma] ; apply reg_lang_biUnion
  intro s _ ; apply reg_lang_concat
  · apply choueka_lang_reg_lemma_3
  · apply reg_lang_inter
    · apply choueka_lang_reg_lemma_4
    · apply reg_lang_compl ; apply reg_lang_concat
      · apply choueka_lang_reg_lemma_4
      · apply reg_lang_compl ; exact reg_lang_epsilon

end ChouekaLemma
