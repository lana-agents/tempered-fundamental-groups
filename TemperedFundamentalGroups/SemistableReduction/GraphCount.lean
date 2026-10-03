/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Counting independent gluing conditions along a connected graph

Blueprint §9.5, G6.7 (abstract part).

* `add_le_finrank_of_triangular`: if functionals `φ₀, …, φ_{n-1}` vanish on `W ≤ U` and vectors
  `t₀, …, t_{n-1}` satisfy `φ_l(t_l) ≠ 0` and `φ_l(t_{l'}) = 0` for `l < l'`, then
  `dim W + n ≤ dim U` (the `t_l` are independent modulo `W`);
* `exists_chain`: in a finite graph in which every nonempty proper vertex set has an edge leaving
  it (connectedness), there are `#V - 1` edges `(iₗ, jₗ)` such that `jₗ'` is not an endpoint of
  `(iₗ, jₗ)` for `l < l'` (grow a spanning tree);
* `add_card_sub_one_le_finrank`: hence, if every edge `(i, j)` carries a functional `φ_{ij}`
  vanishing on `W` and a test vector `t_{ij}` "supported at `j`", then
  `dim W + (#V - 1) ≤ dim U`.
-/

namespace SemistableReduction

namespace GraphCount

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]

/-- Triangular families of functionals and vectors give independent conditions. -/
theorem add_le_finrank_of_triangular [FiniteDimensional k U] (W : Submodule k U) (n : ℕ)
    (φ : ℕ → Module.Dual k U) (t : ℕ → U) (hW : ∀ l < n, ∀ w ∈ W, φ l w = 0)
    (hdiag : ∀ l < n, φ l (t l) ≠ 0) (htri : ∀ l l', l < l' → l' < n → φ l (t l') = 0) :
    Module.finrank k W + n ≤ Module.finrank k U := by
  classical
  have hli : LinearIndependent k fun l : Fin n ↦ W.mkQ (t l) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra! hne
    have hs : (Finset.univ.filter fun l : Fin n ↦ c l ≠ 0).Nonempty := by
      obtain ⟨l, hl⟩ := hne
      exact ⟨l, by simpa using hl⟩
    set l₀ := (Finset.univ.filter fun l : Fin n ↦ c l ≠ 0).min' hs
    have hl₀ : c l₀ ≠ 0 := (Finset.mem_filter.1 (Finset.min'_mem _ hs)).2
    have hmin (l : Fin n) (hl : l < l₀) : c l = 0 := by
      by_contra h
      exact not_lt.2 (Finset.min'_le _ l (by simpa using h)) hl
    have hmem : ∑ l, c l • t l ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      simpa using hc
    have h0 := hW l₀ l₀.2 _ hmem
    rw [map_sum, Finset.sum_eq_single l₀] at h0
    · rw [map_smul, smul_eq_mul, mul_eq_zero] at h0
      exact h0.elim hl₀ (hdiag l₀ l₀.2)
    · intro l _ hl
      rw [map_smul, smul_eq_mul]
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hmin l h, zero_mul]
      · rw [htri l₀ l h l.2, mul_zero]
    · simp
  have h1 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h1
  have h2 := Submodule.finrank_quotient_add_finrank W
  omega

variable {ι : Type*} [Fintype ι]

/-- Growing a spanning tree: `n + 1` vertices joined by `n` edges, each new edge ending at a new
vertex. -/
lemma exists_chain_aux (adj : ι → ι → Prop) (root : ι)
    (hcut : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j ∉ S, adj i j) :
    ∀ n, n < Fintype.card ι → ∃ (S : Finset ι) (e : ℕ → ι × ι), S.card = n + 1 ∧
      (∀ l < n, adj (e l).1 (e l).2 ∧ (e l).1 ∈ S ∧ (e l).2 ∈ S) ∧
      ∀ l l', l < l' → l' < n → (e l').2 ≠ (e l).1 ∧ (e l').2 ≠ (e l).2 := by
  classical
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨{root}, fun _ ↦ (root, root), by simp, by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨S, e, hS, he, htri⟩ := ih (by omega)
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hSu : S ≠ Finset.univ := by
      intro h
      rw [h, Finset.card_univ] at hS
      omega
    obtain ⟨i, hi, j, hj, hij⟩ := hcut S hSne hSu
    refine ⟨insert j S, Function.update e n (i, j), by rw [Finset.card_insert_of_notMem hj, hS],
      fun l hl ↦ ?_, fun l l' hll' hl' ↦ ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · rw [Function.update_of_ne hl.ne]
        obtain ⟨h1, h2, h3⟩ := he l hl
        exact ⟨h1, Finset.mem_insert_of_mem h2, Finset.mem_insert_of_mem h3⟩
      · simp only [Function.update_self]
        exact ⟨hij, Finset.mem_insert_of_mem hi, Finset.mem_insert_self _ _⟩
    · have hl : l < n := by omega
      rw [Function.update_of_ne hl.ne]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with hl' | rfl
      · rw [Function.update_of_ne hl'.ne]
        exact htri l l' hll' hl'
      · simp only [Function.update_self]
        obtain ⟨-, h2, h3⟩ := he l hl
        exact ⟨fun h ↦ hj (h ▸ h2), fun h ↦ hj (h ▸ h3)⟩

/-- **Independent gluing conditions along a connected graph.** -/
theorem add_card_sub_one_le_finrank [FiniteDimensional k U] (W : Submodule k U) [Nonempty ι]
    (adj : ι → ι → Prop)
    (hcut : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j ∉ S, adj i j)
    (φ : ι → ι → Module.Dual k U) (t : ι → ι → U)
    (hW : ∀ i j, adj i j → ∀ w ∈ W, φ i j w = 0) (hdiag : ∀ i j, adj i j → φ i j (t i j) ≠ 0)
    (hsupp : ∀ i j i' j', adj i j → adj i' j' → j' ≠ i → j' ≠ j → φ i j (t i' j') = 0) :
    Module.finrank k W + (Fintype.card ι - 1) ≤ Module.finrank k U := by
  obtain ⟨root⟩ := ‹Nonempty ι›
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨S, e, -, he, htri⟩ := exists_chain_aux adj root hcut (Fintype.card ι - 1) (by omega)
  refine add_le_finrank_of_triangular W _ (fun l ↦ φ (e l).1 (e l).2) (fun l ↦ t (e l).1 (e l).2)
    (fun l hl ↦ hW _ _ (he l hl).1) (fun l hl ↦ hdiag _ _ (he l hl).1)
    fun l l' hll' hl' ↦ ?_
  obtain ⟨h1, h2⟩ := htri l l' hll' hl'
  exact hsupp _ _ _ _ (he l (hll'.trans hl')).1 (he l' hl').1 h1 h2

end GraphCount

end SemistableReduction
