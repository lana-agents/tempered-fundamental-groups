/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeUnitBranch
import TemperedFundamentalGroups.SemistableReduction.MonomialUnique

/-!
# Node germs, symmetric form (Blueprint §10.3.8, CrossingX1)

`NodeCore P ι ϖ u v n`: the symmetric part of a node germ `P ⊆ L` with non-unit coordinates
`u v = ϖ ^ n` over a base `ι : O → P` with `𝔪_O ↦ ϖ P` (`NodeCore.of_nodeGerm`), stable under
`u ↔ v` (`NodeCore.swap`).

* `NodeCore.valuation_lt_one`: a valuation subring containing the local ring `P`, with `ϖ, u, v`
  in its maximal ideal, dominates `P`;
* `NodeCore.valuation_lt_one_of_branch`: the branch on which `u` is a unit is unique
  (`NodeUnitBranch`).
-/

open IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction

variable {L : Type*} [Field L] {O : Type*} [CommRing O]

/-- The symmetric data of a node germ with non-unit coordinates. -/
structure NodeCore (P : Subring L) (ι : O →+* L) (ϖ u v : L) (n : ℕ) : Prop where
  base_mem : ∀ o, ι o ∈ P
  ϖ_mem : ϖ ∈ P
  u_mem : u ∈ P
  v_mem : v ∈ P
  mul_eq : u * v = ϖ ^ n
  gen : ∀ z ∈ P, ∃ o : O, ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, z = ι o + ϖ * a + u * b + v * c
  base_nonunit : ∀ o : O, ¬ IsUnit o → ∃ o', ι o = ϖ * ι o'
  u_nonunit : ∀ w ∈ P, u * w ≠ 1
  v_nonunit : ∀ w ∈ P, v * w ≠ 1

namespace NodeCore

variable {P : Subring L} {ι : O →+* L} {ϖ u v : L} {n : ℕ}

theorem swap (h : NodeCore P ι ϖ u v n) : NodeCore P ι ϖ v u n where
  base_mem := h.base_mem
  ϖ_mem := h.ϖ_mem
  u_mem := h.v_mem
  v_mem := h.u_mem
  mul_eq := by rw [mul_comm]; exact h.mul_eq
  gen z hz := by
    obtain ⟨o, a, ha, b, hb, c, hc, rfl⟩ := h.gen z hz
    exact ⟨o, a, ha, c, hc, b, hb, by ring⟩
  base_nonunit := h.base_nonunit
  u_nonunit := h.v_nonunit
  v_nonunit := h.u_nonunit

lemma one_le (h : NodeCore P ι ϖ u v n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (by rw [h.mul_eq, pow_zero]) (h.u_nonunit v h.v_mem)
  · exact hn

lemma ϖ_nonunit (h : NodeCore P ι ϖ u v n) : ∀ w ∈ P, ϖ * w ≠ 1 := by
  intro w hw h1
  apply h.u_nonunit (v * w ^ n) (mul_mem h.v_mem (pow_mem hw _))
  calc u * (v * w ^ n) = (u * v) * w ^ n := by ring
    _ = 1 := by rw [h.mul_eq, ← mul_pow, h1, one_pow]

/-- **Domination of a local node germ.** -/
theorem valuation_lt_one (h : NodeCore P ι ϖ u v n) [IsLocalRing P] {W : ValuationSubring L}
    (hW : P ≤ W.toSubring) (hϖW : W.valuation ϖ < 1) (huW : W.valuation u < 1)
    (hvW : W.valuation v < 1) {f : L} (hf : f ∈ P) (hf1 : ∀ w ∈ P, f * w ≠ 1) :
    W.valuation f < 1 := by
  have hle : ∀ p ∈ P, W.valuation p ≤ 1 := fun p hp ↦ (W.valuation_le_one_iff _).2 (hW hp)
  have hmax : ∀ p (hp : p ∈ P), (∀ w ∈ P, p * w ≠ 1) → (⟨p, hp⟩ : P) ∈ maximalIdeal P :=
    fun p hp h1 hu ↦ by
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      exact h1 w w.2 (congrArg Subtype.val hw)
  obtain ⟨o, a, ha, b, hb, c, hc, rfl⟩ := h.gen f hf
  have hrest : W.valuation (ϖ * a + u * b + v * c) < 1 := by
    refine lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt (lt_of_le_of_lt
      (W.valuation.map_add _ _) (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
    · exact (mul_le_of_le_one_right' (hle a ha)).trans_lt hϖW
    · exact (mul_le_of_le_one_right' (hle b hb)).trans_lt huW
    · exact (mul_le_of_le_one_right' (hle c hc)).trans_lt hvW
  have hrP : ϖ * a + u * b + v * c ∈ P :=
    add_mem (add_mem (mul_mem h.ϖ_mem ha) (mul_mem h.u_mem hb)) (mul_mem h.v_mem hc)
  have ho : ¬ IsUnit o := by
    intro hou
    have hrm : (⟨_, hrP⟩ : P) ∈ maximalIdeal P := by
      have h1 := Ideal.mul_mem_right (⟨a, ha⟩ : P) _ (hmax _ h.ϖ_mem h.ϖ_nonunit)
      have h2 := Ideal.mul_mem_right (⟨b, hb⟩ : P) _ (hmax _ h.u_mem h.u_nonunit)
      have h3 := Ideal.mul_mem_right (⟨c, hc⟩ : P) _ (hmax _ h.v_mem h.v_nonunit)
      exact add_mem (add_mem h1 h2) h3
    have := sub_mem (hmax _ hf hf1) hrm
    have e : (⟨_, hf⟩ : P) - ⟨_, hrP⟩ = ⟨_, h.base_mem o⟩ := by
      apply Subtype.ext; change _ - _ = _; ring
    rw [e] at this
    apply this
    obtain ⟨w, hw⟩ := hou.exists_right_inv
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h.base_mem w⟩, by
      apply Subtype.ext; change ι o * ι w = 1; rw [← map_mul, hw, map_one]⟩
  obtain ⟨o', ho'⟩ := h.base_nonunit o ho
  have hoW : W.valuation (ι o) < 1 := by
    rw [ho', map_mul, mul_comm]
    exact (mul_le_of_le_one_left' (hle _ (h.base_mem o'))).trans_lt hϖW
  rw [show ι o + ϖ * a + u * b + v * c = ι o + (ϖ * a + u * b + v * c) by ring]
  exact lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt hoW hrest)

/-- **The branch on which `u` is a unit is unique.** -/
theorem valuation_lt_one_of_branch (h : NodeCore P ι ϖ u v n) [IsLocalRing P]
    [IsNoetherianRing P] {W₁ W₂ : ValuationSubring L} (h₁ : P ≤ W₁.toSubring)
    (h₂ : P ≤ W₂.toSubring) (hϖ₁ : W₁.valuation ϖ < 1) (hv₁ : W₁.valuation v < 1)
    (hu₁ : W₁.valuation u = 1) (hϖ₂ : W₂.valuation ϖ < 1) (hv₂ : W₂.valuation v < 1)
    {f : L} (hf : f ∈ P) (hf₁ : W₁.valuation f < 1) : W₂.valuation f < 1 :=
  NodeUnitBranch.valuation_lt_one_of_branch P ι ϖ u v h.base_mem h.base_nonunit h.gen h.u_mem
    h.u_nonunit h.ϖ_mem h.v_mem h₁ h₂ hϖ₁ hv₁ hu₁ hϖ₂ hv₂ hf hf₁

end NodeCore

/-- **Node germs give node cores.** -/
theorem NodeCore.of_nodeGerm {K : Type*} [Field K] [Algebra K L] {O : ValuationSubring K}
    [IsDiscreteValuationRing O] {ϖ : O} {P : Subring L} {u v : L} {n : ℕ}
    (h : _root_.SemistableReduction.NodeGerm O ϖ P u v n) (hϖ : Irreducible ϖ)
    (hu : ∀ w ∈ P, u * w ≠ 1) (hv : ∀ w ∈ P, v * w ≠ 1) :
    NodeCore P ((algebraMap K L).comp O.subtype) (algebraMap K L (ϖ : K)) u v n where
  base_mem o := h.algebraMap_mem o
  ϖ_mem := h.algebraMap_mem ϖ
  u_mem := h.u_mem
  v_mem := h.v_mem
  mul_eq := h.mul_eq
  gen := h.gen
  base_nonunit o ho := by
    have : o ∈ Ideal.span {ϖ} := by
      rw [← hϖ.maximalIdeal_eq]; exact ho
    obtain ⟨o', rfl⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨o', by simp [mul_comm]⟩
  u_nonunit := hu
  v_nonunit := hv

end TemperedFundamentalGroups.SemistableReduction
