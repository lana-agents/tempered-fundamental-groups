/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeBranchesW
import TemperedFundamentalGroups.SemistableReduction.UnfoldedCentre
import TemperedFundamentalGroups.SemistableReduction.UnfoldedVertex
import TemperedFundamentalGroups.SemistableReduction.XLengthUnfolded
import TemperedFundamentalGroups.SemistableReduction.GaussDescent
import TemperedFundamentalGroups.SemistableReduction.TrdegOne

/-!
# Nodes of unfolded W-models are unfolded node germs (Blueprint §9.7, XL6)

`exists_unfoldedNodeGerm`: at a node `y` of an unfolded split W-model without loops, the germs
form an `UnfoldedNodeGerm` whose branch valuations are the centre valuations of the two components
through `y`: the specialization on the Gauss tree lies in the germs (`center_subset_germs`) and
in two distinct vertices (`ModelCode.IsUnfolded`), so it is the local ring of a node chart
`O[t, c' / t]` (`exists_nodeChart_of_two_vertices`) with `t`, `c' / t` non-units of the germs;
the divisor lemma gives `t = ε ϖ ^ α w ^ e` (`w` a node coordinate), and `e ≥ 1` since otherwise
`t` would have the same value `|ϖ| ^ α < 1` at both vertices.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}

/-- The node germ with the roles of the coordinates exchanged. -/
theorem NodeGerm.swap' {ϖ : O} {P : Subring L} {u v : L} {n : ℕ} (h : NodeGerm O ϖ P u v n)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K {v}) L) : NodeGerm O ϖ P v u n where
  algebraMap_mem := h.algebraMap_mem
  u_mem := h.v_mem
  v_mem := h.u_mem
  mul_eq := by rw [mul_comm]; exact h.mul_eq
  gen z hz := by
    obtain ⟨o, a, ha, b, hb, c, hc, rfl⟩ := h.gen z hz
    exact ⟨o, a, ha, c, hc, b, hb, by ring⟩
  frac := h.frac
  alg := fun _ _ hf ↦ exists_relation_of_transcendental halg hf

/-- A discrete valuation ring has rank one. -/
lemma rank_le_one (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    ∀ O' : ValuationSubring K, O.valuation.valuationSubring ≤ O' →
      O' = O.valuation.valuationSubring ∨ O' = ⊤ := by
  haveI : IsDiscreteValuationRing O.valuation.valuationSubring := by
    rw [ValuationSubring.valuationSubring_valuation]; infer_instance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O.valuation.valuationSubring
  exact eq_or_eq_top_of_le hϖ

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode _root_.SemistableReduction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
  (hW : IsWModel O L x c j) {ϖ : O} (hϖ : Irreducible ϖ)

include hW hϖ in
/-- **An unfolded node germ** from the coordinate `x - a = β ε u ^ e ϖ ^ α` (`e ≥ 1`). -/
theorem unfoldedNodeGerm_of {y : c.scheme} {P : Subring L} {u v : L} {n : ℕ}
    (hG : NodeGerm O ϖ P u v n) (hn : 1 ≤ n) (hPg : (P : Set L) = germs c j y)
    {v₁ v₂ : Set c.scheme} (hv₁ : v₁ ∈ components c) (hv₂ : v₂ ∈ components c) (hy₁ : y ∈ v₁)
    (hy₂ : y ∈ v₂)
    (HB : NodeBranches O ϖ P (algebraMap O L) u v n (Wc hW hv₁) (Wc hW hv₂)) {a β : K}
    (hβ : β ≠ 0) {e α : ℕ} {ε : L} (he : 1 ≤ e) (hε0 : ε ≠ 0) (hε : ε ∈ P) (hεi : ε⁻¹ ∈ P)
    (hcoord : x - algebraMap K L a =
      algebraMap K L β * (ε * u ^ e * algebraMap K L (ϖ : K) ^ α)) :
    UnfoldedNodeGerm O ϖ P u v n x a β e α ε (Wc hW hv₁) (Wc hW hv₂) := by
  have hy := specializes_of_isWModel hW y
  have hdom : ∀ R : ValuationSubring L, IsCentre j R y → ∀ f ∈ P, (∀ w ∈ P, f * w ≠ 1) →
      R.valuation f < 1 := fun R hR f hf hfu ↦
    ((isCentre_iff_dominates c j hy R).1 hR).2 f (hPg ▸ hf)
      (fun w hw ↦ hfu w (by rw [← SetLike.mem_coe, hPg]; exact hw))
  have hRP : ∀ R : ValuationSubring L, IsCentre j R y → ∀ f ∈ P, f ∈ R := fun R hR f hf ↦
    ((isCentre_iff_dominates c j hy R).1 hR).1 (hPg ▸ hf)
  have hϖL : algebraMap K L (ϖ : K) = algebraMap O L ϖ := algebraMap_O_K ϖ
  have hcomap : ∀ {w} (hw : w ∈ components c), (P : Set L) ⊆ Wc hW hw →
      (Wc hW hw).comap (algebraMap K L) = O := by
    intro w hw hPW
    refine comap_eq_of_lt_one hϖ (fun o ↦ hPW (HB.base o ▸ HB.core.base_mem o)) ?_
    rw [hϖL]
    exact valuation_ϖ_lt_one hW hϖ (hw.2.1 (gp_mem hw)) (Wc_spec hW hw)
  have hu1 : (Wc hW hv₁).valuation u = 1 := NodeBranches.isLogValue_zero_iff.1 HB.mono₁.2.2.1
  have hv1 : (Wc hW hv₂).valuation v = 1 := NodeBranches.isLogValue_zero_iff.1 HB.swap.mono₁.2.2.1
  have hε1 : ∀ {w} (hw : w ∈ components c), (P : Set L) ⊆ Wc hW hw →
      (Wc hW hw).valuation ε = 1 := fun hw hPW ↦
    valuation_eq_one_of_mem_of_inv_mem hε0 (hPW hε) (hPW hεi)
  have hP₁ := HB.mono₁.1
  have hP₂ := HB.mono₂.1
  have hu0 := HB.u_ne_zero
  have hv0 := HB.v_ne_zero
  refine
    { germ := hG
      one_le_n := hn
      β_ne := hβ
      one_le_e := he
      ε_ne := hε0
      ε_mem := hε
      ε_inv_mem := hεi
      coord := hcoord
      isMonomialPt₁ := HB.mono₁
      isMonomialPt₂ := HB.mono₂
      unique₁ := fun U hU ↦ HB.uniq₁ U hU.1 hU.2.1 (NodeBranches.isLogValue_zero_iff.1 hU.2.2.1)
      unique₂ := fun U hU ↦ HB.uniq₂ U hU.1 hU.2.1 (HB.valuation_v_eq (by
        rw [pow_one, zpow_natCast]; exact (NodeBranches.isLogValue_nat_iff n).1 hU.2.2.1) hu0)
      residue₁ := ?_
      residue₂ := ?_ }
  · refine residue_of_vanishing hW hϖ hv₁ hy₁ (mul_mem (hP₁ hε) (pow_mem (hP₁ HB.core.u_mem) e))
      (by rw [map_mul, map_pow, hε1 hv₁ hP₁, hu1, one_pow, one_mul]) fun R hR ↦ ?_
    rw [map_mul, map_pow]
    have hRε : R.valuation ε ≤ 1 := (R.valuation_le_one_iff _).2 (hRP R hR ε hε)
    have hRu := hdom R hR u HB.core.u_mem HB.core.u_nonunit
    exact (mul_le_of_le_one_left' hRε).trans_lt (pow_lt_one₀ zero_le hRu (by omega))
  · have e1 : ε * u ^ e / algebraMap K L (ϖ : K) ^ (e * n) = (ε⁻¹ * v ^ e)⁻¹ := by
      rw [pow_mul', ← HB.core.mul_eq, mul_pow]
      field_simp
    rw [e1]
    have hg := residue_of_vanishing hW hϖ hv₂ hy₂ (g := ε⁻¹ * v ^ e)
      (mul_mem (hP₂ hεi) (pow_mem (hP₂ HB.core.v_mem) e))
      (by rw [map_mul, map_pow, map_inv₀, hε1 hv₂ hP₂, hv1, one_pow, inv_one, one_mul])
      fun R hR ↦ by
        rw [map_mul, map_pow]
        have hRε : R.valuation ε⁻¹ ≤ 1 := (R.valuation_le_one_iff _).2 (hRP R hR _ hεi)
        have hRv := hdom R hR v HB.core.v_mem HB.core.v_nonunit
        exact (mul_le_of_le_one_left' hRε).trans_lt (pow_lt_one₀ zero_le hRv (by omega))
    refine hg.inv (hcomap hv₂ hP₂) ?_
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_mul, map_pow, map_inv₀,
      hε1 hv₂ hP₂, hv1, one_pow, inv_one, one_mul, inv_one]

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
