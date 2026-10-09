/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiModel

/-!
# Functions with a zero have transcendental residue

`isResidueTranscendental_of_lt_one`: if `g` is a unit of `W` (a function on a component) and
`g ∈ 𝔪_R` for some valuation subring `R ≤ W` containing the base (`g` vanishes at a point of the
component), then the residue of `g` is transcendental over the residue field of the base: an
algebraic non-zero residue would be invertible in `κ(O)[ḡ]`, so `g q(g) ≡ 1` for a polynomial `q`
with integral coefficients, which is impossible in `𝔪_R`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {O : ValuationSubring K}
  {W : ValuationSubring F}

/-- **A function with a zero has transcendental residue.** -/
theorem isResidueTranscendental_of_lt_one (hW : W.comap (algebraMap K F) = O) {g : F}
    (hg : g ∈ W) (hg1 : W.valuation g = 1) {R : ValuationSubring F} (hRW : R ≤ W)
    (hRO : ∀ o : O, algebraMap K F (o : K) ∈ R) (hR : R.valuation g < 1) :
    IsResidueTranscendental O W g := by
  rw [isResidueTranscendental_iff hW hg]
  letI := residueAlgebra hW
  intro halg
  set gb := residue W ⟨g, hg⟩
  have hgb0 : gb ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact (W.valuation_eq_one_iff _).2 hg1
  have hint : IsIntegral (ResidueField O) gb := halg.isIntegral
  have hinv := hint.inv_mem_adjoin
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hinv
  obtain ⟨q, hq⟩ := hinv
  obtain ⟨Q, rfl⟩ := map_surjective _ (residue_surjective (R := O)) q
  set z := eval₂ (toVal hW) ⟨g, hg⟩ Q
  have hz : residue W z = gb⁻¹ := by
    rw [← aeval_residue hW hg Q]; exact hq
  have hm : (⟨g, hg⟩ : W) * z - 1 ∈ maximalIdeal W := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, map_one, hz, mul_inv_cancel₀ hgb0, sub_self]
  have hm' : W.valuation (g * (z : F) - 1) < 1 := (W.valuation_lt_one_iff _).1 hm
  have hgR : g ∈ R := (R.valuation_le_one_iff _).1 hR.le
  have hzR : (z : F) ∈ R := by
    rw [coe_eval₂_toVal hW hg Q, aeval_eq_sum_range]
    refine sum_mem fun i _ ↦ ?_
    rw [Algebra.smul_def, coeff_map]
    exact mul_mem (hRO _) (pow_mem hgR _)
  have h1 : R.valuation (g * z) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' ((R.valuation_le_one_iff _).2 hzR)).trans_lt hR
  have h2 : R.valuation (g * z - 1) < 1 := by
    by_contra h
    have h' : 1 ≤ R.valuation (g * z - 1) := not_lt.1 h
    have hne : g * (z : F) - 1 ≠ 0 := fun h0 ↦ by
      rw [h0, map_zero] at h'; exact absurd h' (by simp)
    have hinvR : (g * (z : F) - 1)⁻¹ ∈ R := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ h'
    have hinvW := hRW hinvR
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀] at hinvW
    have hpos : 0 < W.valuation (g * (z : F) - 1) := zero_lt_iff.2 (by simpa using hne)
    have := (inv_le_one₀ hpos).1 hinvW
    exact absurd hm' (not_lt.2 this)
  have : R.valuation (1 : F) < 1 := by
    have e : (1 : F) = g * z - (g * z - 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (R.valuation.map_sub _ _) (max_lt h1 h2)
  rw [map_one] at this
  exact lt_irrefl _ this

end SemistableReduction
