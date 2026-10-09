/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.VertexDescent
import TemperedFundamentalGroups.Setup.DVRNorm

/-!
# Unique extension over a complete DVR (Blueprint §10.3.8, CrossingX1)

`eq_of_comap_eq_dvr`: over a complete discretely valued `K` with valuation ring `O`, two
valuation subrings of an algebraic extension lying over `O` coincide
(`eq_of_comap_eq_of_completeSpace` for the norm of `O`, `DVRNorm`).
-/

open IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingAux

/-- **Unique extension over a complete DVR.** -/
theorem eq_of_comap_eq_dvr {K : Type*} [Field K] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {K' : Type*} [Field K']
    [Algebra K K'] [Algebra.IsAlgebraic K K'] {V₁ V₂ : ValuationSubring K'}
    (h₁ : V₁.comap (algebraMap K K') = O) (h₂ : V₂.comap (algebraMap K K') = O) : V₁ = V₂ := by
  letI := DVRNorm.normedField O
  haveI := DVRNorm.isUltrametricDist O
  haveI := DVRNorm.completeSpace O
  have hO : (NormedField.valuation (K := K)).valuationSubring = O := by
    ext x
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
    exact DVRNorm.norm_le_one_iff O x
  exact _root_.SemistableReduction.eq_of_comap_eq_of_completeSpace (h₁.trans hO.symm)
    (h₂.trans hO.symm)

end TemperedFundamentalGroups.SemistableReduction.CrossingAux
