/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Apply
import TemperedFundamentalGroups.SemistableReduction.DefinedOverDVR

/-!
# Function fields over `K̄` are defined over complete discretely valued subfields

Blueprint §9.7a (the hypothesis `DefinedOverDVR` of W7). For a complete discretely valued `K` of
characteristic `0` and `C = K̄` with the spectral norm:

* `isCompleteDVRSubfield_of_finiteDimensional`: every finite extension `E ⊆ C` of `K` is a
  complete discretely valued subfield (`W10Apply`: `O_E` is a DVR, `E` is complete);
* `definedOverDVR`: every finite separable `F' / C(x)` is `DefinedOverDVR` (with `K` itself as the
  base, exhausted by the finite extensions `K(T)`; `DefinedOverDVR.of_finite`).
-/

universe u

open IsLocalRing

namespace SemistableReduction

namespace W10DefinedOver

open TemperedFundamentalGroups

variable {K : Type u} [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

theorem isCompleteDVRSubfield_of_finiteDimensional (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] :
    letI := DVRNorm.normedFieldAlgCl O; haveI := DVRNorm.isUltrametricDist_algCl O
    IsCompleteDVRSubfield E.toSubfield := by
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  refine ⟨?_, ?_⟩
  · exact W10Apply.isDiscreteValuationRing_OE O E
  · letI := W10Apply.normedFieldE O E
    haveI := W10Apply.completeSpace_E O E
    exact completeSpace_coe_iff_isComplete.1 ‹CompleteSpace E›

omit [CharZero K] in
lemma closure_bot_union (S : Set (AlgebraicClosure K)) :
    Subfield.closure (((⊥ : IntermediateField K (AlgebraicClosure K)).toSubfield :
      Set (AlgebraicClosure K)) ∪ S) =
      (IntermediateField.adjoin K S).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield]
  congr 2

/-- **Every finite separable `F' / K̄(x)` is defined over a complete discretely valued
subfield.** -/
theorem definedOverDVR (F' : Type*) [Field F'] [Algebra (RatFunc (AlgebraicClosure K)) F']
    [FiniteDimensional (RatFunc (AlgebraicClosure K)) F']
    [Algebra.IsSeparable (RatFunc (AlgebraicClosure K)) F'] :
    letI := DVRNorm.normedFieldAlgCl O; haveI := DVRNorm.isUltrametricDist_algCl O
    DefinedOverDVR (AlgebraicClosure K) F' := by
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  refine DefinedOverDVR.of_finite (F' := RatFunc (AlgebraicClosure K)) ?_ F'
  set K₀ := (⊥ : IntermediateField K (AlgebraicClosure K)).toSubfield
  refine ⟨K₀, isCompleteDVRSubfield_of_finiteDimensional O ⊥, ?_, fun S ↦ ⟨S, fun s hs ↦ ?_, ?_⟩,
    RatFunc.X, ?_, fun i ↦ ?_⟩
  · exact Algebra.IsAlgebraic.tower_top (K := K) (⊥ : IntermediateField K (AlgebraicClosure K))
  · rw [closure_bot_union]
    exact IntermediateField.subset_adjoin K _ hs
  · rw [closure_bot_union]
    haveI : FiniteDimensional K (IntermediateField.adjoin K (S : Set (AlgebraicClosure K))) :=
      IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
    exact isCompleteDVRSubfield_of_finiteDimensional O _
  · exact eq_top_iff.2 fun y _ ↦ by
      rw [← Algebra.algebraMap_self_apply y]
      exact Subalgebra.algebraMap_mem _ y
  · rw [minpoly.eq_X_sub_C' (RatFunc.X : RatFunc (AlgebraicClosure K))]
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · refine ⟨-RatFunc.X, ?_⟩
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
          map_neg, ← RatFunc.algebraMap_X, ratFuncMap_algebraMap, Polynomial.map_X,
          RatFunc.algebraMap_X]
      · exact ⟨1, by simp⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [Polynomial.natDegree_X_sub_C]; omega)]
      exact zero_mem _

end W10DefinedOver

end SemistableReduction
