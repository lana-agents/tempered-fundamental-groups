/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ResidueCurve

/-!
# The chart at infinity

Blueprint §9.5, G6.5. The automorphism `σ : X ↦ X⁻¹` of `C(X)` preserves the Gauss valuation
`w_{0,1}` (`gauss1_invX`). Twisting the `C(X)`-algebra structure of `F` by `σ`
(`GaussFibre.twist`) replaces `x` by `x⁻¹` and does not change the extensions of the Gauss
valuation (`extTwistEquiv`), so the results of the chart at `0` apply at `∞`
(`red_mem_of_isIntegral_inv`).
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal nonZeroDivisors

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

section InvX

omit [IsUltrametricDist C] in
/-- `P(X⁻¹) = rev(P)(X) · X^{-deg P}`. -/
lemma aeval_X_inv (P : C[X]) :
    aeval (RatFunc.X : RatFunc C)⁻¹ P =
      algebraMap C[X] (RatFunc C) P.reverse * (RatFunc.X : RatFunc C)⁻¹ ^ P.natDegree := by
  have hX : (RatFunc.X : RatFunc C)⁻¹ ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  letI : Invertible (RatFunc.X : RatFunc C)⁻¹ := invertibleOfNonzero hX
  have h := eval₂_reverse_mul_pow (algebraMap C (RatFunc C)) (RatFunc.X : RatFunc C)⁻¹ P
  rw [invOf_eq_inv, inv_inv] at h
  rw [aeval_def, ← h, ← aeval_def, RatFunc.aeval_X_left_eq_algebraMap]

omit [IsUltrametricDist C] in
lemma transcendental_X_inv : Transcendental C (RatFunc.X : RatFunc C)⁻¹ := by
  rintro ⟨P, hP, h⟩
  rw [aeval_X_inv, mul_eq_zero, pow_eq_zero_iff', inv_eq_zero] at h
  rcases h with h | ⟨h, -⟩
  · rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), reverse_eq_zero] at h
    exact hP h
  · exact RatFunc.X_ne_zero h

omit [IsUltrametricDist C] in
lemma nonZeroDivisors_le_comap_aeval_X_inv :
    C[X]⁰ ≤ (RatFunc C)⁰.comap (aeval (RatFunc.X : RatFunc C)⁻¹ : C[X] →ₐ[C] RatFunc C) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.1 transcendental_X_inv)

variable (C) in
/-- The `C`-algebra endomorphism `X ↦ X⁻¹` of `C(X)`. -/
noncomputable def invXHom : RatFunc C →ₐ[C] RatFunc C :=
  RatFunc.liftAlgHom (aeval (RatFunc.X : RatFunc C)⁻¹) nonZeroDivisors_le_comap_aeval_X_inv

omit [IsUltrametricDist C] in
lemma invXHom_algebraMap (P : C[X]) :
    invXHom C (algebraMap C[X] (RatFunc C) P) = aeval (RatFunc.X : RatFunc C)⁻¹ P := by
  have := RatFunc.liftAlgHom_apply_div (aeval (RatFunc.X : RatFunc C)⁻¹)
    nonZeroDivisors_le_comap_aeval_X_inv P 1
  simpa [invXHom] using this

omit [IsUltrametricDist C] in
lemma invXHom_X : invXHom C RatFunc.X = (RatFunc.X : RatFunc C)⁻¹ := by
  conv_lhs => rw [← RatFunc.algebraMap_X]
  rw [invXHom_algebraMap, aeval_X]

omit [IsUltrametricDist C] in
lemma invXHom_invXHom (φ : RatFunc C) : invXHom C (invXHom C φ) = φ := by
  have hpol (P : C[X]) : invXHom C (invXHom C (algebraMap C[X] (RatFunc C) P)) =
      algebraMap C[X] (RatFunc C) P := by
    rw [invXHom_algebraMap, ← aeval_algHom_apply, map_inv₀, invXHom_X, inv_inv,
      RatFunc.aeval_X_left_eq_algebraMap]
  rw [← RatFunc.num_div_denom φ, map_div₀, map_div₀, hpol, hpol]

variable (C) in
/-- The involution `σ : X ↦ X⁻¹` of `C(X)`. -/
noncomputable def invX : RatFunc C ≃ₐ[C] RatFunc C :=
  AlgEquiv.ofAlgHom (invXHom C) (invXHom C) (AlgHom.ext invXHom_invXHom)
    (AlgHom.ext invXHom_invXHom)

omit [IsUltrametricDist C] in
@[simp]
lemma invX_apply (φ : RatFunc C) : invX C φ = invXHom C φ := rfl

/-- The Gauss norm of the reverse polynomial. -/
lemma sup_reverse (P : C[X]) :
    Gauss.sup (NormedField.valuation (K := C)) 1 P.reverse =
      Gauss.sup (NormedField.valuation (K := C)) 1 P := by
  refine le_antisymm (Gauss.sup_le_iff.2 fun i ↦ ?_) (Gauss.sup_le_iff.2 fun i ↦ ?_)
  · have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) P
      (revAt P.natDegree i)
    simpa [Gauss.term, coeff_reverse] using this
  · have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) P.reverse
      (revAt P.natDegree i)
    simpa [Gauss.term, coeff_reverse, revAt_invol] using this

lemma gauss1_aeval_X_inv (P : C[X]) :
    gauss1 C (aeval (RatFunc.X : RatFunc C)⁻¹ P) =
      Gauss.sup (NormedField.valuation (K := C)) 1 P := by
  rw [aeval_X_inv, map_mul, map_pow, map_inv₀, gauss1_X, inv_one, one_pow, mul_one,
    gauss1_algebraMap, sup_reverse]

/-- `σ` preserves the Gauss valuation. -/
lemma gauss1_invX (φ : RatFunc C) : gauss1 C (invX C φ) = gauss1 C φ := by
  rw [invX_apply, ← RatFunc.num_div_denom φ, map_div₀, map_div₀, invXHom_algebraMap,
    invXHom_algebraMap, gauss1_aeval_X_inv, gauss1_aeval_X_inv, map_div₀, gauss1_algebraMap,
    gauss1_algebraMap]

end InvX

section Infinity

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [IsUltrametricDist C] in
lemma algebraMap_aeval_X_inv (Q : C[X]) :
    algebraMap (RatFunc C) F (aeval (RatFunc.X : RatFunc C)⁻¹ Q) = aeval (xF C F)⁻¹ Q := by
  rw [← IsScalarTower.coe_toAlgHom' C (RatFunc C) F, ← aeval_algHom_apply, map_inv₀,
    IsScalarTower.coe_toAlgHom']

omit [IsUltrametricDist C] in
lemma invX_aeval_X_inv (Q : C[X]) :
    invX C (aeval (RatFunc.X : RatFunc C)⁻¹ Q) = algebraMap C[X] (RatFunc C) Q := by
  rw [invX_apply, ← aeval_algHom_apply, map_inv₀, invXHom_X, inv_inv,
    RatFunc.aeval_X_left_eq_algebraMap]

variable [FiniteDimensional (RatFunc C) F]

omit [IsUltrametricDist C] in
/-- If `f` is integral over `C[x⁻¹]`, the coefficients of its minimal polynomial over `C(X)`
are polynomials in `X⁻¹`. -/
lemma exists_minpoly_coeff_eq_inv {f : F}
    (hint : IsIntegral (Algebra.adjoin C {(xF C F)⁻¹}) f) (n : ℕ) :
    ∃ Q : C[X], aeval (RatFunc.X : RatFunc C)⁻¹ Q = (minpoly (RatFunc C) f).coeff n := by
  obtain ⟨P, hPm, hP⟩ := exists_monic_of_isIntegral hint
  set ψ : C[X] →+* RatFunc C :=
    (aeval (RatFunc.X : RatFunc C)⁻¹ : C[X] →ₐ[C] RatFunc C).toRingHom
  have hdvd : minpoly (RatFunc C) f ∣ P.map ψ := by
    refine minpoly.dvd (RatFunc C) f ?_
    have hmap : P.map (aeval (xF C F)⁻¹ : C[X] →ₐ[C] F).toRingHom =
        (P.map ψ).map (algebraMap (RatFunc C) F) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext fun Q ↦ (algebraMap_aeval_X_inv Q).symm
    rw [← hP, hmap]
    exact (aeval_map_algebraMap F f _).symm
  have hσ : (P.map ψ).map (invX C).toRingEquiv.toRingHom =
      P.map (algebraMap C[X] (RatFunc C)) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun Q ↦ invX_aeval_X_inv Q
  have hdvd' := Polynomial.map_dvd (invX C).toRingEquiv.toRingHom hdvd
  rw [hσ] at hdvd'
  have hmon := (minpoly.monic (Algebra.IsIntegral.isIntegral (R := RatFunc C) f)).map
    (invX C).toRingEquiv.toRingHom
  have := Polynomial.isIntegral_coeff_of_dvd _ _ hPm hmon hdvd' n
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  refine ⟨Q, ?_⟩
  rw [coeff_map] at hQ
  have h2 : (invX C).toRingEquiv.toRingHom ((minpoly (RatFunc C) f).coeff n) =
      invXHom C ((minpoly (RatFunc C) f).coeff n) := rfl
  have := congrArg (invXHom C) hQ
  rw [h2, invXHom_invXHom, invXHom_algebraMap] at this
  exact this

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
lemma valuation_xF_inv (w : Ext C F) : w.1 (xF C F)⁻¹ = 1 := by
  rw [map_inv₀, valuation_xF, inv_one]

/-- **G6.5** (chart at `∞`). If `f ∈ F` is integral over `C[x⁻¹]` with `‖f‖ ≤ 1` (and `F` has an
orthonormal `C(X)`-basis), then `f̄ ∈ κ(w)` lies in every valuation ring of `κ(w)` containing
`k` and `x̄⁻¹`. -/
theorem red_mem_of_isIntegral_inv [Fintype (Ext C F)] {ι : Type*} [Fintype ι]
    {b : Module.Basis ι (RatFunc C) F}
    (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
    {f : F} (hf : gnorm C f ≤ 1) (hint : IsIntegral (Algebra.adjoin C {(xF C F)⁻¹}) f)
    (w : Ext C F) (V : ValuationSubring (ResidueField w.1.valuationSubring))
    (hk : ∀ c : 𝓀, algebraMap 𝓀 _ c ∈ V) (hx : red C (xF C F)⁻¹ w ∈ V) :
    red C f w ∈ V := by
  have hfw : w.1 f ≤ 1 := (le_gnorm w f).trans hf
  refine red_mem_of_root hfw (minpoly.monic (Algebra.IsIntegral.isIntegral f))
    (minpoly.aeval _ f) (gauss1_minpoly_coeff_le hb hf) V fun n ↦ ?_
  obtain ⟨Q, hQ⟩ := exists_minpoly_coeff_eq_inv hint n
  have hQ1 : Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1 := by
    rw [← gauss1_aeval_X_inv, hQ]
    exact gauss1_minpoly_coeff_le hb hf n
  rw [← hQ, algebraMap_aeval_X_inv]
  exact red_aeval_mem (valuation_xF_inv w).le hQ1 V hk hx

end Infinity

end GaussFibre

end SemistableReduction
