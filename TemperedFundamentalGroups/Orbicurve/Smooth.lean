/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Orbicurve.GeomModel

/-!
# The orbicurve ring is a smooth affine curve

For an elliptic curve `W` over a field `k`:

* `Orbicurve.smooth_coordinateRing`: the affine coordinate ring `k[W] = k[X, Y] ⧸ (F)` is smooth
  over `k`. Proof by the Jacobian criterion in the form of
  `Algebra.Extension.formallySmooth_iff_split_injection` (`formallySmooth_of_derivation`):
  `F, F_X, F_Y` generate the unit ideal of `k[X, Y]` (`exists_eq_one_polynomialX_polynomialY`,
  from the nonsingularity of `W` over `k̄` and the
  Nullstellensatz), so with `a F_X + b F_Y + e F = 1` the derivation `D = a ∂_X + b ∂_Y` has
  `D F ≡ 1 mod F`, and `ω ↦ D(ω) · [F]` splits the conormal sequence `(F)/(F²) → k[W] ⊗ Ω`.
* `Orbicurve.smooth_ringAway`, `Orbicurve.ringKrullDim_ringAway`: if `𝒮 ∖ {0}` is the zero set of
  `0 ≠ D ∈ k[W]`, the ring `ringAway W 𝒮 = k[W][D⁻¹]` is smooth over `k` and of Krull dimension `1`;
  it is a domain, being a subring of the function field.
* `Orbicurve.smooth_geomOrbicurveRing`, `Orbicurve.ringKrullDim_geomOrbicurveRing` (and the
  `_of_charZero` forms, `1 ≤ ℓ`, `M` finite): the same for IUT's `geomOrbicurveRing W ℓ M`, the
  coordinate ring of `E ∖ (E[ℓ] + M)`, when `E[ℓ] + M` is finite.
-/

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TemperedFundamentalGroups.Orbicurve

/-- **Jacobian criterion for a hypersurface.** Let `P → S` be an extension with `P` formally
smooth and kernel `(F)`. If some derivation `D` of `P` has `D F ≡ 1 mod F`, then `S` is formally
smooth: `ω ↦ D(ω) · [F]` is a retraction of the conormal map `(F)/(F²) → S ⊗ Ω[P]`. -/
theorem formallySmooth_of_derivation {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) [Algebra.FormallySmooth R P.Ring] (F : P.Ring)
    (hker : P.ker = Ideal.span {F}) (D : Derivation R P.Ring P.Ring) (e : P.Ring)
    (hD : D F = 1 + e * F) : Algebra.FormallySmooth R S := by
  have hF : F ∈ P.ker := by rw [hker]; exact Ideal.subset_span rfl
  set c : P.Cotangent := Algebra.Extension.Cotangent.mk ⟨F, hF⟩
  let δ : Derivation R P.Ring P.Cotangent :=
    (LinearMap.toSpanSingleton P.Ring P.Cotangent c).compDer D
  let l : P.CotangentSpace →ₗ[S] P.Cotangent :=
    (δ.liftKaehlerDifferential).liftBaseChange S
  rw [P.formallySmooth_iff_split_injection]
  refine ⟨l, LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  obtain ⟨x, hx⟩ := x
  have hx' := hx
  rw [hker, Ideal.mem_span_singleton'] at hx'
  obtain ⟨h, rfl⟩ := hx'
  rw [LinearMap.comp_apply, Algebra.Extension.cotangentComplex_mk]
  simp only [l, LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  have hFm : ∀ m : P.Cotangent, F • m = 0 := fun m ↦ Algebra.Extension.Cotangent.ext (by
    rw [Algebra.Extension.Cotangent.val_smul', Algebra.Extension.Cotangent.val_zero]
    exact Algebra.Extension.Cotangent.smul_eq_zero_of_mem F hF _)
  have hδF : δ F = c := by
    change D F • c = c
    rw [hD, add_smul, one_smul, mul_smul, hFm, smul_zero, add_zero]
  rw [LinearMap.id_apply, Derivation.leibniz, hδF, hFm, add_zero]
  change _ = Algebra.Extension.Cotangent.mk (h • (⟨F, hF⟩ : P.ker))
  rw [map_smul]

noncomputable section

variable {k : Type u} [Field k]

/-- The partial derivative `∂_X` on `k[X][Y]` (differentiating the coefficients). -/
def derivX : Derivation k k[X][X] k[X][X] :=
  (PolynomialModule.equivPolynomialSelf (R := k[X])).toLinearMap.compDer
    (Polynomial.derivative' : Derivation k k[X] k[X]).mapCoeffs

/-- The partial derivative `∂_Y` on `k[X][Y]`. -/
def derivY : Derivation k k[X][X] k[X][X] :=
  (Polynomial.derivative' : Derivation k[X] k[X][X] k[X][X]).restrictScalars k

lemma derivX_C (p : k[X]) : derivX (C p) = C (derivative p) := by
  simp [derivX]

lemma derivX_X : derivX (X : k[X][X]) = 0 := by
  simp [derivX]

lemma derivY_C (p : k[X]) : derivY (C p) = 0 := by
  simp [derivY]

lemma derivY_X : derivY (X : k[X][X]) = 1 := by
  simp [derivY]

variable (W : WeierstrassCurve k)

lemma derivX_polynomial : derivX W.toAffine.polynomial = W.toAffine.polynomialX := by
  simp only [Affine.polynomial, polynomialX, map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, derivX_X, derivX_C]
  simp
  simp only [map_ofNat]
  ring

lemma derivY_polynomial : derivY W.toAffine.polynomial = W.toAffine.polynomialY := by
  simp only [Affine.polynomial, polynomialY, map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, derivY_X, derivY_C]
  simp
  simp only [map_ofNat]

lemma algHom_eq_evalEval {L : Type*} [Field L] [Algebra k L] (χ : k[X][X] →ₐ[k] L)
    (p : k[X][X]) :
    χ p = (p.map (mapRingHom (algebraMap k L))).evalEval (χ (C X)) (χ X) := by
  have : (χ : k[X][X] →+* L) = (evalEvalRingHom (χ (C X)) (χ X)).comp
      (mapRingHom (mapRingHom (algebraMap k L))) := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext ?_ ?_) ?_
    · intro a
      have h := χ.commutes a
      rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply] at h
      simp [h]
    · simp
    · simp
  exact congrArg (fun f : k[X][X] →+* L ↦ f p) this

variable [W.IsElliptic]

/-- **Nonsingularity as a unit ideal**: `F_X, F_Y, F` generate the unit ideal of `k[X, Y]`. -/
theorem exists_eq_one_polynomialX_polynomialY :
    ∃ a b e : k[X][X], a * W.toAffine.polynomialX + b * W.toAffine.polynomialY +
      e * W.toAffine.polynomial = 1 := by
  set I : Ideal k[X][X] := Ideal.span {W.toAffine.polynomialX, W.toAffine.polynomialY,
    W.toAffine.polynomial}
  suffices h : I = ⊤ by
    have h1 : (1 : k[X][X]) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, b, e, h⟩ := Submodule.mem_span_triple.mp h1
    exact ⟨a, b, e, by simpa [smul_eq_mul] using h⟩
  by_contra hI
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨χ, hχ⟩ := exists_algHom_eq_zero_iff (k := k) 𝔪
  have hz : ∀ p ∈ I, (p.map (mapRingHom (algebraMap k (AlgebraicClosure k)))).evalEval
      (χ (C X)) (χ X) = 0 := fun p hp ↦ by
    rw [← algHom_eq_evalEval]; exact (hχ p).mpr (hI𝔪 hp)
  set W' := W.toAffine.map (algebraMap k (AlgebraicClosure k))
  have heq : W'.Equation (χ (C X)) (χ X) := by
    rw [Affine.Equation, Affine.map_polynomial]
    exact hz _ (Ideal.subset_span (by simp))
  have hns := (W'.equation_iff_nonsingular).mp heq
  rw [Affine.Nonsingular, map_polynomialX, map_polynomialY] at hns
  rcases hns.2 with h | h
  · exact h (hz _ (Ideal.subset_span (by simp)))
  · exact h (hz _ (Ideal.subset_span (by simp)))

/-- The presentation `k[X][Y] → k[W]`. -/
def coordinateRingMk : k[X][X] →ₐ[k] W.toAffine.CoordinateRing :=
  Ideal.Quotient.mkₐ k (Ideal.span {W.toAffine.polynomial})

/-- **The affine coordinate ring of an elliptic curve is smooth.** -/
instance smooth_coordinateRing : Algebra.Smooth k W.toAffine.CoordinateRing := by
  refine ⟨?_, inferInstance⟩
  let P : Algebra.Extension k W.toAffine.CoordinateRing :=
    .ofSurjective (coordinateRingMk W) (Ideal.Quotient.mkₐ_surjective k _)
  haveI : Algebra.FormallySmooth k P.Ring := by
    change Algebra.FormallySmooth k k[X][X]
    exact Algebra.FormallySmooth.comp k k[X] k[X][X]
  obtain ⟨a, b, e, he⟩ := exists_eq_one_polynomialX_polynomialY W
  refine formallySmooth_of_derivation P (W.toAffine.polynomial : k[X][X])
    (Ideal.mk_ker (I := Ideal.span {W.toAffine.polynomial})) (a • derivX + b • derivY) (-e) ?_
  change a * derivX W.toAffine.polynomial + b * derivY W.toAffine.polynomial =
    (1 : k[X][X]) + -e * W.toAffine.polynomial
  rw [derivX_polynomial, derivY_polynomial]
  linear_combination he

omit [W.IsElliptic] in
/-- The coordinate ring `k[W]` is integral over `k[X]`, hence of dimension `≤ 1`. -/
lemma dimensionLEOne_coordinateRing : Ring.DimensionLEOne W.toAffine.CoordinateRing := by
  haveI : Module.Finite k[X] W.toAffine.CoordinateRing := monic_polynomial.finite_adjoinRoot
  exact Ring.DimensionLEOne.of_isIntegral (R := k[X]) W.toAffine.CoordinateRing

/-! ### Rings of functions regular away from `𝒮` -/

variable {W} {𝒮 : Set (GeomPoint W)} {D : W.toAffine.CoordinateRing}

/-- `ringAway W 𝒮` is a domain (a subring of the function field). -/
example : IsDomain (ringAway W 𝒮) := inferInstance

/-- **`ringAway W 𝒮 = k[W][D⁻¹]` is smooth over `k`.** -/
theorem smooth_ringAway (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0}) :
    Algebra.Smooth k (ringAway W 𝒮) := by
  haveI := isLocalization_away_ringAway hD h𝒮
  haveI : Algebra.Smooth W.toAffine.CoordinateRing (ringAway W 𝒮) :=
    Algebra.Smooth.of_isLocalization_Away D
  exact Algebra.Smooth.comp k W.toAffine.CoordinateRing (ringAway W 𝒮)

omit [W.IsElliptic] in
lemma injective_algebraMap_ringAway :
    Function.Injective (algebraMap W.toAffine.CoordinateRing (ringAway W 𝒮)) := fun _ _ h ↦
  injective_algebraMap_funField W (congrArg Subtype.val h)

/-- **`ringAway W 𝒮 = k[W][D⁻¹]` is not a field**: `x` is transcendental over `k`, while a field
finitely generated over `k` is finite over `k`. -/
theorem not_isField_ringAway (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0}) :
    ¬ IsField (ringAway W 𝒮) := by
  intro hF
  letI := hF.toField
  haveI := isLocalization_away_ringAway hD h𝒮
  haveI : Algebra.FiniteType W.toAffine.CoordinateRing (ringAway W 𝒮) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers D) (ringAway W 𝒮)
  haveI : Algebra.FiniteType k (ringAway W 𝒮) :=
    Algebra.FiniteType.trans (S := W.toAffine.CoordinateRing) inferInstance inferInstance
  haveI : Module.Finite k (ringAway W 𝒮) := finite_of_finite_type_of_isJacobsonRing k _
  obtain ⟨p, hp, hpr⟩ := (Algebra.IsIntegral.isIntegral (R := k)
    (algebraMap W.toAffine.CoordinateRing (ringAway W 𝒮) (xC W)))
  have hx : xC W = algebraMap k[X] W.toAffine.CoordinateRing X := rfl
  have : algebraMap k[X] W.toAffine.CoordinateRing p = 0 := by
    apply injective_algebraMap_ringAway (𝒮 := 𝒮)
    rw [map_zero, ← hpr, ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply, hx,
      Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [← map_zero (algebraMap k[X] W.toAffine.CoordinateRing)] at this
  exact hp.ne_zero (injective_algebraMap_polynomial this)

/-- **`ringAway W 𝒮 = k[W][D⁻¹]` has Krull dimension `1`.** -/
theorem ringKrullDim_ringAway (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0}) :
    ringKrullDim (ringAway W 𝒮) = 1 := by
  haveI := isLocalization_away_ringAway hD h𝒮
  haveI := dimensionLEOne_coordinateRing W
  haveI : Ring.DimensionLEOne (ringAway W 𝒮) :=
    Ring.DimensionLEOne.localization (ringAway W 𝒮) (M := Submonoid.powers D)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hD)
  apply eq_of_le_of_not_lt ?_ fun h' ↦ not_isField_ringAway hD h𝒮 ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    exact .mk₁' fun _ hI hI' ↦ hI'.isMaximal hI
  · have h'' : ringKrullDim (ringAway W 𝒮) ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

/-! ### IUT's orbicurve ring -/

variable [DecidableEq k] {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}

/-- **The coordinate ring of `E ∖ (E[ℓ] + M)` is smooth** (for `E[ℓ] + M` finite). -/
theorem smooth_geomOrbicurveRing (hfin : (geomRemovedSet W ℓ M).Finite) :
    Algebra.Smooth k (geomOrbicurveRing W ℓ M) := by
  obtain ⟨Ψ, hΨ, hz, -⟩ := exists_isLocalization_geomOrbicurveRing hfin
  exact smooth_ringAway ((_root_.map_ne_zero_iff _ injective_algebraMap_polynomial).mpr hΨ) hz

/-- **The coordinate ring of `E ∖ (E[ℓ] + M)` has Krull dimension `1`** (for `E[ℓ] + M`
finite). -/
theorem ringKrullDim_geomOrbicurveRing (hfin : (geomRemovedSet W ℓ M).Finite) :
    ringKrullDim (geomOrbicurveRing W ℓ M) = 1 := by
  obtain ⟨Ψ, hΨ, hz, -⟩ := exists_isLocalization_geomOrbicurveRing hfin
  exact ringKrullDim_ringAway
    ((_root_.map_ne_zero_iff _ injective_algebraMap_polynomial).mpr hΨ) hz

/-- The orbicurve ring is a domain (a subring of the function field; Mathlib instance). -/
example : IsDomain (geomOrbicurveRing W ℓ M) := inferInstance

/-- Smoothness of the orbicurve ring in characteristic `0` (`ℓ ≥ 1`, `M` finite). -/
theorem smooth_geomOrbicurveRing_of_charZero [CharZero k] (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) : Algebra.Smooth k (geomOrbicurveRing W ℓ M) :=
  smooth_geomOrbicurveRing (finite_geomRemovedSet_of_charZero hℓ hM)

/-- The orbicurve ring has Krull dimension `1` in characteristic `0` (`ℓ ≥ 1`, `M` finite). -/
theorem ringKrullDim_geomOrbicurveRing_of_charZero [CharZero k] (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) : ringKrullDim (geomOrbicurveRing W ℓ M) = 1 :=
  ringKrullDim_geomOrbicurveRing (finite_geomRemovedSet_of_charZero hℓ hM)

end

end TemperedFundamentalGroups.Orbicurve
