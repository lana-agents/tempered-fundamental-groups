/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.VertexMatch

/-!
# The inner vertex of an annulus: the inversion `x ↦ c/x`

Blueprint §9.9, W7 layer S6 (inner vertex). The inversion `σ_c : C(x) → C(x)`, `x ↦ c/x`, is an
involution of `C(x)` over `C` (`inv`), it exchanges the Gauss points `w_{0,s}` and `w_{0,|c|/s}`
(`gaussRat_inv`), preserves the node chart `O_C[x, c/x]` (`map_nodeRing`) and the open segment
`(|c|, 1)`. Twisting the `C(x)`-algebra structure of `F'` by `σ_c` (`Inv c F'`) turns the inner
vertex `w_{0,|c|}` into the outer vertex `w_{0,1}`, so `VertexMatch` applies to the inner vertex.
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

section Inversion

variable {c : C} (hc0 : c ≠ 0)

/-- `p ↦ p(c/X)`, injective since `c/X` is transcendental. -/
noncomputable def invPoly (c : C) : C[X] →ₐ[C] RatFunc C :=
  aeval (algebraMap C (RatFunc C) c / RatFunc.X)

include hc0 in
lemma invPoly_injective : Function.Injective (invPoly c) := by
  have ht : Transcendental C (algebraMap C (RatFunc C) c / RatFunc.X) := by
    intro halg
    have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
    have hX : (RatFunc.X : RatFunc C) = algebraMap C (RatFunc C) c *
        (algebraMap C (RatFunc C) c / RatFunc.X)⁻¹ := by
      rw [inv_div, mul_div_cancel₀ _ hc']
    have : IsAlgebraic C (RatFunc.X : RatFunc C) := by
      rw [hX]
      exact (isAlgebraic_algebraMap (R := C) (A := RatFunc C) c).mul halg.inv
    exact RatFunc.transcendental_X this
  exact (injective_iff_map_eq_zero _).2 fun p hp ↦ by
    by_contra h
    exact ht ⟨p, h, hp⟩

include hc0 in
/-- The inversion `x ↦ c/x` of `C(x)` as an algebra homomorphism. -/
noncomputable def invHom : RatFunc C →ₐ[C] RatFunc C :=
  RatFunc.liftAlgHom (invPoly c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (invPoly_injective hc0))

lemma invHom_algebraMap (p : C[X]) :
    invHom hc0 (algebraMap C[X] (RatFunc C) p) =
      aeval (algebraMap C (RatFunc C) c / RatFunc.X) p := by
  have := RatFunc.liftAlgHom_apply_div (invPoly c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (invPoly_injective hc0)) p 1
  simpa [invPoly, invHom] using this

lemma invHom_X : invHom hc0 RatFunc.X = algebraMap C (RatFunc C) c / RatFunc.X := by
  simpa using invHom_algebraMap hc0 Polynomial.X

lemma invHom_invHom (φ : RatFunc C) : invHom hc0 (invHom hc0 φ) = φ := by
  have hp (p : C[X]) : invHom hc0 (invHom hc0 (algebraMap C[X] (RatFunc C) p)) =
      algebraMap C[X] (RatFunc C) p := by
    rw [invHom_algebraMap, ← Polynomial.aeval_algHom_apply, map_div₀, AlgHom.commutes,
      invHom_X]
    have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
    rw [div_div_cancel₀ hc, ← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply,
      aeval_X_left_apply]
  rw [← RatFunc.num_div_denom φ, map_div₀, map_div₀, hp, hp]

/-- The inversion `x ↦ c/x`, an involution of `C(x)`. -/
noncomputable def inv : RatFunc C ≃ₐ[C] RatFunc C :=
  AlgEquiv.ofAlgHom (invHom hc0) (invHom hc0) (AlgHom.ext (invHom_invHom hc0))
    (AlgHom.ext (invHom_invHom hc0))

lemma inv_apply (φ : RatFunc C) : inv hc0 φ = invHom hc0 φ := rfl

lemma inv_inv_apply (φ : RatFunc C) : inv hc0 (inv hc0 φ) = φ := invHom_invHom hc0 φ

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- The inverse radius `|c| / s`. -/
noncomputable def invRad (hc0 : c ≠ 0) (s : ℝ≥0ˣ) : ℝ≥0ˣ :=
  Units.mk0 ‖c‖₊ (by simpa using hc0) * s⁻¹

lemma coe_invRad (s : ℝ≥0ˣ) : ((invRad hc0 s : ℝ≥0ˣ) : ℝ≥0) = ‖c‖₊ / s := by
  simp [invRad, div_eq_mul_inv]

lemma gaussRat_X_sub_C (s : ℝ≥0ˣ) (b : C) :
    w s (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) = max ‖b‖₊ (s : ℝ≥0) := by
  rw [gaussRat_algebraMap, gauss_X_sub_C, zero_sub, Valuation.map_neg, NormedField.valuation_apply]

lemma gaussRat_C_sub_mul_X (s : ℝ≥0ˣ) (b : C) :
    w s (algebraMap C (RatFunc C) c - algebraMap C (RatFunc C) b * RatFunc.X) =
      max ‖c‖₊ (‖b‖₊ * s) := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, zero_mul, sub_zero, gaussRat_C]
    simp
  have : algebraMap C (RatFunc C) c - algebraMap C (RatFunc C) b * RatFunc.X =
      algebraMap C (RatFunc C) (-b) * algebraMap C[X] (RatFunc C) (X - Polynomial.C (c / b)) := by
    have hcb : algebraMap C[X] (RatFunc C) (Polynomial.C (c / b)) =
        algebraMap C (RatFunc C) c / algebraMap C (RatFunc C) b := by
      rw [← map_div₀, IsScalarTower.algebraMap_apply C C[X] (RatFunc C) (c / b)]; rfl
    have hb' : algebraMap C (RatFunc C) b ≠ 0 := by simpa using hb
    rw [_root_.map_sub, RatFunc.algebraMap_X, hcb, _root_.map_neg]
    field_simp
    ring
  rw [this, map_mul, gaussRat_C, gaussRat_X_sub_C, nnnorm_neg, mul_max_of_nonneg _ _ zero_le,
    nnnorm_div, mul_div_cancel₀ _ (by simpa using hb)]

variable [IsAlgClosed C]

/-- **The inversion exchanges the Gauss points `w_{0,s}` and `w_{0,|c|/s}`.** -/
theorem gaussRat_inv (s : ℝ≥0ˣ) (φ : RatFunc C) : w s (inv hc0 φ) = w (invRad hc0 s) φ := by
  have h := valuation_ratFunc_ext_of_linear (w₁ := (w s).comap (inv hc0).toRingHom)
    (w₂ := w (invRad hc0 s)) (fun b ↦ ?_) (fun b ↦ ?_)
  · exact congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v φ) h
  · change w s (inv hc0 (algebraMap C (RatFunc C) b)) = w (invRad hc0 s) (algebraMap C _ b)
    rw [AlgEquiv.commutes, gaussRat_C, gaussRat_C]
  · change w s (inv hc0 (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
    have hb : algebraMap C[X] (RatFunc C) (Polynomial.C b) = algebraMap C (RatFunc C) b := by
      rw [IsScalarTower.algebraMap_apply C C[X] (RatFunc C)]; rfl
    rw [gaussRat_X_sub_C, _root_.map_sub, RatFunc.algebraMap_X, hb, _root_.map_sub,
      AlgEquiv.commutes, inv_apply, invHom_X, coe_invRad]
    have hX : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
    have : algebraMap C (RatFunc C) c / RatFunc.X - algebraMap C (RatFunc C) b =
        (algebraMap C (RatFunc C) c - algebraMap C (RatFunc C) b * RatFunc.X) / RatFunc.X := by
      field_simp
    rw [this, map_div₀, gaussRat_C_sub_mul_X, AnnulusUnit.gaussRat_X]
    rw [← max_div_div_right zero_le, mul_div_cancel_right₀ _ (by simp)]
    exact max_comm _ _

end Inversion

end GaussTube

end SemistableReduction
