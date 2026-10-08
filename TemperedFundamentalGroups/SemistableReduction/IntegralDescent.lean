/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Descent of integrality along base change of the constants (O1, step (3))

Blueprint §9.12, O1 (S7.9, the maximum principle over `E`). Let `φ : K₀ → K₁` be a field
extension, `A ⊆ K₀`, `B ⊆ K₁` subrings with `B` integrally closed with fraction field `K₁` and
`φ⁻¹(B) = A`, and `χ : L₀ → L₁` a map of a `K₀`-algebra to a `K₁`-algebra. If `y ∈ L₀`
keeps its minimal polynomial (`minpoly K₁ (χ y) = φ (minpoly K₀ y)`, e.g. when `L₁ = L₀ ⊗ K₁` is a
field) and `χ y` is integral over `B`, then `y` is integral over `A`
(`isIntegral_of_isIntegral_map`): the coefficients of the minimal polynomial lie in `B ∩ K₀ = A`.
-/

open Polynomial

namespace SemistableReduction

variable {K₀ K₁ L₀ L₁ : Type*} [Field K₀] [Field K₁] [Field L₀] [Field L₁] [Algebra K₀ L₀]
  [Algebra K₁ L₁]

/-- **Integrality descends along base change of the constants.** -/
theorem isIntegral_of_isIntegral_map (φ : K₀ →+* K₁) (χ : L₀ →+* L₁)
    (A : Subring K₀) (B : Subring K₁) [IsIntegrallyClosed B] [IsFractionRing B K₁]
    (hAB : ∀ z : K₀, φ z ∈ B → z ∈ A) {y : L₀}
    (hmin : minpoly K₁ (χ y) = (minpoly K₀ y).map φ)
    (hy : letI : Algebra B L₁ := ((algebraMap K₁ L₁).comp B.subtype).toAlgebra
      IsIntegral B (χ y)) :
    letI : Algebra A L₀ := ((algebraMap K₀ L₀).comp A.subtype).toAlgebra
    IsIntegral A y := by
  letI : Algebra B L₁ := ((algebraMap K₁ L₁).comp B.subtype).toAlgebra
  letI : Algebra A L₀ := ((algebraMap K₀ L₀).comp A.subtype).toAlgebra
  haveI : IsScalarTower B K₁ L₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A K₀ L₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hint : IsIntegral K₀ y := by
    by_contra h
    have h0 : minpoly K₀ y = 0 := minpoly.eq_zero h
    have h1 := minpoly.ne_zero (IsIntegral.tower_top (A := K₁) hy)
    rw [hmin, h0, Polynomial.map_zero] at h1
    exact h1 rfl
  have hB := minpoly.isIntegrallyClosed_eq_field_fractions' K₁ hy
  -- the coefficients lie in `A`
  have hcoeff : ∀ i, (minpoly K₀ y).coeff i ∈ A := by
    intro i
    apply hAB
    have := congrArg (fun p ↦ p.coeff i) (hmin.symm.trans hB)
    simp only [coeff_map] at this
    rw [this]
    exact ((minpoly B (χ y)).coeff i).2
  let p : A[X] := (minpoly K₀ y).toSubring A (by
    intro z hz
    obtain ⟨i, -, rfl⟩ : ∃ i, ¬(minpoly K₀ y).coeff i = 0 ∧ (minpoly K₀ y).coeff i = z := by
      simpa [coeffs] using hz
    exact hcoeff i)
  refine ⟨p, ?_, ?_⟩
  · exact (Polynomial.monic_toSubring _ _ _).mpr (minpoly.monic hint)
  · rw [← aeval_def, ← aeval_map_algebraMap K₀,
      show p.map (algebraMap A K₀) = minpoly K₀ y from Polynomial.map_toSubring _ _ _]
    exact minpoly.aeval K₀ y

end SemistableReduction
