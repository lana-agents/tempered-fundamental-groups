/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Adjoining a root of a unit is étale

Let `R` be a commutative ring, `u ∈ R` a unit and `n` invertible in `R`. Then
`R[Z] ⧸ (Z ^ n - u) = AdjoinRoot (X ^ n - C u)` is étale over `R`
(`RootOfUnit.etale`, Blueprint §9.2, second step of Abhyankar's lemma): it is the standard étale
algebra of the pair `(X ^ n - u, 1)`, since
`n X ^ (n - 1) · (n u)⁻¹ X - (X ^ n - u) · u⁻¹ = 1`.

For a local ring `R` (e.g. a discrete valuation ring) `n` is invertible in `R` iff it is nonzero in
the residue field.
-/

open Polynomial

namespace SemistableReduction

namespace RootOfUnit

variable {R : Type*} [CommRing R] {u : R} {n : ℕ}

/-- The standard étale pair `(X ^ n - u, 1)`. -/
noncomputable def standardEtalePair (hu : IsUnit u) (hn : IsUnit (n : R)) :
    StandardEtalePair R where
  f := X ^ n - C u
  monic_f := by
    nontriviality R
    exact monic_X_pow_sub_C _ (by rintro rfl; simp at hn)
  g := 1
  cond := by
    refine ⟨C (↑(hn.unit⁻¹ * hu.unit⁻¹) : R) * X, -C (↑hu.unit⁻¹ : R), 1, ?_⟩
    nontriviality R
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, one_pow]
    have h1 : (X : R[X]) ^ (n - 1) * X = X ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
    have h2 : (C (n : R) : R[X]) * C (↑(hn.unit⁻¹ * hu.unit⁻¹) : R) = C (↑hu.unit⁻¹ : R) := by
      rw [← C_mul, Units.val_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    have h3 : (C u : R[X]) * C (↑hu.unit⁻¹ : R) = 1 := by
      rw [← C_mul, IsUnit.mul_val_inv, C_1]
    calc C (n : R) * X ^ (n - 1) * (C (↑(hn.unit⁻¹ * hu.unit⁻¹) : R) * X) +
          (X ^ n - C u) * -C (↑hu.unit⁻¹ : R)
        = (C (n : R) * C (↑(hn.unit⁻¹ * hu.unit⁻¹) : R)) * (X ^ (n - 1) * X) -
          X ^ n * C (↑hu.unit⁻¹ : R) + C u * C (↑hu.unit⁻¹ : R) := by ring
      _ = 1 := by rw [h1, h2, h3]; ring

/-- The standard étale algebra of `standardEtalePair` is `R[Z] ⧸ (Z ^ n - u)`. -/
noncomputable def equiv (hu : IsUnit u) (hn : IsUnit (n : R)) :
    (standardEtalePair hu hn).Ring ≃ₐ[R] AdjoinRoot (standardEtalePair hu hn).f :=
  let P := standardEtalePair hu hn
  have h : IsUnit (AdjoinRoot.mk P.f P.g) := by
    rw [show P.g = 1 from rfl, map_one]
    exact isUnit_one
  P.equivAwayAdjoinRoot.trans ((IsLocalization.atUnit (AdjoinRoot P.f)
    (Localization.Away (AdjoinRoot.mk P.f P.g)) _ h).restrictScalars R).symm

/-- **Adjoining a root of a unit is étale.** If `u` is a unit and `n` is invertible in `R`, then
`R[Z] ⧸ (Z ^ n - u)` is étale over `R`. -/
theorem etale (hu : IsUnit u) (hn : IsUnit (n : R)) : Algebra.Etale R (AdjoinRoot (X ^ n - C u)) :=
  .of_equiv (equiv hu hn)

/-- `R[Z] ⧸ (Z ^ n - u)` is standard étale over `R`. -/
theorem isStandardEtale (hu : IsUnit u) (hn : IsUnit (n : R)) :
    Algebra.IsStandardEtale R (AdjoinRoot (X ^ n - C u)) :=
  .of_equiv (equiv hu hn)

/-- Over a local ring: if `u` is a unit and `n ≠ 0` in the residue field, then
`R[Z] ⧸ (Z ^ n - u)` is étale over `R`. -/
theorem etale_of_residueField [IsLocalRing R] (hu : IsUnit u)
    (hn : (n : IsLocalRing.ResidueField R) ≠ 0) : Algebra.Etale R (AdjoinRoot (X ^ n - C u)) :=
  etale hu ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rwa [map_natCast]))

end RootOfUnit

end SemistableReduction
