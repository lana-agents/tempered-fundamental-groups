/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.RamifiedQuadratic

/-!
# Maps out of `K(√ϖ)` and its involution (B3e)

* `liftK'`: the `K`-algebra map `K(√ϖ) → S` sending `√ϖ` to a square root `y` of `ϖ` in `S`;
* `σK`: the involution `√ϖ ↦ -√ϖ` of `K(√ϖ)`, and `σO` its restriction to `O' = O_{K(√ϖ)}`.
-/

universe u

open Polynomial IsLocalRing

namespace TemperedFundamentalGroups.RamifiedQuadratic

open SemistableReduction.W10Apply

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)

local notation "C" => AlgebraicClosure K

lemma isIntegral_sqrtϖ : IsIntegral K (sqrtϖ ϖ) := Algebra.IsIntegral.isIntegral _

variable {S : Type u} [CommRing S] [Algebra K S]

/-- **`K(√ϖ) → S`, `√ϖ ↦ y`** for `y² = ϖ`. -/
def liftK' (y : S) (hy : y ^ 2 = algebraMap K S ϖ) : K' ϖ →ₐ[K] S :=
  (IntermediateField.adjoin.powerBasis (isIntegral_sqrtϖ (ϖ := ϖ))).lift y (by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen,
      minpoly_sqrtϖ hϖ, map_sub, map_pow, aeval_X, aeval_C, hy, sub_self])

lemma liftK'_s (y : S) (hy : y ^ 2 = algebraMap K S ϖ) : liftK' hϖ y hy (s ϖ) = y :=
  (IntermediateField.adjoin.powerBasis (isIntegral_sqrtϖ (ϖ := ϖ))).lift_gen _ _

/-- Maps out of `K(√ϖ)` are determined by the image of `√ϖ`. -/
lemma algHom_ext {f g : K' ϖ →ₐ[K] S} (h : f (s ϖ) = g (s ϖ)) : f = g :=
  (IntermediateField.adjoin.powerBasis (isIntegral_sqrtϖ (ϖ := ϖ))).algHom_ext h

lemma s_sq : (s ϖ) ^ 2 = algebraMap K (K' ϖ) ϖ :=
  Subtype.ext (by
    change sqrtϖ ϖ ^ 2 = _
    rw [sqrtϖ_sq]; rfl)

lemma neg_s_sq : (-s ϖ) ^ 2 = algebraMap K (K' ϖ) ϖ := by rw [neg_sq, s_sq]

/-- **The involution `√ϖ ↦ -√ϖ`.** -/
def σK : K' ϖ ≃ₐ[K] K' ϖ :=
  AlgEquiv.ofAlgHom (liftK' hϖ (-s ϖ) neg_s_sq) (liftK' hϖ (-s ϖ) neg_s_sq)
    (algHom_ext (by simp [liftK'_s]))
    (algHom_ext (by simp [liftK'_s]))

lemma σK_s : σK hϖ (s ϖ) = -s ϖ := liftK'_s hϖ _ neg_s_sq

lemma σK_σK (z : K' ϖ) : σK hϖ (σK hϖ z) = z := by
  have : (σK hϖ).toAlgHom.comp (σK hϖ).toAlgHom = AlgHom.id K (K' ϖ) :=
    algHom_ext (by simp [σK_s])
  exact AlgHom.congr_fun this z

variable [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

/-- The involution of `O'`. -/
def σO : O' ϖ →+* O' ϖ :=
  ((σK hϖ : K' ϖ →+* K' ϖ).comp (O' ϖ).subtype).codRestrict (O' ϖ).toSubring
    fun z ↦ algEquiv_mem_OE O (K' ϖ) (σK hϖ) z.2

@[simp] lemma coe_σO (z : O' ϖ) : (σO hϖ z : K' ϖ) = σK hϖ z := rfl

lemma σO_sO : σO hϖ (sO ϖ) = -sO ϖ := Subtype.ext (σK_s hϖ)

lemma σO_σO (z : O' ϖ) : σO hϖ (σO hϖ z) = z := Subtype.ext (σK_σK hϖ z)

lemma σO_algebraMap (o : O) : σO hϖ (algebraMap O (O' ϖ) o) = algebraMap O (O' ϖ) o :=
  Subtype.ext ((σK hϖ).commutes (o : K))

end

end TemperedFundamentalGroups.RamifiedQuadratic
