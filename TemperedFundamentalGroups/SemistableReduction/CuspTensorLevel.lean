/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspInput
import TemperedFundamentalGroups.SemistableReduction.TateV1Level

/-!
# The levels of a normalisation over the chart `D(c₀)` (MR12 T2 S6, G4 over `V₀`)

For a chart `T0'` (an `O`-algebra), `c₀ ∈ T0'`, the chart `Rc = T0'[1/c₀]`, a `T0'`-algebra `B₀`
and its localization `Bc = B₀[1/c₀]` (an `Rc`-algebra compatibly):

* **`CuspTower.toTensorC`**: `B₀/ϖⁿ⁺¹ → Rc/ϖⁿ⁺¹ ⊗_{Rc} Bc`, `b̄ ↦ 1 ⊗ b` (`toTensorC_mk`), a
  localization away from `c₀` (`isLocalization_toTensorC`), compatible with the structure maps
  `T0' → Tn T0' n → Tn Rc n` (`toTensorC_algebraMap`; the hypothesis `ht` of
  `FormalCuspLevel.CuspLevels.φPX`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace CuspTower

noncomputable section

variable {O : Type u} [CommRing O] (ϖ : O) {T0' : Type u} [CommRing T0'] [Algebra O T0']
  (c0 : T0') (B₀ : Type u) [CommRing B₀] [Algebra T0' B₀] (Bc : Type u) [CommRing Bc]
  [Algebra (Rc T0' c0) Bc] [Algebra B₀ Bc]
  (hB : ∀ x, algebraMap (Rc T0' c0) Bc (algebraMap T0' (Rc T0' c0) x) =
    algebraMap B₀ Bc (algebraMap T0' B₀ x)) (n : ℕ)

/-- The ideal `ϖⁿ⁺¹` of `Rc` is the image of the one of `T0'`. -/
lemma IRc_eq : (EtaleTower.Iv ϖ n).map (algebraMap O (Rc T0' c0)) =
    (EtaleTower.In ϖ T0' n).map (algebraMap T0' (Rc T0' c0)) := by
  rw [EtaleTower.In, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **The patch side of the level `B₀/ϖⁿ⁺¹`**: `B₀/ϖⁿ⁺¹ → Rc/ϖⁿ⁺¹ ⊗_{Rc} Bc`, `b̄ ↦ 1 ⊗ b`. -/
def toTensorC : TateGlue1.Xn ϖ T0' B₀ n →+* EtaleTower.Tn ϖ (Rc T0' c0) n ⊗[Rc T0' c0] Bc :=
  letI : Algebra T0' Bc := ((algebraMap B₀ Bc).comp (algebraMap T0' B₀)).toAlgebra
  haveI : IsScalarTower T0' (Rc T0' c0) Bc := IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower T0' B₀ Bc := IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Bc
      ((EtaleTower.Iv ϖ n).map (algebraMap O (Rc T0' c0)))).toRingEquiv.toRingHom.comp
    (NormAway.quotMap (B₁ := B₀) (B := Bc) (EtaleTower.In ϖ T0' n) _ (IRc_eq ϖ c0 n))

lemma toTensorC_mk (b : B₀) :
    toTensorC ϖ c0 B₀ Bc hB n (Ideal.Quotient.mk _ b) = 1 ⊗ₜ algebraMap B₀ Bc b :=
  rfl

/-- `toTensorC` is compatible with the structure maps `T0' → Tn T0' n → Tn Rc n`. -/
lemma toTensorC_algebraMap (r : T0') : letI := algBR ϖ T0' c0 n
    toTensorC ϖ c0 B₀ Bc hB n (algebraMap T0' (TateGlue1.Xn ϖ T0' B₀ n) r) =
      algebraMap (EtaleTower.Tn ϖ (Rc T0' c0) n) (EtaleTower.Tn ϖ (Rc T0' c0) n ⊗[Rc T0' c0] Bc)
        (algebraMap (EtaleTower.Tn ϖ T0' n) (EtaleTower.Tn ϖ (Rc T0' c0) n)
          (algebraMap T0' (EtaleTower.Tn ϖ T0' n) r)) := by
  letI := algBR ϖ T0' c0 n
  change (1 : EtaleTower.Tn ϖ (Rc T0' c0) n) ⊗ₜ algebraMap B₀ Bc (algebraMap T0' B₀ r) =
    (Ideal.Quotient.mk _ (algebraMap T0' (Rc T0' c0) r)) ⊗ₜ (1 : Bc)
  rw [← hB, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rfl

variable [IsLocalization.Away (algebraMap T0' B₀ c0) Bc]

/-- **`toTensorC` is a localization away from `c₀`.** -/
theorem isLocalization_toTensorC : letI := (toTensorC ϖ c0 B₀ Bc hB n).toAlgebra
    IsLocalization.Away (algebraMap T0' (TateGlue1.Xn ϖ T0' B₀ n) c0)
      (EtaleTower.Tn ϖ (Rc T0' c0) n ⊗[Rc T0' c0] Bc) := by
  letI : Algebra T0' Bc := ((algebraMap B₀ Bc).comp (algebraMap T0' B₀)).toAlgebra
  haveI : IsScalarTower T0' (Rc T0' c0) Bc := IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower T0' B₀ Bc := IsScalarTower.of_algebraMap_eq' rfl
  have h := RingHomAway.equiv _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Bc
      ((EtaleTower.Iv ϖ n).map (algebraMap O (Rc T0' c0)))).toRingEquiv _
    (NormAway.isLocalization_quotMap (B₁ := B₀) (B := Bc) (EtaleTower.In ϖ T0' n) _
      (IRc_eq ϖ c0 n) c0)
  rwa [Ideal.Quotient.algebraMap_quotient_map_quotient] at h

end

end CuspTower

end SemistableReduction
