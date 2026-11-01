/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NormOverlapLevel

/-!
# Witnesses of the overlap identification from the function field (MR12 T2 S6, G5)

For normalisations `B₀`, `B₁` of `A₀`, `A₁` in `L` with common localization `W = A₀[1/a₀] =
A₁[1/a₁]`:

* **`NormOverlap.equiv_mul_pow_of_L`**: if `b · a₁ᵏ = y` in `L`, then `b/1 ↦ y/a₁ᵏ` under
  `B₀[1/a₀] ≃ B₁[1/a₁]` (the hypothesis of `NormOverlap.omegaEquiv_mul_pow`);
* **`NormOverlap.omegaEquiv_mul_pow_of_L`**: then `omegaEquiv I (b̄/1) · ā₁ᵏ = ȳ/1` for every
  ideal `I` of the base.
-/

universe u

namespace SemistableReduction

namespace NormOverlap

noncomputable section

section Main

variable {O A₀ A₁ W B₀ B₁ : Type u} {L : Type*} [CommRing O] [CommRing A₀] [CommRing A₁]
  [CommRing W] [CommRing B₀] [CommRing B₁] [Field L]
  [Algebra O A₀] [Algebra O A₁] [Algebra O W] [Algebra A₀ W] [Algebra A₁ W]
  [IsScalarTower O A₀ W] [IsScalarTower O A₁ W]
  [Algebra A₀ L] [Algebra A₁ L] [Algebra W L] [IsScalarTower A₀ W L] [IsScalarTower A₁ W L]
  [Algebra A₀ B₀] [Algebra B₀ L] [IsScalarTower A₀ B₀ L] [IsIntegralClosure B₀ A₀ L]
  [Algebra A₁ B₁] [Algebra B₁ L] [IsScalarTower A₁ B₁ L] [IsIntegralClosure B₁ A₁ L]
  (a₀ : A₀) (a₁ : A₁) [IsLocalization.Away a₀ W] [IsLocalization.Away a₁ W]
  (ha₀ : algebraMap A₀ L a₀ ≠ 0) (ha₁ : algebraMap A₁ L a₁ ≠ 0)

/-- **A witness of `B₀[1/a₀] ≃ B₁[1/a₁]` from an equation in `L`**: if `b · a₁ᵏ = y` in `L`,
then `b/1 ↦ y/a₁ᵏ`. -/
theorem equiv_mul_pow_of_L (b : B₀) (y : B₁) (k : ℕ)
    (h : algebraMap B₀ L b * algebraMap A₁ L a₁ ^ k = algebraMap B₁ L y) :
    (letI := algW (B := B₀) (W := W) a₀; letI := algL (B := B₀) a₀ ha₀
      letI := algW (B := B₁) (W := W) a₁; letI := algL (B := B₁) a₁ ha₁
      haveI := towerWL (B := B₀) (W := W) a₀ ha₀
      haveI := isIntegralClosure_away (B := B₀) (W := W) a₀ ha₀
      haveI := towerWL (B := B₁) (W := W) a₁ ha₁
      haveI := isIntegralClosure_away (B := B₁) (W := W) a₁ ha₁
      IsIntegralClosure.equiv (R := W) (B := L) (A := Localization.Away (algebraMap A₀ B₀ a₀))
        (Localization.Away (algebraMap A₁ B₁ a₁)) (algebraMap B₀ _ b)) *
      algebraMap B₁ (Localization.Away (algebraMap A₁ B₁ a₁)) (algebraMap A₁ B₁ a₁) ^ k =
      algebraMap B₁ _ y := by
  letI := algW (B := B₀) (W := W) a₀
  letI := algL (B := B₀) a₀ ha₀
  haveI := towerL (B := B₀) a₀ ha₀
  haveI := towerWL (B := B₀) (W := W) a₀ ha₀
  haveI := isIntegralClosure_away (B := B₀) (W := W) a₀ ha₀
  letI := algW (B := B₁) (W := W) a₁
  letI := algL (B := B₁) a₁ ha₁
  haveI := towerL (B := B₁) a₁ ha₁
  haveI := towerWL (B := B₁) (W := W) a₁ ha₁
  haveI := isIntegralClosure_away (B := B₁) (W := W) a₁ ha₁
  apply IsIntegralClosure.algebraMap_injective (Localization.Away (algebraMap A₁ B₁ a₁)) W L
  rw [map_mul, map_pow, IsIntegralClosure.algebraMap_equiv,
    ← IsScalarTower.algebraMap_apply B₀ (Localization.Away (algebraMap A₀ B₀ a₀)) L,
    ← IsScalarTower.algebraMap_apply B₁ (Localization.Away (algebraMap A₁ B₁ a₁)) L,
    ← IsScalarTower.algebraMap_apply B₁ (Localization.Away (algebraMap A₁ B₁ a₁)) L,
    ← IsScalarTower.algebraMap_apply A₁ B₁ L]
  exact h

variable (I : Ideal O)
  [Algebra (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))]
  [Algebra (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    (W ⧸ I.map (algebraMap O W))]
  (hS₀ : ∀ x : A₀, algebraMap (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₀ W x))
  (hS₁ : ∀ x : A₁, algebraMap (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₁ W x))

/-- **`omegaEquiv` on a witness from `L`**: if `b · a₁ᵏ = y` in `L`, then
`omegaEquiv I (b̄/1) · ā₁ᵏ = ȳ/1`. -/
theorem omegaEquiv_mul_pow_of_L (b : B₀) (y : B₁) (k : ℕ)
    (h : algebraMap B₀ L b * algebraMap A₁ L a₁ ^ k = algebraMap B₁ L y) :
    omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀ ha₁
        (algebraMap (B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) _
          (Ideal.Quotient.mk _ b)) *
      algebraMap (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
        (Localization.Away (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
          (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) (Ideal.Quotient.mk _ a₁)))
        (Ideal.Quotient.mk _ (algebraMap A₁ B₁ a₁)) ^ k =
      algebraMap (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) _
        (Ideal.Quotient.mk _ y) :=
  omegaEquiv_mul_pow (W := W) a₀ a₁ ha₀ ha₁ I hS₀ hS₁ b y k
    (equiv_mul_pow_of_L (W := W) a₀ a₁ ha₀ ha₁ b y k h)

end Main

end

end NormOverlap

end SemistableReduction
