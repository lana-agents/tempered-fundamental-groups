/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateModel
import TemperedFundamentalGroups.SemistableReduction.ModelProjection
import TemperedFundamentalGroups.SemistableReduction.ModelChartAlgebra

/-!
# A finite morphism from the Tate model to `ℙ¹` (Blueprint §12.8, M2 step 4(c), Tate case)

The Tate model `𝒯 = TateModel.model π b₄ b₆ ⊆ ℙ²_O` is the reduced subscheme on the cubic
`F = v² w + u v w − π u³ − π b₄ u w² − b₆ w³`. For `t ∈ O` with `t² − b₆` a unit, the point
`P = [0 : t : 1]` has `F(P) = t² − b₆`, so it lies on no fibre of `𝒯`, and the projection from
`P`,

  `[ℓ₀ : ℓ₁] = [v − t w : u] : 𝒯 ⟶ ℙ¹_O`

(`TateProjection.toP1`), is a morphism over `Spec O`. It is **finite** (`isFinite_toP1`): on the
chart `ℓ₀ ≠ 0`, with `h = u / ℓ₀` and `z = w / ℓ₀`, dividing `F` by `ℓ₀³` gives
`(t² − b₆) z³ + (2t + t h − π b₄ h) z² + (1 + h) z − π h³ = 0`, so `z` (and `v / ℓ₀ = 1 + t z`) is
integral over `O[h]`; on the chart `u ≠ 0`, with `h' = ℓ₀ / u` and `z' = w / u`,
`(t² − b₆) z'³ + (2t h' + t − π b₄) z'² + (h'² + h') z' − π = 0`. Hence the projection is locally
quasi-finite (`ModelProjection`), and finite by Zariski's main theorem since `𝒯` is proper
(`SemistableReduction.ModelChartAlgebra.isFinite_of_locallyQuasiFinite`).

Over a local ring such a `t` always exists (`t = 0` if `b₆` is a unit, `t = 1` otherwise), so
`exists_isFinite_toP1`: **the Tate model admits a finite morphism to `ℙ¹_O` over `O`** (of
degree `3`, the degree of the plane cubic), and every finite cover of it is the relative `Spec`
of a chart algebra on `ℙ¹_O` (`ModelChartAlgebra.chartAlgebraOfFinite`), the input format of the
algebraization in `formal-schemes`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace TemperedFundamentalGroups

namespace TateProjection

open SemistableReduction.LinearProjection

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] (π b₄ b₆ t : O)

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

/-- The linear forms `ℓ₀ = v − t w` and `ℓ₁ = u` (coordinates `[u : v : w]` on `ℙ²_O`). -/
def lin : Fin (1 + 1) → MvPolynomial (Fin (2 + 1)) O := ![X 1 - C t * X 2, X 0]

lemma lin_zero : lin t 0 = X 1 - C t * X 2 := rfl

lemma lin_one : lin t 1 = X 0 := rfl

lemma lin_mem : ∀ j, lin t j ∈ MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O 1 := by
  intro j
  rw [mem_homogeneousSubmodule]
  fin_cases j
  · exact (isHomogeneous_X O 1).sub (isHomogeneous_C_mul_X t 2)
  · exact isHomogeneous_X O 0

lemma F_eq_lin : TateModel.F π b₄ b₆ = C (t ^ 2 - b₆) * X 2 ^ 3 +
    lin t 0 * (2 * C t * X 2 ^ 2 + X 2 * lin t 0 + X 0 * X 2) +
    X 0 * (C t * X 2 ^ 2 - C π * C b₄ * X 2 ^ 2 - C π * X 0 ^ 2) := by
  simp only [TateModel.F, lin_zero, map_sub, map_pow, map_mul]
  ring

lemma F_mem3 : TateModel.F π b₄ b₆ ∈ (𝒜 2) 3 :=
  (mem_homogeneousSubmodule _ _).2 (TateModel.isHomogeneous_F π b₄ b₆)

variable {t b₆} in
/-- **The Tate model misses the centre `[0 : t : 1]` of the projection.** -/
lemma hcov (hε : IsUnit (t ^ 2 - b₆)) (z : (TateModel.modelIdeal π b₄ b₆).subscheme) :
    TateModel.ι π b₄ b₆ z ∈ D (lin t) (lin_mem t) 0 ∨
      TateModel.ι π b₄ b₆ z ∈ D (lin t) (lin_mem t) 1 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h0, h1⟩ := h
  set y := TateModel.ι π b₄ b₆ z
  replace h0 : lin t 0 ∈ y.asHomogeneousIdeal.toIdeal := by
    have : y ∉ Proj.basicOpen (𝒜 2) (linHom (lin t) (lin_mem t) (X 0)) := h0
    by_contra hn
    exact this ((Proj.mem_basicOpen (𝒜 2) _ _).2 (by rw [linHom_X]; exact hn))
  replace h1 : X 0 ∈ y.asHomogeneousIdeal.toIdeal := by
    have : y ∉ Proj.basicOpen (𝒜 2) (linHom (lin t) (lin_mem t) (X 1)) := h1
    by_contra hn
    exact this ((Proj.mem_basicOpen (𝒜 2) _ _).2 (by rw [linHom_X]; exact hn))
  have hF := TateModel.F_mem π b₄ b₆ z
  rw [F_eq_lin π b₄ b₆ t] at hF
  have hw3 : C (t ^ 2 - b₆) * X 2 ^ 3 ∈ y.asHomogeneousIdeal.toIdeal := by
    have h' : lin t 0 * (2 * C t * X 2 ^ 2 + X 2 * lin t 0 + X 0 * X 2) +
        X 0 * (C t * X 2 ^ 2 - C π * C b₄ * X 2 ^ 2 - C π * X 0 ^ 2) ∈
          y.asHomogeneousIdeal.toIdeal :=
      add_mem (Ideal.mul_mem_right _ _ h0) (Ideal.mul_mem_right _ _ h1)
    have := Ideal.sub_mem _ hF h'
    simpa using this
  have hw : (X 2 : MvPolynomial (Fin (2 + 1)) O) ∈ y.asHomogeneousIdeal.toIdeal := by
    have h3 : (X 2 : MvPolynomial (Fin (2 + 1)) O) ^ 3 ∈ y.asHomogeneousIdeal.toIdeal := by
      have := Ideal.mul_mem_left _ (C (↑hε.unit⁻¹ : O)) hw3
      rwa [← mul_assoc, ← map_mul, hε.val_inv_mul, map_one, one_mul] at this
    exact y.isPrime.mem_of_pow_mem 3 h3
  have hv : (X 1 : MvPolynomial (Fin (2 + 1)) O) ∈ y.asHomogeneousIdeal.toIdeal := by
    have : (X 1 : MvPolynomial (Fin (2 + 1)) O) = lin t 0 + C t * X 2 := by
      rw [lin_zero]; ring
    rw [this]
    exact add_mem h0 (Ideal.mul_mem_left _ _ hw)
  exact TateModel.not_all_X_mem y h1 hv hw

/-! ### The integrality relations on the two charts -/

/-- The constants `O → (O[y]_{(y_k)})₀`. -/
abbrev cst (k : Fin (1 + 1)) (o : O) : Away (𝒜 1) (X k : MvPolynomial (Fin (1 + 1)) O) :=
  fromZeroRingHom (𝒜 1) _ (algebraMap O ((𝒜 1) 0) o)

/-- The coordinate `y₁ / y₀` of the chart `D₊(y₀)` of `ℙ¹`. -/
abbrev H₀ : Away (𝒜 1) (X 0 : MvPolynomial (Fin (1 + 1)) O) :=
  Away.mk (𝒜 1) (X_mem' 0) 1 (X 1) (by simpa using X_mem' (O := O) 1)

/-- The coordinate `y₀ / y₁` of the chart `D₊(y₁)` of `ℙ¹`. -/
abbrev H₁ : Away (𝒜 1) (X 1 : MvPolynomial (Fin (1 + 1)) O) :=
  Away.mk (𝒜 1) (X_mem' 1) 1 (X 0) (by simpa using X_mem' (O := O) 0)

lemma val_map_H₀ : (Away.map (linHom (lin t) (lin_mem t)) (X 0) (H₀ (O := O))).val =
    algebraMap (MvPolynomial (Fin (2 + 1)) O)
      (Localization.Away (linHom (lin t) (lin_mem t) (X 0))) (X 0) *
      IsLocalization.Away.invSelf (linHom (lin t) (lin_mem t) (X 0)) := by
  rw [Away.map_mk, val_away_mk, pow_one]
  simp [lin_one]

lemma val_map_H₁ : (Away.map (linHom (lin t) (lin_mem t)) (X 1) (H₁ (O := O))).val =
    algebraMap (MvPolynomial (Fin (2 + 1)) O)
      (Localization.Away (linHom (lin t) (lin_mem t) (X 1))) (X 1 - C t * X 2) *
      IsLocalization.Away.invSelf (linHom (lin t) (lin_mem t) (X 1)) := by
  rw [Away.map_mk, val_away_mk, pow_one]
  simp [lin_zero]

lemma val_map_cst (k : Fin (1 + 1)) (o : O) :
    (Away.map (linHom (lin t) (lin_mem t)) (X k) (cst k o)).val =
      algebraMap (MvPolynomial (Fin (2 + 1)) O)
        (Localization.Away (linHom (lin t) (lin_mem t) (X k))) (C o) := by
  rw [awayMap_fromZero, val_fromZero]

variable {t b₆} (hε : IsUnit (t ^ 2 - b₆))

/-- The monic cubic satisfied by `z = w / ℓ₀` over `O[h]`, `h = u / ℓ₀`. -/
def cubic₀ : Polynomial (Away (𝒜 1) (X 0 : MvPolynomial (Fin (1 + 1)) O)) :=
  Polynomial.X ^ 3 + Polynomial.C (cst 0 (↑hε.unit⁻¹ : O) * (cst 0 (2 * t) + cst 0 t * H₀ -
    cst 0 (π * b₄) * H₀)) * Polynomial.X ^ 2 +
    Polynomial.C (cst 0 (↑hε.unit⁻¹ : O) * (1 + H₀)) * Polynomial.X -
    Polynomial.C (cst 0 (↑hε.unit⁻¹ * π : O) * H₀ ^ 3)

lemma monic_cubic₀ : (cubic₀ π b₄ hε).Monic := by
  unfold cubic₀
  monicity!

lemma eval_cubic₀ : (cubic₀ π b₄ hε).eval₂ (Away.map (linHom (lin t) (lin_mem t)) (X 0))
    (coordFrac (lin t) (lin_mem t) 0 2) =
    fromZeroRingHom (𝒜 2) _ (algebraMap O _ (↑hε.unit⁻¹ : O)) *
      Away.isLocalizationElem ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 0))
        (F_mem3 π b₄ b₆) := by
  apply (show Function.Injective (algebraMap (Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 0)))
    (Localization.Away (linHom (lin t) (lin_mem t) (X 0)))) from val_injective _)
  simp only [cubic₀, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.eval₂_pow, map_add, map_sub, map_mul, map_pow, map_one,
    HomogeneousLocalization.algebraMap_apply, val_map_H₀, val_map_cst, val_away_mk, val_fromZero,
    GradedRingHom.coe_toRingHom, pow_one]
  set s := linHom (lin t) (lin_mem t) (X 0)
  set L := algebraMap (MvPolynomial (Fin (2 + 1)) O) (Localization.Away s)
  set I := IsLocalization.Away.invSelf (S := Localization.Away s) s
  have hs : s = X 1 - C t * X 2 := by simp [s, lin_zero]
  have hI : (L (X 1) - L (C t) * L (X 2)) * I = 1 := by
    rw [← map_mul, ← map_sub, ← hs]
    exact IsLocalization.Away.mul_invSelf s
  have he : L (C (↑hε.unit⁻¹ : O)) * (L (C t) ^ 2 - L (C b₆)) = 1 := by
    have h := congrArg (fun o : O ↦ L (C o)) hε.val_inv_mul
    simp only [map_mul, map_sub, map_pow, map_one] at h
    exact h
  simp only [TateModel.F, map_sub, map_add, map_mul, map_pow, map_ofNat]
  linear_combination (-(L (C (↑hε.unit⁻¹ : O))) * (L (X 2) * I) *
      (L (X 1) * I + 1 + L (C t) * (L (X 2) * I)) -
      L (C (↑hε.unit⁻¹ : O)) * (L (X 0) * I) * (L (X 2) * I)) * hI + (-(L (X 2) * I) ^ 3) * he

/-- The monic cubic satisfied by `z' = w / u` over `O[h']`, `h' = ℓ₀ / u`. -/
def cubic₁ : Polynomial (Away (𝒜 1) (X 1 : MvPolynomial (Fin (1 + 1)) O)) :=
  Polynomial.X ^ 3 + Polynomial.C (cst 1 (↑hε.unit⁻¹ : O) * (cst 1 (2 * t) * H₁ + cst 1 t -
    cst 1 (π * b₄))) * Polynomial.X ^ 2 +
    Polynomial.C (cst 1 (↑hε.unit⁻¹ : O) * (H₁ ^ 2 + H₁)) * Polynomial.X -
    Polynomial.C (cst 1 (↑hε.unit⁻¹ * π : O))

lemma monic_cubic₁ : (cubic₁ π b₄ hε).Monic := by
  unfold cubic₁
  monicity!

lemma eval_cubic₁ : (cubic₁ π b₄ hε).eval₂ (Away.map (linHom (lin t) (lin_mem t)) (X 1))
    (coordFrac (lin t) (lin_mem t) 1 2) =
    fromZeroRingHom (𝒜 2) _ (algebraMap O _ (↑hε.unit⁻¹ : O)) *
      Away.isLocalizationElem ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 1))
        (F_mem3 π b₄ b₆) := by
  apply (show Function.Injective (algebraMap (Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 1)))
    (Localization.Away (linHom (lin t) (lin_mem t) (X 1)))) from val_injective _)
  simp only [cubic₁, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow, map_add, map_sub, map_mul,
    map_pow, HomogeneousLocalization.algebraMap_apply, val_map_H₁, val_map_cst, val_away_mk,
    val_fromZero, GradedRingHom.coe_toRingHom, pow_one]
  set s := linHom (lin t) (lin_mem t) (X 1)
  set L := algebraMap (MvPolynomial (Fin (2 + 1)) O) (Localization.Away s)
  set I := IsLocalization.Away.invSelf (S := Localization.Away s) s
  have hs : s = X 0 := by simp [s, lin_one]
  have hI : L (X 0) * I = 1 := by
    rw [← hs]
    exact IsLocalization.Away.mul_invSelf s
  have he : L (C (↑hε.unit⁻¹ : O)) * (L (C t) ^ 2 - L (C b₆)) = 1 := by
    have h := congrArg (fun o : O ↦ L (C o)) hε.val_inv_mul
    simp only [map_mul, map_sub, map_pow, map_one] at h
    exact h
  simp only [TateModel.F, map_sub, map_add, map_mul, map_pow, map_ofNat]
  linear_combination (-(L (C (↑hε.unit⁻¹ : O))) * (L (X 1) * I * (L (X 2) * I) -
      L (C π) * ((L (X 0) * I) ^ 2 + L (X 0) * I + 1) -
      L (C π) * L (C b₄) * (L (X 2) * I) ^ 2)) * hI + (-(L (X 2) * I) ^ 3) * he

/-! ### The remaining coordinate functions -/

variable (t) in
lemma coordFrac_zero_zero : coordFrac (lin t) (lin_mem t) 0 0 =
    Away.map (linHom (lin t) (lin_mem t)) (X 0) (H₀ (O := O)) := by
  apply (show Function.Injective (algebraMap (Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 0)))
    (Localization.Away (linHom (lin t) (lin_mem t) (X 0)))) from val_injective _)
  simp only [HomogeneousLocalization.algebraMap_apply, val_map_H₀, val_away_mk, pow_one]

variable (t) in
lemma coordFrac_zero_one : coordFrac (lin t) (lin_mem t) 0 1 =
    1 + Away.map (linHom (lin t) (lin_mem t)) (X 0) (cst 0 t) *
      coordFrac (lin t) (lin_mem t) 0 2 := by
  apply (show Function.Injective (algebraMap (Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 0)))
    (Localization.Away (linHom (lin t) (lin_mem t) (X 0)))) from val_injective _)
  simp only [HomogeneousLocalization.algebraMap_apply, val_map_cst, val_away_mk, pow_one,
    val_add, val_mul, val_one]
  set s := linHom (lin t) (lin_mem t) (X 0)
  set L := algebraMap (MvPolynomial (Fin (2 + 1)) O) (Localization.Away s)
  set I := IsLocalization.Away.invSelf (S := Localization.Away s) s
  have hs : s = X 1 - C t * X 2 := by simp [s, lin_zero]
  have hI : (L (X 1) - L (C t) * L (X 2)) * I = 1 := by
    rw [← map_mul, ← map_sub, ← hs]
    exact IsLocalization.Away.mul_invSelf s
  linear_combination hI

variable (t) in
lemma coordFrac_one_zero : coordFrac (lin t) (lin_mem t) 1 0 = 1 := by
  apply (show Function.Injective (algebraMap (Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 1)))
    (Localization.Away (linHom (lin t) (lin_mem t) (X 1)))) from val_injective _)
  simp only [HomogeneousLocalization.algebraMap_apply, val_away_mk, pow_one, val_one]
  set s := linHom (lin t) (lin_mem t) (X 1)
  have hs : s = X 0 := by simp [s, lin_one]
  rw [← hs]
  exact IsLocalization.Away.mul_invSelf s

variable (t) in
lemma coordFrac_one_one : coordFrac (lin t) (lin_mem t) 1 1 =
    Away.map (linHom (lin t) (lin_mem t)) (X 1) (H₁ (O := O)) +
      Away.map (linHom (lin t) (lin_mem t)) (X 1) (cst 1 t) *
        coordFrac (lin t) (lin_mem t) 1 2 := by
  apply (show Function.Injective (algebraMap (Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 1)))
    (Localization.Away (linHom (lin t) (lin_mem t) (X 1)))) from val_injective _)
  simp only [HomogeneousLocalization.algebraMap_apply, val_map_H₁, val_map_cst, val_away_mk,
    pow_one, val_add, val_mul, map_sub, map_mul]
  ring

/-! ### The projection from `[0 : t : 1]` -/

instance isClosedImmersion_ι :
    IsClosedImmersion (X := (TateModel.modelIdeal π b₄ b₆).subscheme) (Y := Proj (𝒜 2))
      (TateModel.ι π b₄ b₆) :=
  inferInstanceAs (IsClosedImmersion (TateModel.modelIdeal π b₄ b₆).subschemeι)

variable (b₆) in
/-- **The projection `[v − t w : u] : 𝒯 ⟶ ℙ¹_O` from `[0 : t : 1]`** (for `t² − b₆` a unit). -/
def toP1 : (TateModel.modelIdeal π b₄ b₆).subscheme ⟶ projSpace O 1 :=
  proj (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) (hcov π b₄ hε)

/-- The projection lies over `Spec O`. -/
lemma toP1_toSpec : toP1 π b₄ b₆ hε ≫ projSpace.toSpec O 1 = (TateModel.model π b₄ b₆).toSpec :=
  proj_toSpec (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) (hcov π b₄ hε)

include hε in
lemma isIntegralElem_coordFrac (k : Fin (1 + 1)) (i : Fin (2 + 1)) :
    (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) k).IsIntegralElem
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) k (coordFrac (lin t) (lin_mem t) k i)) := by
  have hmap := isIntegralElem_secRes_awayMap (lin t) (lin_mem t) (TateModel.ι π b₄ b₆)
  have hF : ∀ z, TateModel.F π b₄ b₆ ∈ ((TateModel.ι π b₄ b₆) z).asHomogeneousIdeal :=
    TateModel.F_mem π b₄ b₆
  have hz₀ : (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0).IsIntegralElem
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (coordFrac (lin t) (lin_mem t) 0 2)) := by
    refine RingHom.isIntegralElem_of_monic_of_isNilpotent _ (monic_cubic₀ π b₄ hε) ?_
    rw [baseRes, ← Polynomial.hom_eval₂, eval_cubic₀, map_mul]
    exact (Commute.all _ _).isNilpotent_mul_left
      (isNilpotent_secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (F_mem3 π b₄ b₆) three_pos hF)
  have hz₁ : (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1).IsIntegralElem
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (coordFrac (lin t) (lin_mem t) 1 2)) := by
    refine RingHom.isIntegralElem_of_monic_of_isNilpotent _ (monic_cubic₁ π b₄ hε) ?_
    rw [baseRes, ← Polynomial.hom_eval₂, eval_cubic₁, map_mul]
    exact (Commute.all _ _).isNilpotent_mul_left
      (isNilpotent_secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (F_mem3 π b₄ b₆) three_pos hF)
  have h00 : (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0).IsIntegralElem
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (coordFrac (lin t) (lin_mem t) 0 0)) := by
    rw [coordFrac_zero_zero]
    exact hmap 0 _
  have h01 : (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0).IsIntegralElem
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (coordFrac (lin t) (lin_mem t) 0 1)) := by
    rw [coordFrac_zero_one, map_add, map_one, map_mul]
    have h1 := hmap 0 1
    rw [map_one, map_one] at h1
    exact RingHom.IsIntegralElem.add _ h1 (RingHom.IsIntegralElem.mul _ (hmap 0 _) hz₀)
  have h10 : (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1).IsIntegralElem
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (coordFrac (lin t) (lin_mem t) 1 0)) := by
    rw [coordFrac_one_zero, map_one]
    have h1 := hmap 1 1
    rwa [map_one, map_one] at h1
  have h11 : (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1).IsIntegralElem
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (coordFrac (lin t) (lin_mem t) 1 1)) := by
    rw [coordFrac_one_one, map_add, map_mul]
    exact RingHom.IsIntegralElem.add _ (hmap 1 _) (RingHom.IsIntegralElem.mul _ (hmap 1 _) hz₁)
  fin_cases k <;> fin_cases i
  exacts [h00, h01, hz₀, h10, h11, hz₁]

/-- **The projection is locally quasi-finite.** -/
instance locallyQuasiFinite_toP1 :
    LocallyQuasiFinite (X := (TateModel.model π b₄ b₆).scheme) (toP1 π b₄ b₆ hε) :=
  locallyQuasiFinite_proj (hcov π b₄ hε) (isIntegralElem_coordFrac π b₄ hε)

/-- **The projection from `[0 : t : 1]` is a finite morphism `𝒯 ⟶ ℙ¹_O`.** -/
instance isFinite_toP1 :
    IsFinite (X := (TateModel.model π b₄ b₆).scheme) (Y := ProjectiveLine.scheme O)
      (toP1 π b₄ b₆ hε) :=
  SemistableReduction.ModelChartAlgebra.isFinite_of_locallyQuasiFinite
    (TateModel.model π b₄ b₆) (toP1 π b₄ b₆ hε) (toP1_toSpec π b₄ hε)

variable (b₆) in
/-- **The Tate model is finite over `ℙ¹_O`** (`O` local): projection from `[0 : 0 : 1]` if `b₆`
is a unit, from `[0 : 1 : 1]` otherwise. -/
theorem exists_isFinite_toP1 [IsLocalRing O] :
    ∃ p : (TateModel.model π b₄ b₆).scheme ⟶ ProjectiveLine.scheme O,
      IsFinite p ∧ p ≫ projSpace.toSpec O 1 = (TateModel.model π b₄ b₆).toSpec := by
  have ht : ∃ t : O, IsUnit (t ^ 2 - b₆) := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self b₆ with h | h
    · exact ⟨0, by simpa using h.neg⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨t, hε⟩ := ht
  exact ⟨toP1 π b₄ b₆ hε, isFinite_toP1 π b₄ hε, toP1_toSpec π b₄ hε⟩

end

end TateProjection

end TemperedFundamentalGroups
