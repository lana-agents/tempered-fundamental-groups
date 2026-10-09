/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateModelNormal
import TemperedFundamentalGroups.SemistableReduction.ProjScheme

/-!
# Points of the Tate model with values in rings, through the chart `w = 1` (B3b)

For a ring `T` with `φ : O → T`, a point `(x, y)` of `y² + xy = x³ + π² b₄ x + π² b₆` and
`φ(π)` a unit, `tateHomR : O[X][Y]/(f) → T`, `X ↦ x/π`, `Y ↦ y/π`, and the induced point
`jChart : Spec T ⟶ projModelCode O (coords)` of the projective model of the Tate function field,
through the chart `w = 1` (`chart_two_eq`).
-/

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "L" => TateField π b₄ b₆

variable {T : Type u} [CommRing T] (φ : O →+* T) {x y : T}
  (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆)) (hπ : IsUnit (φ π))

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
include heq in
lemma eval₂_fpoly_unit :
    (fpoly π b₄ b₆).eval₂ (Polynomial.eval₂RingHom φ (x * ↑hπ.unit⁻¹)) (y * ↑hπ.unit⁻¹) = 0 := by
  rw [eval₂_fpoly]
  have hu : φ π * ↑hπ.unit⁻¹ = 1 := hπ.mul_val_inv
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, cpoly, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul, map_pow] at heq ⊢
  set v := (↑hπ.unit⁻¹ : T)
  linear_combination v ^ 2 * heq +
    (-(x ^ 3 * v ^ 2) + φ π * φ b₄ * x * v + φ b₆ * (φ π * v + 1)) * hu

/-- **The map `O[X][Y]/(f) → T`**, `X ↦ x/π`, `Y ↦ y/π`. -/
def tateHomR : TateRing π b₄ b₆ →+* T :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom φ (x * ↑hπ.unit⁻¹)) (y * ↑hπ.unit⁻¹)
    (eval₂_fpoly_unit π b₄ b₆ φ heq hπ)

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma tateHomR_C (o : O) : tateHomR π b₄ b₆ φ heq hπ (algebraMap O (TateRing π b₄ b₆) o) = φ o := by
  rw [IsScalarTower.algebraMap_apply O O[X] (TateRing π b₄ b₆), AdjoinRoot.algebraMap_eq,
    tateHomR, AdjoinRoot.lift_of]
  simp

/-- The chart `w = 1` is `O[X][Y]/(f)`. -/
def chartTwoEquiv : TateRing π b₄ b₆ ≃+* chart π b₄ b₆ 2 :=
  (RingEquiv.ofBijective (algebraMap (TateRing π b₄ b₆) L).rangeRestrict
    ⟨fun _ _ h ↦ IsFractionRing.injective (TateRing π b₄ b₆) L (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).trans
    (RingEquiv.subringCongr (chart_two_eq π b₄ b₆).symm)

lemma chartTwoEquiv_apply (r : TateRing π b₄ b₆) :
    ((chartTwoEquiv π b₄ b₆ r : chart π b₄ b₆ 2) : L) = algebraMap (TateRing π b₄ b₆) L r := by
  simp [chartTwoEquiv]

/-- **The ring map of the chart `w = 1` to `T`.** -/
def chartHomR : chart π b₄ b₆ 2 →+* T :=
  (tateHomR π b₄ b₆ φ heq hπ).comp (chartTwoEquiv π b₄ b₆).symm.toRingHom

open SemistableReduction.ProjScheme in
variable (hπ0 : π ≠ 0) in
/-- **The point `Spec T ⟶` (projective Tate model)** through the chart `w = 1`. -/
def jChart : Spec (CommRingCat.of T) ⟶ (projModelCode O (hcoords π b₄ b₆ hπ0)).scheme :=
  Spec.map (CommRingCat.ofHom (chartHomR π b₄ b₆ φ heq hπ)) ≫
    chartι (baseRing π b₄ b₆) rfl (hcoords π b₄ b₆ hπ0) 2

open SemistableReduction.ProjScheme in
variable (hπ0 : π ≠ 0) in
lemma jChart_toSpec :
    jChart π b₄ b₆ φ heq hπ hπ0 ≫ (projModelCode O (hcoords π b₄ b₆ hπ0)).toSpec =
      Spec.map (CommRingCat.ofHom φ) := by
  rw [jChart, Category.assoc, chartι_toSpec, ← Spec.map_comp]
  congr 1
  have key : ∀ (o : O) (z : chart π b₄ b₆ 2), (z : L) = algebraMap O L o →
      chartHomR π b₄ b₆ φ heq hπ z = φ o := by
    intro o z hz
    obtain ⟨r, rfl⟩ := (chartTwoEquiv π b₄ b₆).surjective z
    rw [chartTwoEquiv_apply, IsScalarTower.algebraMap_apply O (TateRing π b₄ b₆) L] at hz
    rw [IsFractionRing.injective (TateRing π b₄ b₆) L hz]
    simp only [chartHomR, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, RingEquiv.symm_apply_apply]
    exact tateHomR_C π b₄ b₆ φ heq hπ o
  refine CommRingCat.hom_ext (RingHom.ext fun o ↦ key o _ rfl)

end

end TemperedFundamentalGroups.TateNormal
