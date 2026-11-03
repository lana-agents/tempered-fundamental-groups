/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeDedekind

/-!
# The chart `V₁ = ℙ¹ ∖ {0, 1, a}` of the `P1Three` model as a localized line (MR13 A1, (f) step 2)

The chart ring `R1 = O[Y][s]/(s³ − a Y s² + (1 + a) Y s − Y)` of `ℙ¹_t ∖ {0, 1, a}` (`s = 1/t`,
`Y = s³/((1 − s)(1 − a s))`, `P1ThreeChart`) is the localized line in the coordinate `s`:

* **`P1Three.lineEquiv : R1 O a ≃ₐ[O] O[s][1/((1 − s)(1 − a s))]`** (`s ↦ s`,
  `Y ↦ s³/((1 − s)(1 − a s))`), `lineEquiv_s1`, `lineEquiv_y1`;
* over a field `K` with `a ≠ 0`: **`P1Three.lineEquivK : R1 K a ≃ₐ[K]
  K[s][1/((s − 1)(s − a⁻¹))]`** (`s ↦ s`), the coordinate ring of `ℙ¹_K ∖ {1, a⁻¹, ∞}` in the
  coordinate `s` (the cusps `t = 1, a, 0` are `s = 1, a⁻¹, ∞`);
* **`P1Three.awayLineEquiv`**: for `K = O[1/ϖ]` a field, `R1[1/ϖ] ≃ K[s][1/((s − 1)(s − a⁻¹))]`
  (with `awayEquiv1`), the coordinate ring of the generic fibre `U_K` of `V₁` as a localized line.

This is the presentation through which the generic fibre of the lift of a tame cover of
`ℙ¹_k ∖ {0, 1, ā}` (`P1ThreeEtale.etale_lift`) is compared with the covers of the line
`k[t, 1/P_S(t)]` of curves-jacobian in iut.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace P1Three

noncomputable section

variable (O : Type u) [CommRing O] (a : O)

/-- `q(s) = (1 − s)(1 − a s) ∈ O[s]`. -/
def qS : O[X] := (1 - X) * (1 - C a * X)

/-- **The localized line `O[s, 1/q(s)]`**, `q(s) = (1 − s)(1 − a s)`. -/
abbrev LineR : Type u := Localization.Away (qS O a)

/-- The coordinate `s` of the localized line. -/
abbrev sL : LineR O a := algebraMap O[X] (LineR O a) X

/-- `1/q(s)` in the localized line. -/
abbrev qInv : LineR O a := IsLocalization.Away.invSelf (qS O a)

/-- `Y = s³/q(s)` in the localized line. -/
abbrev yL : LineR O a := sL O a ^ 3 * qInv O a

lemma algebraMap_qS : algebraMap O[X] (LineR O a) (qS O a) =
    (1 - sL O a) * (1 - algebraMap O (LineR O a) a * sL O a) := by
  rw [show algebraMap O[X] (LineR O a) (qS O a) =
      algebraMap O[X] (LineR O a) ((1 - X) * (1 - C a * X)) from rfl,
    IsScalarTower.algebraMap_apply O O[X] (LineR O a), Polynomial.algebraMap_eq]
  simp only [map_mul, map_sub, map_one]

lemma q_mul_qInv : (1 - sL O a) * (1 - algebraMap O (LineR O a) a * sL O a) * qInv O a = 1 := by
  rw [← algebraMap_qS]
  exact IsLocalization.Away.mul_invSelf (qS O a)

/-- `R1 → O[s, 1/q(s)]`, `Y ↦ s³/q(s)`, `s ↦ s`. -/
def toLine : R1 O a →+* LineR O a :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap O (LineR O a)) (yL O a)) (sL O a) (by
    have h := q_mul_qInv O a
    simp only [G1, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      coe_eval₂RingHom, map_add, map_one, eval₂_one]
    linear_combination (-(sL O a) ^ 3) * h)

lemma toLine_s1 : toLine O a (s1 O a) = sL O a :=
  AdjoinRoot.lift_root _

lemma toLine_y1 : toLine O a (y1 O a) = yL O a := by
  rw [y1, toLine, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

lemma toLine_algebraMap (o : O) : toLine O a (algebraMap O (R1 O a) o) = algebraMap O _ o := by
  rw [← of_C, toLine, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]

lemma isUnit_q_s1 : IsUnit (eval₂ (algebraMap O (R1 O a)) (s1 O a) (qS O a)) := by
  have h : eval₂ (algebraMap O (R1 O a)) (s1 O a) (qS O a) =
      (1 - s1 O a) * (1 - algebraMap O (R1 O a) a * s1 O a) := by
    simp only [qS, eval₂_mul, eval₂_sub, eval₂_one, eval₂_X, eval₂_C]
  rw [h]
  exact (IsUnit.of_mul_eq_one _ (one_sub_s1_mul O a)).mul
    (IsUnit.of_mul_eq_one _ (one_sub_a_s1_mul O a))

/-- `O[s, 1/q(s)] → R1`, `s ↦ s` (`q(s)` is a unit of `R1`). -/
def fromLine : LineR O a →+* R1 O a :=
  IsLocalization.Away.lift (qS O a) (g := eval₂RingHom (algebraMap O (R1 O a)) (s1 O a))
    (isUnit_q_s1 O a)

lemma fromLine_algebraMap (p : O[X]) :
    fromLine O a (algebraMap O[X] (LineR O a) p) = eval₂ (algebraMap O (R1 O a)) (s1 O a) p :=
  IsLocalization.Away.lift_eq _ _ p

lemma fromLine_sL : fromLine O a (sL O a) = s1 O a := by
  rw [fromLine_algebraMap, eval₂_X]

lemma fromLine_algebraMapO (o : O) :
    fromLine O a (algebraMap O (LineR O a) o) = algebraMap O (R1 O a) o := by
  rw [IsScalarTower.algebraMap_apply O O[X] (LineR O a), fromLine_algebraMap,
    Polynomial.algebraMap_eq, eval₂_C]

lemma fromLine_comp_toLine : (fromLine O a).comp (toLine O a) = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun o ↦ ?_) ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [of_C, toLine_algebraMap, fromLine_algebraMapO]
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    change fromLine O a (toLine O a (y1 O a)) = y1 O a
    have hq := congrArg (fromLine O a) (q_mul_qInv O a)
    have h1 := eq1 O a
    simp only [map_mul, map_sub, map_one, fromLine_sL, fromLine_algebraMapO] at hq
    rw [toLine_y1, yL, map_mul, map_pow, fromLine_sL]
    rw [map_add, map_one] at h1
    linear_combination (y1 O a) * hq + (fromLine O a (qInv O a)) * h1
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [toLine_s1, fromLine_sL]

lemma toLine_comp_fromLine : (toLine O a).comp (fromLine O a) = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (qS O a))
    (Polynomial.ringHom_ext (fun o ↦ ?_) ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [fromLine_algebraMap, eval₂_C, toLine_algebraMap,
      IsScalarTower.algebraMap_apply O O[X] (LineR O a), Polynomial.algebraMap_eq]
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [fromLine_algebraMap, eval₂_X, toLine_s1]

/-- **`R1 ≃ O[s, 1/((1 − s)(1 − a s))]`** (`s ↦ s`, `Y ↦ s³/((1 − s)(1 − a s))`): the chart
`V₁ = ℙ¹_t ∖ {0, 1, a}` is the localized line in the coordinate `s = 1/t`. -/
def lineEquiv : R1 O a ≃ₐ[O] LineR O a :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (toLine O a) (fromLine O a)
    (toLine_comp_fromLine O a) (fromLine_comp_toLine O a)) (toLine_algebraMap O a)

lemma lineEquiv_s1 : lineEquiv O a (s1 O a) = sL O a :=
  toLine_s1 O a

lemma lineEquiv_y1 : lineEquiv O a (y1 O a) = yL O a :=
  toLine_y1 O a

/-! ### Over a field -/

section Field

variable {K : Type u} [Field K] (a : K)

/-- `(s − 1)(s − a⁻¹) ∈ K[s]`. -/
def pS : K[X] := (X - 1) * (X - C a⁻¹)

lemma associated_qS (ha : a ≠ 0) : Associated (qS K a) (pS a) := by
  have hC : C a * C a⁻¹ = (1 : K[X]) := by rw [← C_mul, mul_inv_cancel₀ ha, C_1]
  have h : qS K a = pS a * C a := by
    rw [qS, pS]
    linear_combination (X - 1) * hC
  rw [h]
  exact associated_mul_unit_left _ _ (isUnit_C.2 (isUnit_iff_ne_zero.2 ha))

/-- **`R1 ≃ K[s, 1/((s − 1)(s − a⁻¹))]` over a field `K`** (`a ≠ 0`, `s ↦ s`): the coordinate ring
of `ℙ¹_K ∖ {1, a⁻¹, ∞}` in the coordinate `s = 1/t`. -/
def lineEquivK (ha : a ≠ 0) : R1 K a ≃ₐ[K] Localization.Away (pS a) :=
  haveI : IsLocalization.Away (pS a) (LineR K a) :=
    IsLocalization.Away.of_associated (associated_qS a ha)
  (lineEquiv K a).trans
    ((IsLocalization.algEquiv (Submonoid.powers (pS a)) (LineR K a)
      (Localization.Away (pS a))).restrictScalars K)

lemma lineEquivK_s1 (ha : a ≠ 0) :
    lineEquivK a ha (s1 K a) = algebraMap K[X] (Localization.Away (pS a)) X := by
  haveI : IsLocalization.Away (pS a) (LineR K a) :=
    IsLocalization.Away.of_associated (associated_qS a ha)
  change IsLocalization.algEquiv (Submonoid.powers (pS a)) (LineR K a)
    (Localization.Away (pS a)) (lineEquiv K a (s1 K a)) = _
  rw [lineEquiv_s1]
  exact (IsLocalization.algEquiv (Submonoid.powers (pS a)) (LineR K a)
    (Localization.Away (pS a))).commutes X

end Field

/-! ### The generic fibre of `V₁` -/

variable {O} {ϖ : O} (hϖ : ϖ ≠ 0) [IsDomain O]

include hϖ in
/-- **`R1[1/ϖ] ≃ K[s, 1/((s − 1)(s − a⁻¹))]`** for `K = O[1/ϖ]` a field and `a` a unit of `K`:
the generic fibre `U_K` of the chart `V₁` is the line `ℙ¹_K ∖ {1, a⁻¹, ∞}` (coordinate
`s = 1/t`). -/
def awayLineEquiv (K : Type u) [Field K] [Algebra O K] [IsLocalization.Away ϖ K]
    (ha : algebraMap O K a ≠ 0) :
    Localization.Away (algebraMap O (R1 O a) ϖ) ≃+* Localization.Away (pS (algebraMap O K a)) :=
  (awayEquiv1 hϖ K a).trans (lineEquivK (algebraMap O K a) ha).toRingEquiv

end

end P1Three

end SemistableReduction
