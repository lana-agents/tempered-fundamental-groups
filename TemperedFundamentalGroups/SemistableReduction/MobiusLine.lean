/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.LinearCombination

/-!
# The Möbius re-charting of the line (MR13 step 7, D1 (S5), generic over a field)

The line `ℓ` of the special fibre of the Tate curve has coordinate `h'`, nodes at `h' = 0, −1`
and the cusp at `h' = ∞`; the chart `V₁ = ℙ¹ ∖ {0, 1, ā}` of `P1Three` has coordinate
`s = 1/t` and is the localized line `F[s, 1/((1 − s)(1 − ā s))]` (`P1Three.lineEquiv`). The Möbius
map `t = ā h'/(h' + 1 − ā)`, i.e. `s = (h' + 1 − ā)/(ā h')`, sends `h' = 0 ↦ t = 0`,
`h' = −1 ↦ t = 1`, `h' = ∞ ↦ t = ā`, and identifies the two charts:

* **`MobiusLine.equiv`**: `F[s, 1/((1 − s)(1 − a s))] ≃ₐ[F] F[h, 1/(h (h + 1))]` for `a ≠ 0, 1`,
  with **`equiv_s`**: `s ↦ (h + 1 − a) · (a h)⁻¹` and **`equiv_symm_h`**:
  `h ↦ (a − 1) · (1 − a s)⁻¹`.

(`1 − s = (a − 1)(h + 1)/(a h)` and `1 − a s = (a − 1)/h`, so both sides invert the same
functions.)
-/

open Polynomial

namespace SemistableReduction

namespace MobiusLine

noncomputable section

variable {F : Type*} [Field F] (a : F)

/-- `q(s) = (1 − s)(1 − a s)`. -/
def q : F[X] := (1 - X) * (1 - C a * X)

variable (F) in
/-- `p(h) = h (h + 1)`. -/
def p : F[X] := X * (X + 1)

/-- The source chart `F[s, 1/q(s)]`. -/
abbrev A : Type _ := Localization.Away (q a)

variable (F) in
/-- The target chart `F[h, 1/p(h)]`. -/
abbrev B : Type _ := Localization.Away (p F)

/-- `s ∈ A`. -/
abbrev sA : A a := algebraMap F[X] (A a) X

variable (F) in
/-- `h ∈ B`. -/
abbrev hB : B F := algebraMap F[X] (B F) X

variable (F) in
lemma isUnit_hB : IsUnit (hB F) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := B F) (p F)
  change IsUnit (algebraMap F[X] (B F) (X * (X + 1))) at this
  rw [map_mul] at this
  exact isUnit_of_mul_isUnit_left this

variable (F) in
lemma isUnit_hB1 : IsUnit (hB F + 1) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := B F) (p F)
  change IsUnit (algebraMap F[X] (B F) (X * (X + 1))) at this
  rw [map_mul, map_add, map_one] at this
  exact isUnit_of_mul_isUnit_right this

lemma isUnit_one_sub_as : IsUnit (1 - algebraMap F (A a) a * sA a) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := A a) (q a)
  change IsUnit (algebraMap F[X] (A a) ((1 - X) * (1 - C a * X))) at this
  have hC : algebraMap F[X] (A a) (C a) = algebraMap F (A a) a := by
    rw [IsScalarTower.algebraMap_apply F F[X] (A a), Polynomial.algebraMap_eq]
  rw [map_mul, map_sub, map_sub, map_one, map_mul, hC] at this
  exact isUnit_of_mul_isUnit_right this

lemma isUnit_one_sub_s : IsUnit (1 - sA a) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := A a) (q a)
  change IsUnit (algebraMap F[X] (A a) ((1 - X) * (1 - C a * X))) at this
  rw [map_mul, map_sub, map_one] at this
  exact isUnit_of_mul_isUnit_left this

variable (F) in
/-- `h⁻¹ ∈ B`. -/
def hInv : B F := ((isUnit_hB F).unit⁻¹ : (B F)ˣ)

/-- `(1 − a s)⁻¹ ∈ A`. -/
def uInv : A a := ((isUnit_one_sub_as a).unit⁻¹ : (A a)ˣ)

variable (F) in
lemma hB_mul_inv : hB F * hInv F = 1 := (isUnit_hB F).mul_val_inv

lemma A_mul_inv : (1 - algebraMap F (A a) a * sA a) * uInv a = 1 :=
  (isUnit_one_sub_as a).mul_val_inv

lemma isUnit_hInv : IsUnit (hInv F) := ((isUnit_hB F).unit⁻¹).isUnit

lemma isUnit_uInv : IsUnit (uInv a) := ((isUnit_one_sub_as a).unit⁻¹).isUnit

/-- The image of `s` in `B`: `(h + 1 − a) · a⁻¹ · h⁻¹`. -/
def sImg : B F := (hB F + 1 - algebraMap F (B F) a) * algebraMap F (B F) a⁻¹ * hInv F

/-- The image of `h` in `A`: `(a − 1) · (1 − a s)⁻¹`. -/
def hImg : A a := algebraMap F (A a) (a - 1) * uInv a

/-- The polynomial map `F[s] → B`, `s ↦ sImg`. -/
def fwd0 : F[X] →+* B F := (Polynomial.aeval (R := F) (sImg a)).toRingHom

/-- The polynomial map `F[h] → A`, `h ↦ hImg`. -/
def bwd0 : F[X] →+* A a := (Polynomial.aeval (R := F) (hImg a)).toRingHom

lemma fwd0_X : fwd0 a X = sImg a := by simp [fwd0]

lemma bwd0_X : bwd0 a X = hImg a := by simp [bwd0]

lemma fwd0_C (c : F) : fwd0 a (C c) = algebraMap F (B F) c := by simp [fwd0]

lemma bwd0_C (c : F) : bwd0 a (C c) = algebraMap F (A a) c := by simp [bwd0]

lemma algebraMap_inv_mul {R : Type*} [CommRing R] [Algebra F R] {c : F} (hc : c ≠ 0) :
    algebraMap F R c⁻¹ * algebraMap F R c = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hc, map_one]

lemma isUnit_algebraMap {R : Type*} [CommRing R] [Algebra F R] [Nontrivial R] {c : F}
    (hc : c ≠ 0) : IsUnit (algebraMap F R c) :=
  (IsUnit.mk0 c hc).map (algebraMap F R)

variable {a}

/-- `1 − s ↦ (a − 1)(h + 1) a⁻¹ h⁻¹`. -/
lemma one_sub_sImg (ha0 : a ≠ 0) : 1 - sImg a = algebraMap F (B F) (a - 1) * (hB F + 1) *
    algebraMap F (B F) a⁻¹ * hInv F := by
  have e1 := hB_mul_inv F
  have e2 := algebraMap_inv_mul (R := B F) ha0
  simp only [sImg, map_sub, map_one]
  linear_combination (-(algebraMap F (B F) a) * algebraMap F (B F) a⁻¹) * e1 - e2

/-- `1 − a s ↦ (a − 1) h⁻¹`. -/
lemma one_sub_a_sImg (ha0 : a ≠ 0) : 1 - algebraMap F (B F) a * sImg a =
    algebraMap F (B F) (a - 1) * hInv F := by
  have e1 := hB_mul_inv F
  have e2 := algebraMap_inv_mul (R := B F) ha0
  simp only [sImg, map_sub, map_one]
  linear_combination (-(algebraMap F (B F) a) * algebraMap F (B F) a⁻¹) * e1 +
    (algebraMap F (B F) a * hInv F - hInv F - 1) * e2

/-- `h + 1 ↦ a (1 − s)(1 − a s)⁻¹`. -/
lemma hImg_add_one : hImg a + 1 = algebraMap F (A a) a * (1 - sA a) * uInv a := by
  have e1 := A_mul_inv a
  simp only [hImg, map_sub, map_one]
  linear_combination -e1

lemma nontrivial_B : Nontrivial (B F) := by
  have hp : p F ≠ 0 := by
    change X * (X + 1) ≠ (0 : F[X])
    exact mul_ne_zero X_ne_zero (by simpa using X_add_C_ne_zero (1 : F))
  haveI : IsDomain (B F) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hp)
  infer_instance

lemma nontrivial_A (ha0 : a ≠ 0) : Nontrivial (A a) := by
  have hq : q a ≠ 0 := by
    unfold q
    refine mul_ne_zero ?_ ?_
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp [coeff_one] at this
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp [coeff_one, ha0] at this
  haveI : IsDomain (A a) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hq)
  infer_instance

variable (ha0 : a ≠ 0) (ha1 : a ≠ 1)
include ha0 ha1

lemma isUnit_fwd0_q : IsUnit (fwd0 a (q a)) := by
  haveI := nontrivial_B (F := F)
  have h1 : (a - 1 : F) ≠ 0 := sub_ne_zero.mpr ha1
  have hai : (a⁻¹ : F) ≠ 0 := inv_ne_zero ha0
  rw [show q a = (1 - X) * (1 - C a * X) from rfl]
  rw [map_mul, map_sub, map_sub, map_one, map_mul, fwd0_X, fwd0_C, one_sub_sImg ha0,
    one_sub_a_sImg ha0]
  exact ((((isUnit_algebraMap h1).mul (isUnit_hB1 F)).mul (isUnit_algebraMap hai)).mul
    isUnit_hInv).mul ((isUnit_algebraMap h1).mul isUnit_hInv)

lemma isUnit_bwd0_p : IsUnit (bwd0 a (p F)) := by
  haveI := nontrivial_A ha0
  have h1 : (a - 1 : F) ≠ 0 := sub_ne_zero.mpr ha1
  rw [show p F = X * (X + 1) from rfl]
  rw [map_mul, map_add, map_one, bwd0_X, hImg_add_one]
  exact ((isUnit_algebraMap h1).mul (isUnit_uInv a)).mul
    (((isUnit_algebraMap ha0).mul (isUnit_one_sub_s a)).mul (isUnit_uInv a))

/-- The forward map `F[s, 1/q] → F[h, 1/p]`. -/
def fwd : A a →+* B F := IsLocalization.Away.lift (q a) (isUnit_fwd0_q ha0 ha1)

/-- The backward map `F[h, 1/p] → F[s, 1/q]`. -/
def bwd : B F →+* A a := IsLocalization.Away.lift (p F) (isUnit_bwd0_p ha0 ha1)

lemma fwd_algebraMap (x : F[X]) : fwd ha0 ha1 (algebraMap F[X] (A a) x) = fwd0 a x :=
  IsLocalization.Away.lift_eq _ _ x

lemma bwd_algebraMap (x : F[X]) : bwd ha0 ha1 (algebraMap F[X] (B F) x) = bwd0 a x :=
  IsLocalization.Away.lift_eq _ _ x

lemma fwd_F (c : F) : fwd ha0 ha1 (algebraMap F (A a) c) = algebraMap F (B F) c := by
  rw [IsScalarTower.algebraMap_apply F F[X] (A a), fwd_algebraMap, Polynomial.algebraMap_eq,
    fwd0_C]

lemma bwd_F (c : F) : bwd ha0 ha1 (algebraMap F (B F) c) = algebraMap F (A a) c := by
  rw [IsScalarTower.algebraMap_apply F F[X] (B F), bwd_algebraMap,
    Polynomial.algebraMap_eq, bwd0_C]

lemma bwd_fwd : (bwd ha0 ha1).comp (fwd ha0 ha1) = RingHom.id (A a) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (q a)) (Polynomial.ringHom_ext
    (fun c ↦ ?_) ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← Polynomial.algebraMap_eq (R := F), ← IsScalarTower.algebraMap_apply, fwd_F, bwd_F]
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [fwd_algebraMap, fwd0_X]
    set w := bwd ha0 ha1 (hInv F)
    have e2 : hImg a * w = 1 := by
      have := congrArg (bwd ha0 ha1) (hB_mul_inv F)
      rwa [map_mul, bwd_algebraMap, bwd0_X, map_one] at this
    have e1 := A_mul_inv a
    have e3 := algebraMap_inv_mul (R := A a) ha0
    have hs : bwd ha0 ha1 (sImg a) =
        (hImg a + 1 - algebraMap F (A a) a) * algebraMap F (A a) a⁻¹ * w := by
      simp only [sImg, map_mul, map_sub, map_add, map_one, bwd_F, w]
      rw [bwd_algebraMap, bwd0_X]
    rw [hs]
    simp only [hImg, map_sub, map_one] at e2 ⊢
    linear_combination (algebraMap F (A a) a⁻¹ * w * (algebraMap F (A a) a - 1)) * e1 +
      (algebraMap F (A a) a * algebraMap F (A a) a⁻¹ * sA a) * e2 + sA a * e3

lemma fwd_bwd : (fwd ha0 ha1).comp (bwd ha0 ha1) = RingHom.id (B F) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (p F)) (Polynomial.ringHom_ext
    (fun c ↦ ?_) ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← Polynomial.algebraMap_eq (R := F), ← IsScalarTower.algebraMap_apply, bwd_F, fwd_F]
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [bwd_algebraMap, bwd0_X]
    set w := fwd ha0 ha1 (uInv a)
    have e1 : (1 - algebraMap F (B F) a * sImg a) * w = 1 := by
      have := congrArg (fwd ha0 ha1) (A_mul_inv a)
      rwa [map_mul, map_sub, map_one, map_mul, fwd_F, fwd_algebraMap, fwd0_X] at this
    have e2 := hB_mul_inv F
    have e3 := algebraMap_inv_mul (R := B F) ha0
    have hh : fwd ha0 ha1 (hImg a) = algebraMap F (B F) (a - 1) * w := by
      rw [hImg, map_mul, fwd_F]
    rw [hh]
    simp only [sImg, map_sub, map_one] at e1 ⊢
    linear_combination hB F * e1 -
      (algebraMap F (B F) a * algebraMap F (B F) a⁻¹ * w *
        (algebraMap F (B F) a - hB F - 1)) * e2 -
      (w * (algebraMap F (B F) a - hB F - 1)) * e3

/-- **The Möbius re-charting** `F[s, 1/((1 − s)(1 − a s))] ≃ₐ[F] F[h, 1/(h (h + 1))]`,
`s ↦ (h + 1 − a)/(a h)` (`t = 1/s = a h/(h + 1 − a)`). -/
def equiv : A a ≃ₐ[F] B F :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (fwd ha0 ha1) (bwd ha0 ha1)
    (fwd_bwd ha0 ha1) (bwd_fwd ha0 ha1)) (fwd_F ha0 ha1)

lemma equiv_s : equiv ha0 ha1 (sA a) = sImg a := by
  change fwd ha0 ha1 (algebraMap F[X] (A a) X) = _
  rw [fwd_algebraMap, fwd0_X]

lemma equiv_symm_h : (equiv ha0 ha1).symm (hB F) = hImg a := by
  change bwd ha0 ha1 (algebraMap F[X] (B F) X) = _
  rw [bwd_algebraMap, bwd0_X]

end

end MobiusLine

end SemistableReduction
