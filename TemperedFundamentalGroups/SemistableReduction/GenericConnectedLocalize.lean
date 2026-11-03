/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.GenericConnectedBaseChange
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The generic fibre of a base change as a tensor product over the base (generic; MR13, (f) step 3)

For a ring map `R → R'` and an `R[X]`-algebra `B` (with `R → R[X] → B`):

* **`GenericConnected.polyCancel : R'[X] ⊗_{R[X]} B ≃ R' ⊗_R B`** (`p ⊗ b ↦ p(1 ⊗ X) · (1 ⊗ b)`,
  inverse `r ⊗ b ↦ C r ⊗ b`), `polyCancel_symm_tmul`;
* for `E = R'[1/π']`: **`isLocalization_tensor`** (`E ⊗_R B` is the localization of
  `R'[X] ⊗_{R[X]} B` away from `C π'`, through `polyCancel` and
  `IsLocalization.tensorProduct_tensorProduct`);
* **`eq_zero_or_eq_one_tensor`**: if every localization of `R'[X] ⊗_{R[X]} B` away from `C π'` has
  only the trivial idempotents, so has `E ⊗_R B`.

With `B = B₁` (the lift of a tame cover over `V₁`, an `O[X]`-algebra) and `E = K'` a finite
extension of `K = O[1/ϖ]` with ring of integers `O'`, this identifies the object of
`P1Three.connected_lift_baseChange` with the base change `K' ⊗_O B₁ = K' ⊗_K B₁[1/ϖ]` of the
generic fibre.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace GenericConnected

noncomputable section

variable {R R' B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing B] [Algebra R B]
  [Algebra R[X] B] [IsScalarTower R R[X] B]

/-- `R' ⊗_R B` over `R[X]` through `B`. -/
@[reducible] def algXT : Algebra R[X] (R' ⊗[R] B) :=
  (Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R[X] B)).toAlgebra

/-- `R'[X] → R' ⊗_R B`, `X ↦ 1 ⊗ X`. -/
def polyToT : R'[X] →+* R' ⊗[R] B :=
  eval₂RingHom Algebra.TensorProduct.includeLeftRingHom
    ((1 : R') ⊗ₜ[R] algebraMap R[X] B X)

omit [IsScalarTower R R[X] B] in
lemma polyToT_C (r : R') : polyToT (R := R) (B := B) (C r) = r ⊗ₜ[R] (1 : B) := by
  simp [polyToT]

lemma polyToT_map (p : R[X]) :
    polyToT (R := R) (B := B) (p.map (algebraMap R R')) = (1 : R') ⊗ₜ[R] algebraMap R[X] B p := by
  have h : (polyToT (R := R) (B := B)).comp (mapRingHom (algebraMap R R')) =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R[X] B) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, coe_mapRingHom, map_C, polyToT_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [show (C a : R[X]) = algebraMap R R[X] a from rfl,
        ← IsScalarTower.algebraMap_apply R R[X] B a, ← Algebra.TensorProduct.algebraMap_apply',
        Algebra.TensorProduct.algebraMap_apply]
    · simp [polyToT]
  exact RingHom.congr_fun h p

/-- `R'[X] → R' ⊗_R B` as a map of `R[X]`-algebras. -/
def polyToTAlg : letI := algPoly (R := R) (R' := R'); letI := algXT (R := R) (R' := R') (B := B)
    R'[X] →ₐ[R[X]] R' ⊗[R] B :=
  letI := algPoly (R := R) (R' := R')
  letI := algXT (R := R) (R' := R') (B := B)
  { polyToT (R := R) (B := B) with commutes' := fun p ↦ polyToT_map p }

/-- `B → R' ⊗_R B` as a map of `R[X]`-algebras. -/
def incRX : letI := algXT (R := R) (R' := R') (B := B); B →ₐ[R[X]] R' ⊗[R] B :=
  letI := algXT (R := R) (R' := R') (B := B)
  { (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B).toRingHom with
    commutes' := fun _ ↦ rfl }

/-- The forward map `R'[X] ⊗_{R[X]} B → R' ⊗_R B`. -/
def polyCancelFwd : letI := algPoly (R := R) (R' := R')
    R'[X] ⊗[R[X]] B →+* R' ⊗[R] B :=
  letI := algPoly (R := R) (R' := R')
  letI := algXT (R := R) (R' := R') (B := B)
  (Algebra.TensorProduct.lift polyToTAlg incRX fun _ _ ↦ Commute.all _ _).toRingHom

omit [Algebra R B] in
/-- `R[X]` and `R` act compatibly on `R'[X]` (so `R'[X] ⊗_{R[X]} B` is an `R`-algebra,
`Algebra.TensorProduct.leftAlgebra`). -/
lemma smulCommRX : letI := algPoly (R := R) (R' := R'); SMulCommClass R[X] R R'[X] := by
  letI := algPoly (R := R) (R' := R')
  exact ⟨fun p r q ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    ring⟩

/-- `R' → R'[X] ⊗_{R[X]} B`, `r ↦ C r ⊗ 1`. -/
def incLeftC : letI := algPoly (R := R) (R' := R'); haveI := smulCommRX (R := R) (R' := R')
    R' →ₐ[R] R'[X] ⊗[R[X]] B :=
  letI := algPoly (R := R) (R' := R')
  haveI := smulCommRX (R := R) (R' := R')
  { Algebra.TensorProduct.includeLeftRingHom.comp (C : R' →+* R'[X]) with
    commutes' := fun a ↦ by
      rw [Algebra.TensorProduct.algebraMap_apply, Polynomial.algebraMap_apply]
      rfl }

/-- `B → R'[X] ⊗_{R[X]} B` over `R`. -/
def incRightR : letI := algPoly (R := R) (R' := R'); haveI := smulCommRX (R := R) (R' := R')
    B →ₐ[R] R'[X] ⊗[R[X]] B :=
  letI := algPoly (R := R) (R' := R')
  haveI := smulCommRX (R := R) (R' := R')
  { toFun := fun b ↦ (1 : R'[X]) ⊗ₜ[R[X]] b
    map_one' := rfl
    map_mul' := fun b b' ↦ by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    map_zero' := TensorProduct.tmul_zero _ _
    map_add' := fun b b' ↦ TensorProduct.tmul_add _ _ _
    commutes' := fun a ↦ by
      change (1 : R'[X]) ⊗ₜ[R[X]] algebraMap R B a = _
      rw [Algebra.TensorProduct.algebraMap_apply, Polynomial.algebraMap_apply,
        IsScalarTower.algebraMap_apply R R[X] B a, ← Algebra.TensorProduct.algebraMap_apply',
        Algebra.TensorProduct.algebraMap_apply]
      change (map (algebraMap R R') (C a)) ⊗ₜ[R[X]] (1 : B) = _
      rw [Polynomial.map_C] }

/-- The inverse map `R' ⊗_R B → R'[X] ⊗_{R[X]} B`. -/
def polyCancelBwd : letI := algPoly (R := R) (R' := R')
    R' ⊗[R] B →+* R'[X] ⊗[R[X]] B :=
  letI := algPoly (R := R) (R' := R')
  haveI := smulCommRX (R := R) (R' := R')
  (Algebra.TensorProduct.lift incLeftC incRightR fun _ _ ↦ Commute.all _ _).toRingHom

lemma polyCancelBwd_tmul (r : R') (b : B) : letI := algPoly (R := R) (R' := R')
    polyCancelBwd (r ⊗ₜ[R] b) = (C r : R'[X]) ⊗ₜ[R[X]] b := by
  letI := algPoly (R := R) (R' := R')
  change (C r : R'[X]) ⊗ₜ[R[X]] (1 : B) * (1 : R'[X]) ⊗ₜ[R[X]] b = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

lemma polyCancelFwd_tmul (p : R'[X]) (b : B) : letI := algPoly (R := R) (R' := R')
    polyCancelFwd (p ⊗ₜ[R[X]] b) = polyToT p * (1 : R') ⊗ₜ[R] b :=
  rfl

lemma polyCancelBwd_polyToT (p : R'[X]) : letI := algPoly (R := R) (R' := R')
    polyCancelBwd (polyToT (R := R) (B := B) p) = p ⊗ₜ[R[X]] (1 : B) := by
  letI := algPoly (R := R) (R' := R')
  have h : (polyCancelBwd (R := R) (R' := R') (B := B)).comp polyToT =
      Algebra.TensorProduct.includeLeftRingHom := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · rw [RingHom.comp_apply, polyToT_C, polyCancelBwd_tmul]
      rfl
    · rw [RingHom.comp_apply]
      rw [show polyToT (R := R) (B := B) X = (1 : R') ⊗ₜ[R] algebraMap R[X] B X by
        simp [polyToT], polyCancelBwd_tmul, map_one, ← Algebra.TensorProduct.algebraMap_apply',
        Algebra.TensorProduct.algebraMap_apply]
      change (map (algebraMap R R') X) ⊗ₜ[R[X]] (1 : B) = _
      rw [Polynomial.map_X]
      rfl
  exact RingHom.congr_fun h p

/-- **`R'[X] ⊗_{R[X]} B ≃ R' ⊗_R B`.** -/
def polyCancel : letI := algPoly (R := R) (R' := R')
    R'[X] ⊗[R[X]] B ≃+* R' ⊗[R] B :=
  letI := algPoly (R := R) (R' := R')
  RingEquiv.ofRingHom polyCancelFwd polyCancelBwd
    (by
      refine RingHom.ext fun x ↦ ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r b =>
        simp only [RingHom.comp_apply, polyCancelBwd_tmul, polyCancelFwd_tmul, polyToT_C,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, RingHom.id_apply]
      | add x y hx hy => rw [map_add, hx, hy, map_add])
    (by
      refine RingHom.ext fun x ↦ ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul p b =>
        simp only [RingHom.comp_apply, polyCancelFwd_tmul, map_mul, polyCancelBwd_polyToT,
          polyCancelBwd_tmul, Algebra.TensorProduct.tmul_mul_tmul, C_1, mul_one, one_mul,
          RingHom.id_apply]
      | add x y hx hy => rw [map_add, hx, hy, map_add])

lemma polyCancel_symm_tmul (r : R') (b : B) : letI := algPoly (R := R) (R' := R')
    (polyCancel (R := R) (R' := R') (B := B)).symm (r ⊗ₜ[R] b) = (C r : R'[X]) ⊗ₜ[R[X]] b :=
  polyCancelBwd_tmul r b

/-! ### The localization `E ⊗_R B` -/

variable (E : Type u) [CommRing E] [Algebra R' E] [Algebra R E] [IsScalarTower R R' E] (π' : R')
  [IsLocalization.Away π' E]

/-- `R' ⊗_R B → E ⊗_R B`. -/
@[reducible] def algTE : Algebra (R' ⊗[R] B) (E ⊗[R] B) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' E) (AlgHom.id R B)).toRingHom.toAlgebra

omit [Algebra R[X] B] [IsScalarTower R R[X] B] in
lemma isLocalization_tensor_aux : letI := algTE (R := R) (R' := R') (B := B) E
    IsLocalization (Algebra.algebraMapSubmonoid (R' ⊗[R] B) (Submonoid.powers π'))
      (E ⊗[R] B) := by
  letI := algTE (R := R) (R' := R') (B := B) E
  haveI : IsScalarTower R' (R' ⊗[R] B) (E ⊗[R] B) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  exact IsLocalization.tensorProduct_tensorProduct R B (Submonoid.powers π') E
    (RingHom.ext fun b ↦ by
      change Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' E) (AlgHom.id R B)
        ((1 : R') ⊗ₜ[R] b) = (1 : E) ⊗ₜ[R] b
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply])

/-- `R'[X] ⊗_{R[X]} B → E ⊗_R B` (through `polyCancel`). -/
@[reducible] def algBCE : letI := algPoly (R := R) (R' := R')
    Algebra (R'[X] ⊗[R[X]] B) (E ⊗[R] B) :=
  letI := algPoly (R := R) (R' := R')
  letI := algTE (R := R) (R' := R') (B := B) E
  ((algebraMap (R' ⊗[R] B) (E ⊗[R] B)).comp
    (polyCancel (R := R) (R' := R') (B := B)).toRingHom).toAlgebra

/-- **`E ⊗_R B` is the localization of `R'[X] ⊗_{R[X]} B` away from `C π'`** (`E = R'[1/π']`). -/
theorem isLocalization_tensor : letI := algPoly (R := R) (R' := R')
    letI := algBCE (R := R) (R' := R') (B := B) E
    IsLocalization.Away (algebraMap R'[X] (R'[X] ⊗[R[X]] B) (C π')) (E ⊗[R] B) := by
  letI := algPoly (R := R) (R' := R')
  letI := algTE (R := R) (R' := R') (B := B) E
  haveI := isLocalization_tensor_aux (R := R) (R' := R') (B := B) E π'
  have h := IsLocalization.isLocalization_of_base_ringEquiv
    (Algebra.algebraMapSubmonoid (R' ⊗[R] B) (Submonoid.powers π')) (E ⊗[R] B)
    (polyCancel (R := R) (R' := R') (B := B)).symm
  have hM : (Algebra.algebraMapSubmonoid (R' ⊗[R] B) (Submonoid.powers π')).map
      (polyCancel (R := R) (R' := R') (B := B)).symm =
      Submonoid.powers (algebraMap R'[X] (R'[X] ⊗[R[X]] B) (C π')) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Submonoid.map_powers]
    congr 1
    change (polyCancel (R := R) (R' := R') (B := B)).symm (π' ⊗ₜ[R] (1 : B)) = _
    rw [polyCancel_symm_tmul]
    rfl
  rw [hM] at h
  exact h

include π' in
/-- **Trivial idempotents of `E ⊗_R B`** from those of the localizations of `R'[X] ⊗_{R[X]} B`
away from `C π'` (the form of `P1Three.connected_lift_baseChange`). -/
theorem eq_zero_or_eq_one_tensor
    (h : letI := algPoly (R := R) (R' := R')
      ∀ (S : Type u) [CommRing S] [Algebra (R'[X] ⊗[R[X]] B) S]
        [IsLocalization.Away (algebraMap R'[X] (R'[X] ⊗[R[X]] B) (C π')) S] {e : S},
        IsIdempotentElem e → e = 0 ∨ e = 1)
    {e : E ⊗[R] B} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  letI := algPoly (R := R) (R' := R')
  letI := algBCE (R := R) (R' := R') (B := B) E
  haveI := isLocalization_tensor (R := R) (R' := R') (B := B) E π'
  exact h (E ⊗[R] B) he

end

end GenericConnected

end SemistableReduction
