/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeLine
import TemperedFundamentalGroups.SemistableReduction.P1ThreeEtale
import TemperedFundamentalGroups.SemistableReduction.P1ThreeGeomConnectedTensor
import TemperedFundamentalGroups.SemistableReduction.BaseChangeAct
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Base change of the chart `V₁` of `ℙ¹_O` with three cusps and of its lift (MR13)

For an `O`-algebra `L` (think `L = K̄`, an algebraic closure of `K = Frac O`):

* **`P1Three.tensorR1Equiv : L ⊗_O R1 O a ≃ₐ[L] R1 L a`** (adjoining a root commutes with base
  change; `1 ⊗ s ↦ s`, `1 ⊗ Y ↦ Y`), and for a field `L` with `a ≠ 0` in `L`,
  **`P1Three.tensorLineEquiv : L ⊗_O R1 ≃ₐ[L] L[s, 1/((s − 1)(s − a⁻¹))]`** (`1 ⊗ s ↦ s`);
* for an `R`-algebra `B` (with compatible `O`-algebra structure) and the
  `T = L ⊗_O R`-algebra structure on `C = L ⊗_O B` given by `tensorMap`:
  **`isPushout_tensor`** (`C = T ⊗_R B`), **`finrank_tensor`**
  (`[K ⊗_T C : K] = rank_R B` for a field `K` over `T` with `R → K` injective),
  **`finite_tensor`**, **`etale_tensor`** (`C` étale over `T` if `B[1/x]` is étale over
  `R[1/x]` and `x` is a unit of `T`), and **`tensorAct`**: `BaseChangeAct.act` as an action by
  `T`-algebra automorphisms;
* for the lift `B₁` of the second chart: **`finite_tensor_lift`**, **`etale_tensor_lift`**
  (`L ⊗_O B₁` is finite étale over `L ⊗_O R1` when `ϖ` is a unit of `L`).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace P1Three

noncomputable section

section BaseChange

variable {O : Type u} [CommRing O] (a : O) (L : Type u) [CommRing L] [Algebra O L]

lemma eval₂_G1_map : (G1 O a).eval₂ ((AdjoinRoot.of (G1 L (algebraMap O L a))).comp
    (mapRingHom (algebraMap O L))) (AdjoinRoot.root _) = 0 := by
  rw [← Polynomial.eval₂_map, map_G1, AdjoinRoot.eval₂_root]

/-- The ring map `R1 O a → R1 L a` induced by `O → L`. -/
def toR1Ring : R1 O a →+* R1 L (algebraMap O L a) :=
  AdjoinRoot.lift ((AdjoinRoot.of (G1 L (algebraMap O L a))).comp
    (mapRingHom (algebraMap O L))) (AdjoinRoot.root _) (eval₂_G1_map a L)

/-- The ring map `R1 O a → R1 L a` induced by `O → L`, as an `O`-algebra map. -/
def toR1 : R1 O a →ₐ[O] R1 L (algebraMap O L a) where
  __ := toR1Ring a L
  commutes' o := by
    change toR1Ring a L (algebraMap O (R1 O a) o) = _
    rw [← of_C, toR1Ring, AdjoinRoot.lift_of, RingHom.comp_apply, coe_mapRingHom,
      Polynomial.map_C, of_C, ← IsScalarTower.algebraMap_apply]

lemma toR1_s1 : toR1 a L (s1 O a) = s1 L (algebraMap O L a) :=
  AdjoinRoot.lift_root (eval₂_G1_map a L)

lemma toR1_y1 : toR1 a L (y1 O a) = y1 L (algebraMap O L a) := by
  change toR1Ring a L (AdjoinRoot.of _ X) = _
  rw [toR1Ring, AdjoinRoot.lift_of, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]

/-- `L ⊗_O R1 O a → R1 L a`. -/
def tensorToR1 : L ⊗[O] R1 O a →ₐ[L] R1 L (algebraMap O L a) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (toR1 a L) fun _ _ ↦ Commute.all _ _

lemma tensorToR1_tmul_one (x : R1 O a) : tensorToR1 a L ((1 : L) ⊗ₜ x) = toR1 a L x := by
  rw [tensorToR1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

lemma eval₂_G1_tmul : (G1 L (algebraMap O L a)).eval₂
    ((aeval ((1 : L) ⊗ₜ[O] y1 O a) : L[X] →ₐ[L] L ⊗[O] R1 O a) : L[X] →+* L ⊗[O] R1 O a)
    ((1 : L) ⊗ₜ[O] s1 O a) = 0 := by
  rw [eval₂_G1, ← IsScalarTower.algebraMap_apply]
  have h := congrArg (Algebra.TensorProduct.includeRight : R1 O a →ₐ[O] L ⊗[O] R1 O a) (eq1 O a)
  simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_zero, map_one,
    Algebra.TensorProduct.includeRight_apply] at h
  linear_combination h

/-- `R1 L a → L ⊗_O R1 O a`. -/
def r1ToTensor : R1 L (algebraMap O L a) →ₐ[L] L ⊗[O] R1 O a :=
  AdjoinRoot.liftAlgHom _ (aeval ((1 : L) ⊗ₜ[O] y1 O a)) ((1 : L) ⊗ₜ[O] s1 O a)
    (eval₂_G1_tmul a L)

lemma r1ToTensor_s1 : r1ToTensor a L (s1 L (algebraMap O L a)) = (1 : L) ⊗ₜ[O] s1 O a :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma r1ToTensor_y1 : r1ToTensor a L (y1 L (algebraMap O L a)) = (1 : L) ⊗ₜ[O] y1 O a := by
  rw [r1ToTensor, AdjoinRoot.liftAlgHom_of, aeval_X]

lemma tensorToR1_comp_r1ToTensor :
    (tensorToR1 a L).comp (r1ToTensor a L) = AlgHom.id L _ := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change tensorToR1 a L (r1ToTensor a L (y1 L _)) = y1 L _
    rw [r1ToTensor_y1, tensorToR1_tmul_one, toR1_y1]
  · change tensorToR1 a L (r1ToTensor a L (s1 L _)) = s1 L _
    rw [r1ToTensor_s1, tensorToR1_tmul_one, toR1_s1]

lemma r1ToTensor_comp_tensorToR1 :
    (r1ToTensor a L).comp (tensorToR1 a L) = AlgHom.id L _ := by
  apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change r1ToTensor a L (tensorToR1 a L ((1 : L) ⊗ₜ y1 O a)) = (1 : L) ⊗ₜ y1 O a
    rw [tensorToR1_tmul_one, toR1_y1, r1ToTensor_y1]
  · change r1ToTensor a L (tensorToR1 a L ((1 : L) ⊗ₜ s1 O a)) = (1 : L) ⊗ₜ s1 O a
    rw [tensorToR1_tmul_one, toR1_s1, r1ToTensor_s1]

/-- **`L ⊗_O R1 O a ≃ R1 L a`** (adjoining a root commutes with base change). -/
def tensorR1Equiv : L ⊗[O] R1 O a ≃ₐ[L] R1 L (algebraMap O L a) :=
  AlgEquiv.ofAlgHom (tensorToR1 a L) (r1ToTensor a L) (tensorToR1_comp_r1ToTensor a L)
    (r1ToTensor_comp_tensorToR1 a L)

lemma tensorR1Equiv_apply (x : L ⊗[O] R1 O a) : tensorR1Equiv a L x = tensorToR1 a L x :=
  rfl

lemma tensorR1Equiv_symm_apply (x : R1 L (algebraMap O L a)) :
    (tensorR1Equiv a L).symm x = r1ToTensor a L x :=
  rfl

@[simp]
lemma tensorR1Equiv_s1 : tensorR1Equiv a L ((1 : L) ⊗ₜ[O] s1 O a) = s1 L (algebraMap O L a) :=
  by rw [tensorR1Equiv_apply, tensorToR1_tmul_one, toR1_s1]

@[simp]
lemma tensorR1Equiv_y1 : tensorR1Equiv a L ((1 : L) ⊗ₜ[O] y1 O a) = y1 L (algebraMap O L a) :=
  by rw [tensorR1Equiv_apply, tensorToR1_tmul_one, toR1_y1]

@[simp]
lemma tensorR1Equiv_symm_s1 :
    (tensorR1Equiv a L).symm (s1 L (algebraMap O L a)) = (1 : L) ⊗ₜ[O] s1 O a := by
  rw [tensorR1Equiv_symm_apply, r1ToTensor_s1]

@[simp]
lemma tensorR1Equiv_symm_y1 :
    (tensorR1Equiv a L).symm (y1 L (algebraMap O L a)) = (1 : L) ⊗ₜ[O] y1 O a := by
  rw [tensorR1Equiv_symm_apply, r1ToTensor_y1]

end BaseChange

section Field

variable {O : Type u} [CommRing O] (a : O) (L : Type u) [Field L] [Algebra O L]

/-- **`L ⊗_O R1 ≃ L[s, 1/((s − 1)(s − a⁻¹))]`** for a field `L` over `O` with `a ≠ 0` in `L`
(`1 ⊗ s ↦ s`): the base change of the chart `V₁` to `L` is the line
`ℙ¹_L ∖ {1, a⁻¹, ∞}` in the coordinate `s = 1/t`. -/
def tensorLineEquiv (ha : algebraMap O L a ≠ 0) :
    L ⊗[O] R1 O a ≃ₐ[L] Localization.Away (pS (algebraMap O L a)) :=
  (tensorR1Equiv a L).trans (lineEquivK (algebraMap O L a) ha)

@[simp]
lemma tensorLineEquiv_s1 (ha : algebraMap O L a ≠ 0) :
    tensorLineEquiv a L ha ((1 : L) ⊗ₜ[O] s1 O a) =
      algebraMap L[X] (Localization.Away (pS (algebraMap O L a))) X := by
  rw [tensorLineEquiv, AlgEquiv.trans_apply, tensorR1Equiv_s1, lineEquivK_s1]

end Field

end


section Pushout

variable {O R B L : Type*} [CommRing O] [CommRing R] [CommRing B] [CommRing L] [Algebra O R]
  [Algebra R B] [Algebra O B] [IsScalarTower O R B] [Algebra O L]

variable (O R B L) in
/-- The map `L ⊗_O R → L ⊗_O B` induced by `R → B`. -/
noncomputable abbrev tensorMap : L ⊗[O] R →ₐ[L] L ⊗[O] B :=
  Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom O R B)

/-- **`L ⊗_O B` is the base change of `B` along `R → L ⊗_O R`** (for any algebra structures
given by the canonical maps). -/
theorem isPushout_tensor {i₁ : Algebra R (L ⊗[O] R)} {i₂ : Algebra B (L ⊗[O] B)}
    [Algebra R (L ⊗[O] B)] [Algebra (L ⊗[O] R) (L ⊗[O] B)]
    [IsScalarTower R (L ⊗[O] R) (L ⊗[O] B)] [IsScalarTower R B (L ⊗[O] B)]
    (h₁ : algebraMap R (L ⊗[O] R) = (Algebra.TensorProduct.includeRight : R →ₐ[O] _).toRingHom)
    (h₂ : algebraMap B (L ⊗[O] B) = (Algebra.TensorProduct.includeRight : B →ₐ[O] _).toRingHom)
    (h₃ : algebraMap (L ⊗[O] R) (L ⊗[O] B) = (tensorMap O R B L).toRingHom) :
    Algebra.IsPushout R (L ⊗[O] R) B (L ⊗[O] B) := by
  obtain rfl : i₁ = Algebra.TensorProduct.rightAlgebra :=
    Algebra.algebra_ext _ _ fun r ↦ RingHom.congr_fun h₁ r
  obtain rfl : i₂ = Algebra.TensorProduct.rightAlgebra :=
    Algebra.algebra_ext _ _ fun r ↦ RingHom.congr_fun h₂ r
  letI : Algebra R (L ⊗[O] R) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (L ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower O B (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun o ↦ by
    change algebraMap O L o ⊗ₜ (1 : B) = (1 : L) ⊗ₜ algebraMap O B o
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  haveI : IsScalarTower O R (L ⊗[O] R) := IsScalarTower.of_algebraMap_eq fun o ↦ by
    change algebraMap O L o ⊗ₜ (1 : R) = (1 : L) ⊗ₜ algebraMap O R o
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  haveI : IsScalarTower O (L ⊗[O] R) (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun o ↦ by
    rw [h₃]
    exact ((tensorMap O R B L).restrictScalars O).commutes o |>.symm
  haveI : IsScalarTower L (L ⊗[O] R) (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun l ↦ by
    rw [h₃]
    exact ((tensorMap O R B L).commutes l).symm
  exact Algebra.IsPushout.symm
    ((Algebra.IsPushout.comp_iff O R L (T := B) (S' := L ⊗[O] R) (T' := L ⊗[O] B)).1
      inferInstance)


/-- **Degree of a base change** (abstract form): if `C = T ⊗_R B` and `K` is a field over `T`
with `R → K` injective, then `[K ⊗_T C : K] = rank_R B`. -/
theorem finrank_of_isPushout {R B T C K : Type*} [CommRing R] [CommRing B] [CommRing T]
    [CommRing C] [Field K] [Algebra R B] [Algebra R T] [Algebra T C] [Algebra B C] [Algebra R C]
    [IsScalarTower R T C] [IsScalarTower R B C] [hP : Algebra.IsPushout R T B C]
    [Algebra T K] [Algebra R K] [IsScalarTower R T K] [FaithfulSMul R K] :
    Module.finrank K (K ⊗[T] C) = Module.finrank R B :=
  (hP.out.comp (TensorProduct.isBaseChange T C K)).finrank_eq

/-- **Degree of the base change** `L ⊗_O B` over `L ⊗_O R`: for a field `K` over `L ⊗_O R`
such that `R → K` is injective, `[K ⊗_{L ⊗_O R} (L ⊗_O B) : K] = rank_R B`. -/
theorem finrank_tensor [Algebra (L ⊗[O] R) (L ⊗[O] B)]
    (h₃ : algebraMap (L ⊗[O] R) (L ⊗[O] B) = (tensorMap O R B L).toRingHom)
    (K : Type*) [Field K] [Algebra (L ⊗[O] R) K]
    (hK : Function.Injective ((algebraMap (L ⊗[O] R) K).comp
      (Algebra.TensorProduct.includeRight : R →ₐ[O] L ⊗[O] R).toRingHom)) :
    Module.finrank K (K ⊗[L ⊗[O] R] (L ⊗[O] B)) = Module.finrank R B := by
  letI : Algebra R (L ⊗[O] R) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (L ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra R (L ⊗[O] B) := ((algebraMap B (L ⊗[O] B)).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (L ⊗[O] R) (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [h₃]
    rfl
  haveI : Algebra.IsPushout R (L ⊗[O] R) B (L ⊗[O] B) := isPushout_tensor rfl rfl h₃
  letI : Algebra R K := ((algebraMap (L ⊗[O] R) K).comp (algebraMap R (L ⊗[O] R))).toAlgebra
  haveI : IsScalarTower R (L ⊗[O] R) K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hK
  exact finrank_of_isPushout (B := B)

end Pushout


section Etale

variable {R B T C : Type*} [CommRing R] [CommRing B] [CommRing T] [CommRing C] [Algebra R B]
  [Algebra R T] [Algebra T C] [Algebra B C] [Algebra R C] [IsScalarTower R T C]
  [IsScalarTower R B C] [Algebra.IsPushout R T B C]

/-- **Finiteness is stable under base change**: `C = T ⊗_R B` is finite over `T` if `B` is
finite over `R`. -/
theorem finite_of_isPushout [Module.Finite R B] : Module.Finite T C :=
  Module.Finite.equiv (Algebra.IsPushout.equiv R T B C).toLinearEquiv

/-- **Étaleness after inverting `x` is stable under base change to a ring in which `x` is a
unit**: if `B[1/x]` is étale over `R[1/x]` and `x` is a unit of `T`, then `C = T ⊗_R B` is étale
over `T`. -/
theorem etale_of_isPushout_away (x : R) (Rx Bx : Type*) [CommRing Rx] [CommRing Bx]
    [Algebra R Rx] [IsLocalization.Away x Rx] [Algebra B Bx] [Algebra R Bx] [IsScalarTower R B Bx]
    [IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers x)) Bx]
    [Algebra Rx Bx] [IsScalarTower R Rx Bx] [Algebra.Etale Rx Bx]
    (hx : IsUnit (algebraMap R T x)) : Algebra.Etale T C := by
  letI : Algebra Rx T := (IsLocalization.Away.lift x hx).toAlgebra
  haveI : IsScalarTower R Rx T := IsScalarTower.of_algebraMap_eq fun r ↦
    (IsLocalization.Away.lift_eq x hx r).symm
  letI : Algebra Bx (T ⊗[Rx] Bx) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (T ⊗[Rx] Bx) :=
    ((algebraMap Bx (T ⊗[Rx] Bx)).comp (algebraMap B Bx)).toAlgebra
  haveI : IsScalarTower B Bx (T ⊗[Rx] Bx) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower Rx Bx (T ⊗[Rx] Bx) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap Rx T r ⊗ₜ (1 : Bx) = (1 : T) ⊗ₜ algebraMap Rx Bx r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  haveI : IsScalarTower R Bx (T ⊗[Rx] Bx) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R Rx Bx, ← IsScalarTower.algebraMap_apply Rx Bx,
      IsScalarTower.algebraMap_apply R Rx (T ⊗[Rx] Bx)]
  haveI : IsScalarTower R B (T ⊗[Rx] Bx) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = algebraMap Bx (T ⊗[Rx] Bx) (algebraMap B Bx (algebraMap R B r))
    rw [← IsScalarTower.algebraMap_apply R B Bx, ← IsScalarTower.algebraMap_apply R Bx]
  haveI : Algebra.IsPushout R Rx B Bx :=
    Algebra.IsPushout.symm (Algebra.isPushout_of_isLocalization (Submonoid.powers x) Rx B Bx)
  haveI hD : Algebra.IsPushout R T B (T ⊗[Rx] Bx) :=
    (Algebra.IsPushout.comp_iff R Rx B (T := T) (S' := Bx) (T' := T ⊗[Rx] Bx)).2 inferInstance
  exact Algebra.Etale.of_equiv
    ((Algebra.IsPushout.equiv R T B (T ⊗[Rx] Bx)).symm.trans (Algebra.IsPushout.equiv R T B C))

end Etale


section TensorEtale

variable {O R B L : Type*} [CommRing O] [CommRing R] [CommRing B] [CommRing L] [Algebra O R]
  [Algebra R B] [Algebra O B] [IsScalarTower O R B] [Algebra O L]
  [Algebra (L ⊗[O] R) (L ⊗[O] B)]

/-- **`L ⊗_O B` is finite over `L ⊗_O R`** if `B` is finite over `R`. -/
theorem finite_tensor (h₃ : algebraMap (L ⊗[O] R) (L ⊗[O] B) = (tensorMap O R B L).toRingHom)
    [Module.Finite R B] : Module.Finite (L ⊗[O] R) (L ⊗[O] B) := by
  letI : Algebra R (L ⊗[O] R) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (L ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra R (L ⊗[O] B) := ((algebraMap B (L ⊗[O] B)).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (L ⊗[O] R) (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [h₃]
    rfl
  haveI : Algebra.IsPushout R (L ⊗[O] R) B (L ⊗[O] B) := isPushout_tensor rfl rfl h₃
  exact finite_of_isPushout (R := R) (B := B)

/-- **`L ⊗_O B` is étale over `L ⊗_O R`** if `B[1/x]` is étale over `R[1/x]` and `1 ⊗ x` is a
unit of `L ⊗_O R`. -/
theorem etale_tensor (h₃ : algebraMap (L ⊗[O] R) (L ⊗[O] B) = (tensorMap O R B L).toRingHom)
    (x : R) (Rx Bx : Type*) [CommRing Rx] [CommRing Bx]
    [Algebra R Rx] [IsLocalization.Away x Rx] [Algebra B Bx] [Algebra R Bx] [IsScalarTower R B Bx]
    [IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers x)) Bx]
    [Algebra Rx Bx] [IsScalarTower R Rx Bx] [Algebra.Etale Rx Bx]
    (hx : IsUnit ((1 : L) ⊗ₜ[O] x)) : Algebra.Etale (L ⊗[O] R) (L ⊗[O] B) := by
  letI : Algebra R (L ⊗[O] R) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (L ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra R (L ⊗[O] B) := ((algebraMap B (L ⊗[O] B)).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (L ⊗[O] R) (L ⊗[O] B) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [h₃]
    rfl
  haveI : Algebra.IsPushout R (L ⊗[O] R) B (L ⊗[O] B) := isPushout_tensor rfl rfl h₃
  exact etale_of_isPushout_away (R := R) (B := B) x Rx Bx hx

end TensorEtale

noncomputable section

/-! ### The Galois action on the base change -/

section Action

variable {O R B : Type u} [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra R B]
  [Algebra O B] [IsScalarTower O R B] (L : Type u) [CommRing L] [Algebra O L]
  [Algebra (L ⊗[O] R) (L ⊗[O] B)]
  (h₃ : algebraMap (L ⊗[O] R) (L ⊗[O] B) = (tensorMap O R B L).toRingHom)
  {G : Type*} [Group G] (ρ : G →* (B ≃ₐ[R] B))

include h₃ in
/-- The action `BaseChangeAct.act` on `L ⊗_O B` fixes `L ⊗_O R`. -/
lemma act_algebraMap (g : G) (r : L ⊗[O] R) :
    BaseChangeAct.act O L ρ g (algebraMap (L ⊗[O] R) (L ⊗[O] B) r) =
      algebraMap (L ⊗[O] R) (L ⊗[O] B) r := by
  rw [h₃]
  exact AlgHom.congr_fun (BaseChangeAct.act_comp_map O L ρ g) r

/-- **The action of `G` on `L ⊗_O B` by `L ⊗_O R`-algebra automorphisms.** -/
def tensorAct : G →* (L ⊗[O] B ≃ₐ[L ⊗[O] R] L ⊗[O] B) :=
  BaseChangeAct.toAlgAct
    { toFun := fun g ↦ (BaseChangeAct.act O L ρ g).toRingEquiv
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g g' ↦ by rw [map_mul]; rfl }
    (act_algebraMap L h₃ ρ)

lemma tensorAct_apply (g : G) (x : L ⊗[O] B) :
    tensorAct L h₃ ρ g x = BaseChangeAct.act O L ρ g x :=
  rfl

end Action

/-! ### The lift over `V₁` -/

section Lift

open TateLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O] (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))
  (ω : OmegaC Sp S0.C0) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) O]
  (hϖ0 : ϖ ≠ 0)
  {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
  [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)}
  (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
    LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
  (hB : ∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n))
  {ψ : ProjectiveLine.ChartModule.Hom (twoChart O a).chartModule N}
  (hψ : (twoChart O a).algStr.IsHom B ψ)
  (hψα : ∀ n, (α (n + 1)).comp ψ = structureMaps Sp hϖ hker S0 ω hO n)

omit [IsNoetherianRing O] [IsDomain O] [(Ideal.span {ϖ}).IsMaximal]
  [IsAdicComplete (Ideal.span {ϖ}) O] [Module.Finite O[X] (Module.AEval' N.x0)]
  [Module.Finite O[X] (Module.AEval' N.x1)] in
/-- The `O`-algebra structure `algO1` of `B₁` is compatible with the structure map `R1 → B₁`. -/
lemma isScalarTower_algO1 :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    letI : Algebra O B.Ring1 := algO1 B
    IsScalarTower O (R1 O a) B.Ring1 := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI : Algebra O B.Ring1 := algO1 B
  refine IsScalarTower.of_algebraMap_eq fun o ↦ ?_
  rw [algR1_const hψ]
  change B.polyHom1 (algebraMap O O[X] o) = B.const1 o
  simp [ProjectiveLine.ChartModule.AlgStr.polyHom1]

omit [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) O]
  [IsNoetherianRing O] [Module.Finite O[X] (Module.AEval' N.x0)] in
/-- **`L ⊗_O B₁` is finite over `L ⊗_O R1`.** -/
theorem finite_tensor_lift (L : Type u) [CommRing L] [Algebra O L] :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    letI : Algebra O B.Ring1 := algO1 B
    ∀ [IsScalarTower O (R1 O a) B.Ring1] [Algebra (L ⊗[O] R1 O a) (L ⊗[O] B.Ring1)],
      algebraMap (L ⊗[O] R1 O a) (L ⊗[O] B.Ring1) =
        (tensorMap O (R1 O a) B.Ring1 L).toRingHom →
      Module.Finite (L ⊗[O] R1 O a) (L ⊗[O] B.Ring1) := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI : Algebra O B.Ring1 := algO1 B
  intro _ _ h₃
  haveI : Module.Finite (R1 O a) B.Ring1 := finite_ring1 hψ
  exact finite_tensor h₃

variable [IsDiscreteValuationRing O]

omit [(Ideal.span {ϖ}).IsMaximal] in
include hα hB hψ hψα hϖ0 in
/-- **`L ⊗_O B₁` is étale over `L ⊗_O R1`** for an `O`-algebra `L` in which `ϖ` is a unit
(e.g. an algebraic closure of `K = Frac O`): base change of `etale_lift`. -/
theorem etale_tensor_lift [Module.Flat O[X] (Module.AEval' N.x1)] (L : Type u) [CommRing L]
    [Algebra O L] (hL : IsUnit (algebraMap O L ϖ)) :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    letI : Algebra O B.Ring1 := algO1 B
    ∀ [IsScalarTower O (R1 O a) B.Ring1] [Algebra (L ⊗[O] R1 O a) (L ⊗[O] B.Ring1)],
      algebraMap (L ⊗[O] R1 O a) (L ⊗[O] B.Ring1) =
        (tensorMap O (R1 O a) B.Ring1 L).toRingHom →
      Algebra.Etale (L ⊗[O] R1 O a) (L ⊗[O] B.Ring1) := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI : Algebra O B.Ring1 := algO1 B
  intro _ _ h₃
  letI : Algebra (R1 O a) (Localization.Away (B.const1 ϖ)) :=
    ((algebraMap B.Ring1 _).comp (algebraMap (R1 O a) B.Ring1)).toAlgebra
  haveI : @IsScalarTower (R1 O a) B.Ring1 (Localization.Away (B.const1 ϖ))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hu : IsUnit (algebraMap (R1 O a) (Localization.Away (B.const1 ϖ))
      (algebraMap O (R1 O a) ϖ)) := by
    rw [IsScalarTower.algebraMap_apply (R1 O a) B.Ring1, algR1_const hψ]
    exact IsLocalization.Away.algebraMap_isUnit _
  letI : Algebra (Localization.Away (algebraMap O (R1 O a) ϖ)) (Localization.Away (B.const1 ϖ)) :=
    (IsLocalization.Away.lift (algebraMap O (R1 O a) ϖ) hu).toAlgebra
  haveI : @IsScalarTower (R1 O a) (Localization.Away (algebraMap O (R1 O a) ϖ))
      (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (IsLocalization.Away.lift_eq _ hu r).symm
  haveI : Algebra.Etale (Localization.Away (algebraMap O (R1 O a) ϖ))
      (Localization.Away (B.const1 ϖ)) :=
    etale_lift Sp hϖ hker S0 ω hO hϖ0 hα hB hψ hψα
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B.Ring1
      (Submonoid.powers (algebraMap O (R1 O a) ϖ))) (Localization.Away (B.const1 ϖ)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, algR1_const hψ]
    infer_instance
  refine etale_tensor h₃ (algebraMap O (R1 O a) ϖ) (Localization.Away (algebraMap O (R1 O a) ϖ))
    (Localization.Away (B.const1 ϖ)) ?_
  rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply O L]
  exact hL.map _

end Lift

end

end P1Three

end SemistableReduction
