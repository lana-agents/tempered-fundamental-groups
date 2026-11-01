/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ChartAlgebraRingHom

/-!
# The ring map on the overlap of a morphism of chart algebras

* **`ProjectiveLine.ChartModule.AlgStr.IsHom.ringHom01'`**: a morphism of chart algebras
  `φ : B → B'` is a ring map `B₀₁ → B'₀₁` on the overlap, compatible with the restrictions
  (`ringHom01'_r0Hom`, `ringHom01'_r1Hom`);
* **`ProjectiveLine.TwoChartRings.ring01Equiv`**: the ring of sections of `D.algStr` over the
  overlap is `D.R01`.
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

namespace AlgStr

open BTensor

variable {A : Type u} [CommRing A] {M N : ChartModule A} {B : AlgStr M} {B' : AlgStr N}
  {φ : Hom M N}

/-- A morphism of chart algebras is multiplicative on the overlap. -/
lemma IsHom.f01_mul (h : B.IsHom B' φ) (a b : M.M01) :
    φ.f01 (B.mul.f01 (tm (M.t : M.M01 →ₗ[A] M.M01) (M.t : M.M01 →ₗ[A] M.M01) a b)) =
      B'.mul.f01 (tm (N.t : N.M01 →ₗ[A] N.M01) (N.t : N.M01 →ₗ[A] N.M01) (φ.f01 a) (φ.f01 b)) := by
  have := Hom.f01_eq_of_eq h.1 (tm _ _ a b)
  rw [show (tm _ _ (φ.f01 a) (φ.f01 b) : BTensor (N.t : N.M01 →ₗ[A] N.M01)
      (N.t : N.M01 →ₗ[A] N.M01)) = (φ.tensor φ).f01 (tm _ _ a b) from
      (bmap_tm _ _ _ _ a b).symm]
  exact this

/-- **A morphism of chart algebras is a ring map on the overlap.** -/
noncomputable def IsHom.ringHom01' (h : B.IsHom B' φ) : B.Ring01 →+* B'.Ring01 where
  toFun := φ.f01
  map_one' := by
    change φ.f01 (M.r0 B.one.1.1) = N.r0 B'.one.1.1
    rw [φ.comm_r0]
    exact congrArg N.r0 h.ringHom0.map_one
  map_mul' a b := h.f01_mul a b
  map_zero' := φ.f01.map_zero
  map_add' := φ.f01.map_add

lemma IsHom.ringHom01'_apply (h : B.IsHom B' φ) (z : B.Ring01) : h.ringHom01' z = φ.f01 z := rfl

lemma IsHom.ringHom01'_r0Hom (h : B.IsHom B' φ) (a : B.Ring0) :
    h.ringHom01' (B.r0Hom a) = B'.r0Hom (h.ringHom0 a) :=
  φ.comm_r0 a

lemma IsHom.ringHom01'_r1Hom (h : B.IsHom B' φ) (a : B.Ring1) :
    h.ringHom01' (B.r1Hom a) = B'.r1Hom (h.ringHom1 a) :=
  φ.comm_r1 a

end AlgStr

end ChartModule

namespace TwoChartRings

open ChartModule

variable {A : Type u} [CommRing A] (D : TwoChartRings A)

noncomputable instance : CommRing D.algStr.Ring01 := AlgStr.instCommRingRing01 _

/-- **The ring of sections of `D.algStr` over the overlap is `D.R01`.** -/
noncomputable def ring01Equiv : D.algStr.Ring01 ≃+* D.R01 where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := bmul_tm A (D.u : D.R01) a b
  map_add' _ _ := rfl

lemma ring01Equiv_r0Hom (a : D.algStr.Ring0) :
    D.ring01Equiv (D.algStr.r0Hom a) = D.ρ0 (D.ring0Equiv a) := rfl

lemma ring01Equiv_r1Hom (a : D.algStr.Ring1) :
    D.ring01Equiv (D.algStr.r1Hom a) = D.ρ1 (D.ring1Equiv a) := rfl

end TwoChartRings

end ProjectiveLine
