/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KaehlerChartVanish
import TemperedFundamentalGroups.SemistableReduction.NormalisedModel

/-!
# The relative differentials of a chart algebra over a base model (Blueprint §12.8, M2.5 (f))

For a coherent chart algebra `B` on `ℙ¹_A` (the covering `𝒴`) with a morphism of chart algebras
`φ : D.algStr → B` from two-chart rings `D` (the base model `𝒳`), the relative differentials
`Ω[B₀⁄D.R0]`, `Ω[B₁⁄D.R1]`, `Ω[B₀₁⁄D.R01]` form a coherent chart module
(**`ProjectiveLine.ChartModule.AlgStr.IsHom.kaehler`**, an instance of `KaehlerChart.chartModule`;
the ring map on the overlap is **`AlgStr.IsHom.ringHom01`**). Over a Noetherian `I`-adically
complete `A`, the full faithfulness of completion on `ℙ¹_A` then gives
(**`AlgStr.IsHom.kills_of_quot`**): a constant `c ∈ A` killing the differentials of all
reductions `B_i ⧸ Iⁿ B_i` over `D.R_i` kills `Ω[B_i⁄D.R_i]`; and
(**`AlgStr.IsHom.kills_x_of_quot`**) the same with `c X` on the first chart and `c` on the
second (coverings ramified over `X = 0`).
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace TwoChartRings

variable {A : Type u} [CommRing A] (D : TwoChartRings A)

/-- The overlap is the localization of the first chart at `x`. -/
theorem isLocalization_ρ0 :
    letI := D.ρ0.toRingHom.toAlgebra
    IsLocalization.Away D.x D.R01 := by
  letI := D.ρ0.toRingHom.toAlgebra
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, fun z ↦ ?_, fun {a b} hab ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit (D.ρ0 (D.x ^ k))
    rw [map_pow, D.ρ0_x]
    exact (Units.isUnit _).pow k
  · obtain ⟨m, k, hk⟩ := D.exists0 z
    refine ⟨⟨m, ⟨D.x ^ k, k, rfl⟩⟩, ?_⟩
    change z * D.ρ0 (D.x ^ k) = D.ρ0 m
    rw [map_pow, D.ρ0_x, mul_comm, hk]
  · change D.ρ0 a = D.ρ0 b at hab
    obtain ⟨k, hk⟩ := D.ker0 (a - b) (by rw [map_sub, hab, sub_self])
    exact ⟨⟨D.x ^ k, k, rfl⟩, by
      change D.x ^ k * a = D.x ^ k * b
      rw [← sub_eq_zero, ← mul_sub, hk]⟩

/-- The overlap is the localization of the second chart at `y`. -/
theorem isLocalization_ρ1 :
    letI := D.ρ1.toRingHom.toAlgebra
    IsLocalization.Away D.y D.R01 := by
  letI := D.ρ1.toRingHom.toAlgebra
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, fun z ↦ ?_, fun {a b} hab ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit (D.ρ1 (D.y ^ k))
    rw [map_pow, D.ρ1_y]
    exact (Units.isUnit _).pow k
  · obtain ⟨m, k, hk⟩ := D.exists1 z
    refine ⟨⟨m, ⟨D.y ^ k, k, rfl⟩⟩, ?_⟩
    change z * D.ρ1 (D.y ^ k) = D.ρ1 m
    rw [map_pow, D.ρ1_y, mul_comm, hk]
  · change D.ρ1 a = D.ρ1 b at hab
    obtain ⟨k, hk⟩ := D.ker1 (a - b) (by rw [map_sub, hab, sub_self])
    exact ⟨⟨D.y ^ k, k, rfl⟩, by
      change D.y ^ k * a = D.y ^ k * b
      rw [← sub_eq_zero, ← mul_sub, hk]⟩

end TwoChartRings

namespace ChartModule

namespace AlgStr

open BTensor

variable {A : Type u} [CommRing A] {M : ChartModule A} {B : AlgStr M} {D : TwoChartRings A}
  {φ : Hom D.chartModule M} (h : D.algStr.IsHom B φ)

/-- **A morphism of chart algebras is a ring map on the overlap.** -/
noncomputable def IsHom.ringHom01 : D.R01 →+* B.Ring01 where
  toFun := φ.f01
  map_one' := by
    have h1 : φ.f0 (1 : D.R0) = B.one.1.1 := h.ringHom0.map_one
    have h2 : φ.f01 (D.ρ0 1) = M.r0 (φ.f0 1) := φ.comm_r0 1
    rw [h1, map_one] at h2
    exact h2
  map_mul' a b := by
    have := Hom.f01_eq_of_eq h.1 (tm _ _ a b)
    change φ.f01 (TwoChartRings.bmul A (D.u : D.R01) (tm _ _ a b)) =
      B.mul.f01 (tm _ _ (φ.f01 a) (φ.f01 b)) at *
    rw [show (tm _ _ (φ.f01 a) (φ.f01 b) : BTensor (M.t : M.M01 →ₗ[A] M.M01)
        (M.t : M.M01 →ₗ[A] M.M01)) = (φ.tensor φ).f01 (tm _ _ a b) from
        (bmap_tm _ _ _ _ a b).symm]
    rw [TwoChartRings.bmul_tm] at this ⊢
    exact this
  map_zero' := map_zero φ.f01
  map_add' := map_add φ.f01

lemma IsHom.ringHom01_apply (z : D.R01) : h.ringHom01 z = φ.f01 z := rfl

lemma IsHom.ringHom01_ρ0 (m : D.R0) :
    h.ringHom01 (D.ρ0 m) = B.r0Hom (h.ringHom0 ((TwoChartRings.ring0Equiv D).symm m)) :=
  φ.comm_r0 m

lemma IsHom.ringHom01_ρ1 (m : D.R1) :
    h.ringHom01 (D.ρ1 m) = B.r1Hom (h.ringHom1 ((TwoChartRings.ring1Equiv D).symm m)) :=
  φ.comm_r1 m

lemma IsHom.ringHom0_x : h.ringHom0 ((TwoChartRings.ring0Equiv D).symm D.x) = B.X0 := by
  rw [← TwoChartRings.ring0Equiv_X0, RingEquiv.symm_apply_apply, h.ringHom0_X0]

lemma IsHom.ringHom1_y : h.ringHom1 ((TwoChartRings.ring1Equiv D).symm D.y) = B.X1 := by
  rw [← TwoChartRings.ring1Equiv_X1, RingEquiv.symm_apply_apply, h.ringHom1_X1]

/-- The `D.R01`-algebra structure of `B₀₁`. -/
noncomputable abbrev algR01 : Algebra D.R01 B.Ring01 := h.ringHom01.toAlgebra

variable (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A]
  [Module.Finite A[X] (Module.AEval' M.x0)] [Module.Finite A[X] (Module.AEval' M.x1)]

/-- **The relative differentials of a coherent chart algebra over a base model, killed modulo all
`Iⁿ`, are killed**: if `c Xʲ` (`j ≤ 1`) kills the differentials of `B₀ ⧸ Iⁿ B₀` over `D.R0` and
`c` kills those of `B₁ ⧸ Iⁿ B₁` over `D.R1` for all `n`, then `c Xʲ` kills `Ω[B₀⁄D.R0]` and `c`
kills `Ω[B₁⁄D.R1]` (through the chart module `KaehlerChart.chartModule` of `Ω_{𝒴/𝒳}` and the full
faithfulness of completion on `ℙ¹_A`). -/
theorem IsHom.kills_of_quot {c : A} {j : ℕ} (hj : j ≤ 1)
    (h0 : ∀ n, letI := B.algR0 h
      KaehlerLocal.Kills D.R0 (Ideal.Quotient.mk ((I ^ n).map B.const0) (B.const0 c * B.X0 ^ j)))
    (h1 : ∀ n, letI := B.algR1 h
      KaehlerLocal.Kills D.R1 (Ideal.Quotient.mk ((I ^ n).map B.const1) (B.const1 c))) :
    (letI := B.algR0 h; KaehlerLocal.Kills D.R0 (B.const0 c * B.X0 ^ j)) ∧
      (letI := B.algR1 h; KaehlerLocal.Kills D.R1 (B.const1 c)) := by
  letI : Algebra A B.Ring0 := B.const0.toAlgebra
  letI : Algebra A B.Ring1 := B.const1.toAlgebra
  letI : Algebra A B.Ring01 := B.const01.toAlgebra
  letI := B.algR0 h
  letI := B.algR1 h
  letI := algR01 h
  letI : Algebra D.R0 D.R01 := D.ρ0.toRingHom.toAlgebra
  letI : Algebra D.R1 D.R01 := D.ρ1.toRingHom.toAlgebra
  letI : Algebra B.Ring0 B.Ring01 := B.r0Hom.toAlgebra
  letI : Algebra B.Ring1 B.Ring01 := B.r1Hom.toAlgebra
  letI : Algebra D.R0 B.Ring01 := (B.r0Hom.comp (algebraMap D.R0 B.Ring0)).toAlgebra
  letI : Algebra D.R1 B.Ring01 := (B.r1Hom.comp (algebraMap D.R1 B.Ring1)).toAlgebra
  haveI : IsScalarTower A D.R0 B.Ring0 := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change B.const0 a = h.ringHom0 ((TwoChartRings.ring0Equiv D).symm (algebraMap A D.R0 a))
    rw [← TwoChartRings.ring0Equiv_const0, RingEquiv.symm_apply_apply, h.ringHom0_const0]
  haveI : IsScalarTower A D.R1 B.Ring1 := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change B.const1 a = h.ringHom1 ((TwoChartRings.ring1Equiv D).symm (algebraMap A D.R1 a))
    rw [← TwoChartRings.ring1Equiv_const1, RingEquiv.symm_apply_apply, h.ringHom1_const1]
  haveI : IsScalarTower A D.R01 B.Ring01 := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change B.const01 a = h.ringHom01 (algebraMap A D.R01 a)
    rw [← D.ρ0.commutes a]
    rw [h.ringHom01_ρ0, ← TwoChartRings.ring0Equiv_const0, RingEquiv.symm_apply_apply,
      h.ringHom0_const0, B.r0Hom_const0]
  haveI : IsScalarTower D.R0 D.R01 B.Ring01 := IsScalarTower.of_algebraMap_eq fun m ↦
    (h.ringHom01_ρ0 m).symm
  haveI : IsScalarTower D.R1 D.R01 B.Ring01 := IsScalarTower.of_algebraMap_eq fun m ↦
    (h.ringHom01_ρ1 m).symm
  haveI : IsScalarTower D.R0 B.Ring0 B.Ring01 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower D.R1 B.Ring1 B.Ring01 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A B.Ring0 B.Ring01 := IsScalarTower.of_algebraMap_eq fun a ↦
    (B.r0Hom_const0 a).symm
  haveI : IsScalarTower A B.Ring1 B.Ring01 := IsScalarTower.of_algebraMap_eq fun a ↦
    (B.r1Hom_const1 a).symm
  haveI : IsLocalization.Away D.x D.R01 := D.isLocalization_ρ0
  haveI : IsLocalization.Away D.y D.R01 := D.isLocalization_ρ1
  haveI : IsLocalization.Away (algebraMap D.R0 B.Ring0 D.x) B.Ring01 := by
    change IsLocalization.Away (h.ringHom0 ((TwoChartRings.ring0Equiv D).symm D.x)) B.Ring01
    rw [h.ringHom0_x]
    exact B.isLocalization_r0
  haveI : IsLocalization.Away (algebraMap D.R1 B.Ring1 D.y) B.Ring01 := by
    change IsLocalization.Away (h.ringHom1 ((TwoChartRings.ring1Equiv D).symm D.y)) B.Ring01
    rw [h.ringHom1_y]
    exact B.isLocalization_r1
  have hxy : algebraMap D.R0 B.Ring01 D.x * algebraMap D.R1 B.Ring01 D.y = 1 := by
    change B.r0Hom (h.ringHom0 ((TwoChartRings.ring0Equiv D).symm D.x)) *
      B.r1Hom (h.ringHom1 ((TwoChartRings.ring1Equiv D).symm D.y)) = 1
    rw [h.ringHom0_x, h.ringHom1_y, B.r0Hom_X0, B.r1Hom_X1, B.T01_mul_Tinv]
  have hx : algebraMap D.R0 B.Ring0 D.x = B.X0 := h.ringHom0_x
  have hy : algebraMap D.R1 B.Ring1 D.y = B.X1 := h.ringHom1_y
  haveI : Module.Finite D.R0 B.Ring0 := by
    letI := (Polynomial.aeval (R := A) D.x).toRingHom.toAlgebra
    letI := B.polyHom0.toAlgebra
    haveI := B.finite_polyHom0
    haveI : IsScalarTower A[X] D.R0 B.Ring0 := IsScalarTower.of_algebraMap_eq fun p ↦ by
      change B.polyHom0 p =
        h.ringHom0 ((TwoChartRings.ring0Equiv D).symm (Polynomial.aeval D.x p))
      rw [ring0Equiv_symm_aeval, h.ringHom0_polyHom0]
    exact Module.Finite.of_restrictScalars_finite A[X] D.R0 B.Ring0
  haveI : Module.Finite D.R1 B.Ring1 := by
    letI := (Polynomial.aeval (R := A) D.y).toRingHom.toAlgebra
    letI := B.polyHom1.toAlgebra
    haveI := B.finite_polyHom1
    haveI : IsScalarTower A[X] D.R1 B.Ring1 := IsScalarTower.of_algebraMap_eq fun p ↦ by
      change B.polyHom1 p =
        h.ringHom1 ((TwoChartRings.ring1Equiv D).symm (Polynomial.aeval D.y p))
      rw [ring1Equiv_symm_aeval, h.ringHom1_polyHom1]
    exact Module.Finite.of_restrictScalars_finite A[X] D.R1 B.Ring1
  haveI : Algebra.FiniteType D.R0 B.Ring0 := inferInstance
  haveI : Algebra.FiniteType D.R1 B.Ring1 := inferInstance
  haveI := KaehlerChart.finite_x0 (R01 := D.R01) (S1 := B.Ring1) A D.x D.y hxy B.polyHom0
    (by rw [hx]; exact Polynomial.eval₂_X _ _) (fun a ↦ Polynomial.eval₂_C _ _) B.finite_polyHom0
  haveI := KaehlerChart.finite_x1 (R01 := D.R01) (S0 := B.Ring0) A D.x D.y hxy B.polyHom1
    (by rw [hy]; exact Polynomial.eval₂_X _ _) (fun a ↦ Polynomial.eval₂_C _ _) B.finite_polyHom1
  interval_cases j
  · simp only [pow_zero, mul_one] at h0 ⊢
    exact KaehlerChart.kills_of_quot (R01 := D.R01) (S0 := B.Ring0) (S1 := B.Ring1) A D.x D.y I hxy
      h0 h1
  · simp only [pow_one] at h0 ⊢
    rw [← hx] at h0 ⊢
    exact KaehlerChart.kills_x_of_quot (R01 := D.R01) (S0 := B.Ring0) (S1 := B.Ring1) A D.x D.y I
      hxy h0 h1

end AlgStr

end ChartModule

end ProjectiveLine
