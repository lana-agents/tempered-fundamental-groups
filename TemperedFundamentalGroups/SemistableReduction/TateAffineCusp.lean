/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateAffineGlue
import TemperedFundamentalGroups.SemistableReduction.TateEtaleCusp

/-!
# T1a: the generic fibre of the Tate covering ramified at the cusp over `E ∖ {0}`

For a chart algebra `B` over the Tate model (a morphism of chart algebras
`ψ : TateTwoChart.twoChart → B`), the data of `TateAffineGlue` are `ι₀ = B₀`'s `T0`-structure,
`ι₁`, `ι₀₁ = hψ.ringHom01`, `r₀ = B.r0Hom`, `r₁ = B.r1Hom` (**`TateAffine.hc0_chart`**,
`hc1_chart`, `hloc0_chart`, `hloc1_chart`, `finite_iota0`, `finite_iota1`).

**`TateGlue0.finite_etale_gluedK_cusp`** (T1a): for the algebraized Tate covering ramified at the
cusp (as in `TateGlue0.etale_overlapCusp_z`), with the ramified cusp factors over the origin
(`CuspOverOrigin`), the glued generic fibre `TateAffine.gluedK` is a **finite étale algebra over
the coordinate ring `A[1/ϖ] = K[x, y]/(y² + x y − π x³ − π b₄ x − b₆)` of `E ∖ {0}`**, whose
restrictions to `D(y − t)` and `D(x)` are `B₀[1/(ϖ z)]` and `B₁[1/ϖ]`
(`TateAffine.isLocalization_gluedK_fst/snd`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateAffine

open TateTwoChart ProjectiveLine ProjectiveLine.ChartModule

noncomputable section

variable {O : Type u} [CommRing O] {π b₄ t κ : O} {N : ChartModule O} {B : AlgStr N}
  {ψ : Hom (twoChart π b₄ t κ).chartModule N} (hψ : (twoChart π b₄ t κ).algStr.IsHom B ψ)

/-- The `T0`-structure of `B₀`, as a ring map. -/
abbrev iota0 : T0 π b₄ t κ →+* B.Ring0 := @algebraMap _ _ _ _ (B.algR0 hψ)

/-- The `T1`-structure of `B₁`, as a ring map. -/
abbrev iota1 : T1 π b₄ t κ →+* B.Ring1 := @algebraMap _ _ _ _ (B.algR1 hψ)

lemma hc0_chart : B.r0Hom.comp (iota0 hψ) = hψ.ringHom01.comp (rho0 π b₄ t κ).toRingHom :=
  RingHom.ext fun a ↦ (hψ.ringHom01_ρ0 a).symm

lemma hc1_chart : B.r1Hom.comp (iota1 hψ) =
    hψ.ringHom01.comp (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ)) :=
  RingHom.ext fun a ↦ (hψ.ringHom01_ρ1 a).symm

lemma hloc0_chart : letI := B.r0Hom.toAlgebra
    IsLocalization.Away (iota0 hψ (h0 π b₄ t κ)) B.Ring01 := by
  have : iota0 hψ (h0 π b₄ t κ) = B.X0 := hψ.ringHom0_x
  rw [this]
  exact B.isLocalization_r0

lemma hloc1_chart : letI := B.r1Hom.toAlgebra
    IsLocalization.Away (iota1 hψ (h1 π b₄ t κ)) B.Ring01 := by
  have : iota1 hψ (h1 π b₄ t κ) = B.X1 := hψ.ringHom1_y
  rw [this]
  exact B.isLocalization_r1

lemma finite_iota0 [Module.Finite O[X] (Module.AEval' N.x0)] : (iota0 hψ).Finite := by
  have h := B.finite_polyHom0
  rw [← algR0_comp hψ] at h
  exact RingHom.Finite.of_comp_finite h

lemma finite_iota1 [Module.Finite O[X] (Module.AEval' N.x1)] : (iota1 hψ).Finite := by
  have h := B.finite_polyHom1
  rw [← algR1_comp hψ] at h
  exact RingHom.Finite.of_comp_finite h

lemma iota0_const (a : O) : iota0 hψ (algebraMap O (T0 π b₄ t κ) a) = B.const0 a := by
  have h := RingHom.congr_fun (algR0_comp hψ) (C a)
  rw [RingHom.comp_apply, algebraMap_C_T0] at h
  rw [h]
  simp [AlgStr.polyHom0]

lemma iota1_const (a : O) : iota1 hψ (algebraMap O (T1 π b₄ t κ) a) = B.const1 a := by
  have h := RingHom.congr_fun (algR1_comp hψ) (C a)
  rw [RingHom.comp_apply, algebraMap_C_T1] at h
  rw [h]
  simp [AlgStr.polyHom1]

end

end TateAffine

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel AdmissibleLift EtaleTower TateAffine

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsAdicComplete (Ideal.span {ϖ}) O]
  [IsEmpty cov₀.κ] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ0 : ϖ ≠ 0) (h3 : (3 : O) ≠ 0) (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)

omit [IsNoetherianRing O] [IsAdicComplete (Ideal.span {ϖ}) O] [IsDomain O]
  [IsDiscreteValuationRing O] in
include hπ hε in
lemma pi_dvd : π ∣ ϖ ^ m := ⟨εi, by rw [hπ]; linear_combination (-(ϖ ^ m)) * hε⟩

include hπ' hm hϖ0 h3 hE in
/-- **T1a for the Tate covering ramified at the cusp**: if the ramified cusp factors of the
special-fibre covering lie over the origin (`CuspOverOrigin`), the generic fibre of the
algebraized covering, glued over `E ∖ {0} = D(y − t) ∪ D(x)` (`TateAffine.gluedK`), is a
**finite étale algebra over the coordinate ring `A[1/ϖ]` of `E ∖ {0}`**; its restrictions to
`D(y − t)`, `D(x)` are `B₀[1/(ϖ z)]`, `B₁[1/ϖ]` (`TateAffine.isLocalization_gluedK_fst/snd`
with `TateAffine.hloc0_chart`, `hloc1_chart`). -/
theorem finite_etale_gluedK_cusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (hSc : CuspOverOrigin Sc) (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x0)]
    [Module.Flat O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n))
    {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N}
    (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n) :
    letI := algA b₄ ϖ hκ (iota0 hψ)
    letI := algB b₄ hκ (pi_dvd hπ hε) (iota1 hψ)
    Module.Finite (AK π b₄ b₆ ϖ)
        (gluedK b₄ hκ (pi_dvd hπ hε) (hc0_chart hψ) (hc1_chart hψ)) ∧
      Algebra.Etale (AK π b₄ b₆ ϖ)
        (gluedK b₄ hκ (pi_dvd hπ hε) (hc0_chart hψ) (hc1_chart hψ)) := by
  have e0 : iota0 hψ (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ) =
      B.const0 ϖ * iota0 hψ (z0 π b₄ t κ) := by
    rw [map_mul, iota0_const]
  have e1 : iota1 hψ (algebraMap O (T1 π b₄ t κ) ϖ) = B.const1 ϖ := iota1_const hψ ϖ
  have hBa : letI : Algebra (T0 π b₄ t κ) (Ba b₄ ϖ (iota0 hψ)) :=
        ((algebraMap B.Ring0 (Ba b₄ ϖ (iota0 hψ))).comp (iota0 hψ)).toAlgebra
      ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (Ba b₄ ϖ (iota0 hψ))]
        [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
          (Ba b₄ ϖ (iota0 hψ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
          (Ba b₄ ϖ (iota0 hψ)) := by
    have key : ∀ s : B.Ring0, s = B.const0 ϖ * iota0 hψ (z0 π b₄ t κ) →
        letI : Algebra (T0 π b₄ t κ) (Localization.Away s) :=
          ((algebraMap B.Ring0 (Localization.Away s)).comp (iota0 hψ)).toAlgebra
        ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (Localization.Away s)]
          [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
            (Localization.Away s) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
          Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
            (Localization.Away s) := by
      rintro s rfl
      intros
      exact etale_overlapCusp_z hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 h3 hE Sc hSc ω hα hB hψ hψα
    intros
    exact key _ e0
  have hBb : letI : Algebra (T1 π b₄ t κ) (Bb b₄ ϖ (iota1 hψ)) :=
        ((algebraMap B.Ring1 (Bb b₄ ϖ (iota1 hψ))).comp (iota1 hψ)).toAlgebra
      ∀ [Algebra (T1K π b₄ t κ ϖ) (Bb b₄ ϖ (iota1 hψ))]
        [@IsScalarTower (T1 π b₄ t κ) (T1K π b₄ t κ ϖ)
          (Bb b₄ ϖ (iota1 hψ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (T1K π b₄ t κ ϖ) (Bb b₄ ϖ (iota1 hψ)) := by
    have key : ∀ s : B.Ring1, s = B.const1 ϖ →
        letI : Algebra (T1 π b₄ t κ) (Localization.Away s) :=
          ((algebraMap B.Ring1 (Localization.Away s)).comp (iota1 hψ)).toAlgebra
        ∀ [Algebra (T1K π b₄ t κ ϖ) (Localization.Away s)]
          [@IsScalarTower (T1 π b₄ t κ) (T1K π b₄ t κ ϖ)
            (Localization.Away s) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
          Algebra.Etale (T1K π b₄ t κ ϖ) (Localization.Away s) := by
      rintro s rfl
      intros
      exact (etale_overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 h3 hE Sc ω hα hB hψ hψα).2
    intros
    exact key _ e1
  exact ⟨finite_gluedK b₄ hκ (pi_dvd hπ hε) (hc0_chart hψ) (hc1_chart hψ) (hloc0_chart hψ)
      (hloc1_chart hψ) (finite_iota0 hψ) (finite_iota1 hψ),
    etale_gluedK b₄ hκ (pi_dvd hπ hε) (hc0_chart hψ) (hc1_chart hψ) (hloc0_chart hψ)
      (hloc1_chart hψ) hBa hBb⟩

end

end TateGlue0

end SemistableReduction
