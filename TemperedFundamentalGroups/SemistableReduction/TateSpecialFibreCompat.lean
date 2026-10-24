/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateSpecialFibre
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0SpecialCompat

/-!
# The special fibre of the algebraized Tate coverings as a chart datum (Blueprint §12.8, M2.5 (b))

For the flat algebraization `(N, B, α)` of a Tate covering with its structure map
`ψ : 𝒯 → B` (`TateGlue0.exists_etale_normalisedModel(_cusp)(_of_isElliptic)`), the special-fibre
identifications `B₀ ⧸ (ϖ) ≃ C0`, `B₁ ⧸ (ϖ) ≃ C1` (`specialFibreEquiv0/1(_cusp)`) are

* compatible with the overlap (`specialFibre01_r0/r1(_cusp)`): restricting to `B₀₁` and reducing
  gives `C1 → C1[1/h̄']` on `V₁` and `C0 → C0[1/h̄] ≃ω C1[1/h̄']` on `V₀`, i.e. the reduction of
  the algebraized covering is the special-fibre covering together with its glueing datum `ω`;
* linear over the Tate model (`specialFibreEquiv0/1_ψ(_cusp)`): the reduction of `ψ` is the
  structure map `T_i → C_i` of the given covering.

So the lift produced by M2 lifts the given covering of `𝒯_s` (chart-wise, with glueing and
structure maps).
-/

universe u

open Polynomial

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel

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
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

section Etale

variable (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0)
  {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N
    ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)}

/-- **The special fibre of the algebraized Tate covering over the overlap** (covering étale over
`D(1 + h)`): `B₀₁ → C1[1/h̄']`. -/
def specialFibre01 :=
  (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).specialFibre01 hθ.out hO (B := B) (α := α)
    (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) (J_Tn_zero_eq_bot hker _)

variable (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
    LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
  (hB : ∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n))

/-- The Tate special fibre over `V₁` is the generic one (`Overlap.specialFibreEquiv1`). -/
lemma specialFibreEquiv1_eq :
    specialFibreEquiv1 hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω hα hB =
      NodeEtaleGlue.Overlap.specialFibreEquiv1 hθ.out hO
        (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (J_Tn_zero_eq_bot hker _) :=
  rfl

/-- The Tate special fibre over `V₀` is the generic one (`Overlap.specialFibreEquiv0`). -/
lemma specialFibreEquiv0_eq :
    specialFibreEquiv0 hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω hα hB =
      (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).specialFibreEquiv0 hθ.out hO
        (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (J_Tn_zero_eq_bot hker _)
        (piece0Bottom hϖ hker Sp0) :=
  rfl

/-- Restriction from `V₁` reduces to `C1 → C1[1/h̄']`. -/
theorem specialFibre01_r1 (b : B.Ring1) :
    specialFibre01 hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω (α := α) (B.r1Hom b) =
      algebraMap (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).C1 _
        (NodeEtaleGlue.Overlap.specialFibreEquiv1 hθ.out hO
          (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (J_Tn_zero_eq_bot hker _)
          (Ideal.Quotient.mk _ b)) :=
  NodeEtaleGlue.Overlap.specialFibre01_r1 (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω) hθ.out hO
    hα hB (J_Tn_zero_eq_bot hker _) (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) b

/-- Restriction from `V₀` reduces to `C0 → C0[1/h̄] ≃ω C1[1/h̄']`. -/
theorem specialFibre01_r0 (b : B.Ring0) :
    specialFibre01 hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω (α := α) (B.r0Hom b) =
      (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ω
        (algebraMap (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).C0 _
          ((overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).specialFibreEquiv0 hθ.out hO
          (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (J_Tn_zero_eq_bot hker _)
          (piece0Bottom hϖ hker Sp0)
            (Ideal.Quotient.mk _ b))) :=
  NodeEtaleGlue.Overlap.specialFibre01_r0 (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω) hθ.out hO
    hα hB (J_Tn_zero_eq_bot hker _) (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω)
    (piece0Bottom hϖ hker Sp0) b

variable {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N}
  (hc : ∀ n, (α (n + 1)).comp ψ = structureMaps hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω n)

include hc in
/-- **The special fibre over `V₁` is linear over the Tate model.** -/
theorem specialFibreEquiv1_ψ (r : T1 π b₄ t κ) :
    NodeEtaleGlue.Overlap.specialFibreEquiv1 hθ.out hO
          (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (J_Tn_zero_eq_bot hker _)
        (Ideal.Quotient.mk _ (ψ.f1 r)) =
      (letI := (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).algC10 0
       algebraMap (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).B0
        (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).C1 r) :=
  NodeEtaleGlue.Overlap.specialFibreEquiv1_ψ (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω)
    hθ.out hO hα hB (J_Tn_zero_eq_bot hker _) (baseMap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω)
    (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hc r

include hc in
/-- **The special fibre over `V₀` is linear over the Tate model.** -/
theorem specialFibreEquiv0_ψ (r : T0 π b₄ t κ) :
    (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).specialFibreEquiv0 hθ.out hO
          (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (J_Tn_zero_eq_bot hker _)
          (piece0Bottom hϖ hker Sp0)
        (Ideal.Quotient.mk _ (ψ.f0 r)) =
      (letI := (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).algC0' 0
       algebraMap (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).B0'
        (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).C0 r) :=
  NodeEtaleGlue.Overlap.specialFibreEquiv0_ψ (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω)
    hθ.out hO hα hB (J_Tn_zero_eq_bot hker _) (baseMap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω)
    (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) (piece0Bottom hϖ hker Sp0) hc r

end Etale

section Cusp

variable (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
  (ω : OmegaC hκ hπ Sp Sc.C0)
  {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N
    ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)}

/-- **The special fibre of the algebraized Tate covering over the overlap** (covering ramified at
the cusp): `B₀₁ → C1[1/h̄']`. -/
def specialFibre01Cusp :=
  (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).specialFibre01 hθ.out hO (B := B) (α := α)
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) (J_Tn_zero_eq_bot hker _)

variable (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
    LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
  (hB : ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n))

/-- The Tate special fibre over `V₁` is the generic one (`Overlap.specialFibreEquiv1`). -/
lemma specialFibreEquiv1_cusp_eq :
    specialFibreEquiv1_cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω hα hB =
      NodeEtaleGlue.Overlap.specialFibreEquiv1 hθ.out hO
        (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (J_Tn_zero_eq_bot hker _) :=
  rfl

/-- The Tate special fibre over `V₀` is the generic one (`Overlap.specialFibreEquiv0`). -/
lemma specialFibreEquiv0_cusp_eq :
    specialFibreEquiv0_cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω hα hB =
      (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).specialFibreEquiv0 hθ.out hO
        (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (J_Tn_zero_eq_bot hker _)
        ((CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)).bottom hθ.out hO
          (J_Tn_zero_eq_bot hker _)) :=
  rfl

/-- Restriction from `V₁` reduces to `C1 → C1[1/h̄']`. -/
theorem specialFibre01Cusp_r1 (b : B.Ring1) :
    specialFibre01Cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω (α := α) (B.r1Hom b) =
      algebraMap (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).C1 _
        (NodeEtaleGlue.Overlap.specialFibreEquiv1 hθ.out hO
          (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (J_Tn_zero_eq_bot hker _)
          (Ideal.Quotient.mk _ b)) :=
  NodeEtaleGlue.Overlap.specialFibre01_r1 (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω)
    hθ.out hO hα hB (J_Tn_zero_eq_bot hker _)
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) b

/-- Restriction from `V₀` reduces to `C0 → C0[1/h̄] ≃ω C1[1/h̄']`. -/
theorem specialFibre01Cusp_r0 (b : B.Ring0) :
    specialFibre01Cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω (α := α) (B.r0Hom b) =
      (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ω
        (algebraMap (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).C0 _
          ((overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).specialFibreEquiv0 hθ.out hO
          (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (J_Tn_zero_eq_bot hker _)
          ((CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)).bottom hθ.out hO
          (J_Tn_zero_eq_bot hker _))
            (Ideal.Quotient.mk _ b))) :=
  NodeEtaleGlue.Overlap.specialFibre01_r0 (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω)
    hθ.out hO hα hB (J_Tn_zero_eq_bot hker _) (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω)
    ((CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)).bottom hθ.out hO
          (J_Tn_zero_eq_bot hker _)) b

variable {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N}
  (hc : ∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n)

include hc in
/-- **The special fibre over `V₁` is linear over the Tate model.** -/
theorem specialFibreEquiv1_ψ_cusp (r : T1 π b₄ t κ) :
    NodeEtaleGlue.Overlap.specialFibreEquiv1 hθ.out hO
          (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (J_Tn_zero_eq_bot hker _)
        (Ideal.Quotient.mk _ (ψ.f1 r)) =
      (letI := (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).algC10 0
       algebraMap (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).B0
        (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).C1 r) :=
  NodeEtaleGlue.Overlap.specialFibreEquiv1_ψ (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω)
    hθ.out hO hα hB (J_Tn_zero_eq_bot hker _) (baseMapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω)
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hc r

include hc in
/-- **The special fibre over `V₀` is linear over the Tate model.** -/
theorem specialFibreEquiv0_ψ_cusp (r : T0 π b₄ t κ) :
    (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).specialFibreEquiv0 hθ.out hO
          (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (J_Tn_zero_eq_bot hker _)
          ((CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)).bottom hθ.out hO
          (J_Tn_zero_eq_bot hker _))
        (Ideal.Quotient.mk _ (ψ.f0 r)) =
      (letI := (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).algC0' 0
       algebraMap (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).B0'
        (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).C0 r) :=
  NodeEtaleGlue.Overlap.specialFibreEquiv0_ψ (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω)
    hθ.out hO hα hB (J_Tn_zero_eq_bot hker _) (baseMapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω)
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω)
    ((CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)).bottom hθ.out hO
          (J_Tn_zero_eq_bot hker _)) hc r

end Cusp

end TateGlue0

end

end SemistableReduction
