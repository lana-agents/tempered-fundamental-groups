/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNormalisedModel
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Special
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0PatchSpecial

/-!
# The special fibre of the algebraized Tate coverings (Blueprint §12.8, M2.5 (b))

For the flat algebraization `(N, B, α)` of a Tate covering (`TateGlue0.exists_normalisedModel`,
`exists_normalisedModel_cusp`, `exists_etale_normalisedModel(_cusp)`), the special fibre of the
algebraized covering over the chart `V₁` is the given special-fibre covering `C1`
(`TateGlue1.Special1`): **`TateGlue0.specialFibreEquiv1`**, **`specialFibreEquiv1_cusp`**:
`B₁ ⧸ (ϖ) ≃ C1`; over the chart `V₀`: **`TateGlue0.specialFibreEquiv0`**,
**`specialFibreEquiv0_cusp`**: `B₀ ⧸ (ϖ) ≃ C0` (bottom identifications of the pieces over
`D(1 + h)`: `piece0Bottom` for the étale lifts, `PatchInput.bottom` for the cusp patch). So the
lift produced by M2 lifts the given covering over both charts.
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

/-- **The special fibre of the algebraized Tate covering over `V₁` is the given covering**
(covering étale over `D(1 + h)`): `B₁ ⧸ (ϖ) ≃ C1`. -/
def specialFibreEquiv1 (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0)
    {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n)) :
    B.Ring1 ⧸ Ideal.span {B.const1 ϖ} ≃+* Sp.C1 :=
  NodeEtaleGlue.Overlap.specialFibreEquiv1' hθ.out hO
    (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB rfl

/-- **The special fibre of the algebraized Tate covering over `V₁` is the given covering**
(covering ramified at the cusp): `B₁ ⧸ (ϖ) ≃ C1`. -/
def specialFibreEquiv1_cusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n)) :
    B.Ring1 ⧸ Ideal.span {B.const1 ϖ} ≃+* Sp.C1 :=
  NodeEtaleGlue.Overlap.specialFibreEquiv1' hθ.out hO
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB rfl

omit hθ [IsNoetherianRing O] in
include hker in
/-- `J = 0` on the bottom level of a ϖ-adic tower of charts. -/
lemma J_Tn_zero_eq_bot (T : Type u) [CommRing T] [Algebra O T] :
    J θ (R := EtaleTower.Tn ϖ T 0) = ⊥ := by
  simpa using EtaleTower.hJ (T := T) hker 0

/-- **The bottom identification of the étale lifts over `D(1 + h)`.** -/
def piece0Bottom (Sp0 : Special0 θ π b₄ t κ) :
    (piece0 (hϖ := hϖ) (hker := hker) (Sp0 := Sp0)).Bottom 0 := by
  letI : ∀ n, Algebra O (E0 Sp0 hϖ hker n).E := algOE0 hϖ hker Sp0
  haveI : ∀ n, IsScalarTower O (B ϖ π b₄ t κ n) (E0 Sp0 hϖ hker n).E := towerOE0 hϖ hker Sp0
  haveI : ∀ n, IsScalarTower (T0 π b₄ t κ) (B ϖ π b₄ t κ (n + 1)) (B ϖ π b₄ t κ n) :=
    fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact NodeEtaleGlue.Piece0.bottomOfEtale (fun n ↦ (E0 Sp0 hϖ hker n).E)
    (fun n ↦ (E0 Sp0 hϖ hker n).σ) (fun n ↦ (E0 Sp0 hϖ hker n).hb)
    (fun n ↦ (E0 Sp0 hϖ hker n).hfin) (fun _ ↦ rfl) (sE0 Sp0 hϖ hker)
    (Sp0.succ_algebraMap hϖ hker) (Sp0.σ_succ' hϖ hker) (surjective_sE0 Sp0 hϖ hker)
    (hkE0 hϖ hker Sp0) (J_Tn_zero_eq_bot hker _)

/-- **The special fibre of the algebraized Tate covering over `V₀` is the given covering**
(covering étale over `D(1 + h)`): `B₀ ⧸ (ϖ) ≃ C0`. -/
def specialFibreEquiv0 (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0)
    {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n)) :
    B.Ring0 ⧸ Ideal.span {B.const0 ϖ} ≃+* Sp0.C :=
  NodeEtaleGlue.Overlap.specialFibreEquiv0 _ hθ.out hO
    (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (J_Tn_zero_eq_bot hker _)
    (piece0Bottom hϖ hker Sp0)

/-- **The special fibre of the algebraized Tate covering over `V₀` is the given covering**
(covering ramified at the cusp): `B₀ ⧸ (ϖ) ≃ C0`. -/
def specialFibreEquiv0_cusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n)) :
    B.Ring0 ⧸ Ideal.span {B.const0 ϖ} ≃+* Sc.C0 :=
  NodeEtaleGlue.Overlap.specialFibreEquiv0 _ hθ.out hO
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (J_Tn_zero_eq_bot hker _)
    ((CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)).bottom hθ.out hO
      (J_Tn_zero_eq_bot hker _))

end TateGlue0

end

end SemistableReduction
