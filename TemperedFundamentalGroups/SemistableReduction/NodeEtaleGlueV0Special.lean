/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSpecial
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower
import TemperedFundamentalGroups.SemistableReduction.NormalisedModel

/-!
# The special fibre of the algebraized covering is the given covering (Blueprint §12.8, M2.5 (b))

For a flat algebraization `(N, B, α)` of the tower `S = V.system` of an `Overlap` (generic; Tate
case `TateGlue0.system`), whose bottom level has `J = 0` on the base chart:

* **`NodeEtaleGlue.Overlap.specialFibreEquiv1`**: `B₁ ⧸ (ϖ) ≃ C1` — the special fibre of the
  algebraized covering over the second chart is the given special-fibre covering `C1`
  (`TwoChartTower.specialFibreEquiv1`: `B₁/ϖ ≅ Y 0`, and `Input.yEquiv`: `Y 0 ≅ C1`).
-/

universe u

open Polynomial

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} {V : Overlap I}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The special fibre of the algebraized covering, second chart** (generic): for a flat
algebraization `(N, B, α)` of `S = V.system` with `J = 0` on the bottom base chart `B 0`,
`B₁ ⧸ (ϖ) ≃ C1`. -/
def specialFibreEquiv1
    {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S)
    {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) (hJ0 : J θ (R := I.B 0) = ⊥) :
    B.Ring1 ⧸ Ideal.span {B.const1 V.ϖ} ≃+* I.C1 := by
  subst hS
  letI := I.algC10 0
  exact (TwoChartTower.specialFibreEquiv1 (E := fun n ↦ V.twoChart hθ hO n) hα hB).trans
    (I.yEquiv hθ hO hJ0).symm.toRingEquiv

/-- `specialFibreEquiv1` for a tower whose bottom base level is killed by `J` (`mB 0 = 1`). -/
def specialFibreEquiv1'
    {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S)
    {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) (hm1 : I.mB 0 = 1) :
    B.Ring1 ⧸ Ideal.span {B.const1 V.ϖ} ≃+* I.C1 :=
  specialFibreEquiv1 hθ hO hS hα hB (by simpa [hm1] using I.hJB 0)

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
