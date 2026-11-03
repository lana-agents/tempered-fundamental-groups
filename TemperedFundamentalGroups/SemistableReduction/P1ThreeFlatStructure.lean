/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeFixedPoint
import TemperedFundamentalGroups.SemistableReduction.P1ThreeDegree

/-!
# Flat algebraizations of the lift with structure map (MR13 B4′)

For a datum `D` of a tame cover of `ℙ¹_k ∖ {0, 1, ā}`:

* **`P1Three.Datum.exists_flat_algebraization`**: an algebraization `L` of the lift (bundled,
  `AdicChartAlgSystem.Algebraization (systemD D)`), flat on both charts, with a structure map `ψ`
  from the model satisfying the full equation `(α (n + 1)) ∘ ψ = structureMaps n` (the form used by
  `etale_lift`, `specialFibreEquiv0_ψ`, `specialFibreEquiv1_ψ`, `finrank_lift`);
* `P1Three.structure_f1`: the pointwise form on the second chart (the form used by `ring1AlgAct`);
-/

universe u

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower ProjectiveLine Polynomial

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

section Structure

variable (Sp : Special1 O θ a) (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))
  (ω : OmegaC Sp S0.C0) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {N : ChartModule O}
  {α : ∀ n, ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)}
  {ψ : ChartModule.Hom (twoChart O a).chartModule N}

/-- **The structure map on the second chart, pointwise**: from the full structure-map equation. -/
theorem structure_f1 (hψα : ∀ n, (α (n + 1)).comp ψ = structureMaps Sp hϖ hker S0 ω hO n)
    (n : ℕ) (r : R1 O a) :
    ((α (n + 1)).f1 (ψ.f1 r) : (input Sp hϖ hker).Y hθ.out n) =
      algebraMap (input Sp hϖ hker).B0 ((input Sp hϖ hker).Y hθ.out n) r :=
  (congrArg (fun f ↦ f.f1 r) (hψα n)).trans rfl

end Structure

namespace Datum

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **A flat algebraization of the lift of a datum with its structure map.** -/
theorem exists_flat_algebraization [IsDomain O] [(Ideal.span {ϖ}).IsMaximal]
    [IsAdicComplete (Ideal.span {ϖ}) O] (hϖ0 : ϖ ≠ 0) (D : Datum O θ a) :
    ∃ L : AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D),
      Module.Flat O[X] (Module.AEval' L.N.x0) ∧ Module.Flat O[X] (Module.AEval' L.N.x1) ∧
      ∃ ψ : ChartModule.Hom (twoChart O a).chartModule L.N,
        (twoChart O a).algStr.IsHom L.B ψ ∧
        ∀ n, (L.α (n + 1)).comp ψ = structureMaps D.Sp hϖ hker D.S0 D.om hO n := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα⟩ :=
    exists_flat_algebraization_structureMap D.Sp hϖ hker D.S0 D.om hO hϖ0
  exact ⟨⟨N, B, α, hα, hc, hB⟩, hf0, hf1, ψ, hψ, hψα⟩


end Datum

end

end P1Three

end SemistableReduction
