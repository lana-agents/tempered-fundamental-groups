/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHomDatum
import TemperedFundamentalGroups.SemistableReduction.P1ThreeEtale
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueStructureHom

/-!
# The morphisms of the lifts respect the structure maps (MR13, (f) step 4 bridge)

For a datum `D` of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` and an algebraization `L` of its lift:

* **`P1Three.Datum.exists_structureMap`**: the structure map `ψ : 𝒳 → L` from the model `twoChart`
  (reducing to `R1 = B0 → Y n` on the second chart);
* **`Datum.algMap_f1_structure`**: for a morphism `f : D → D'` the induced morphism of
  algebraizations commutes with the structure maps on the second chart (`L'` flat there), so it
  is `R1`-linear on `B₁` (used in `P1ThreeHomAction`).
-/

universe u

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower ProjectiveLine Polynomial

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

namespace Datum

variable (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {D D' : Datum O θ a} [IsAdicComplete (Ideal.span {ϖ}) O]

/-- **The structure map of an algebraization of the lift** of a datum: a morphism of chart
algebras `ψ` from the model `twoChart` reducing to `R1 = B0 → Y n` on the second chart. -/
theorem exists_structureMap (D : Datum O θ a)
    (L : AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D)) :
    ∃ ψ : ChartModule.Hom (twoChart O a).chartModule L.N, (twoChart O a).algStr.IsHom L.B ψ ∧
      ∀ n r, ((L.α (n + 1)).f1 (ψ.f1 r) : (input D.Sp hϖ hker).Y hθ.out n) =
        algebraMap (input D.Sp hϖ hker).B0 ((input D.Sp hϖ hker).Y hθ.out n) r := by
  haveI := finite_x0 O a
  haveI := finite_x1 O a
  exact (overlap D.Sp hϖ hker D.S0 D.om hO).exists_structureMap_systemAt hθ.out hO ϖ rfl
    (baseMap D.Sp hϖ hker D.S0 D.om hO) L

/-- **The morphisms of algebraizations commute with the structure maps on the second chart.** -/
theorem algMap_f1_structure [IsDomain O] (hϖu : ¬IsUnit ϖ) (f : D.Hom D')
    (L : AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D))
    (L' : AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D'))
    [Module.Flat O[X] (Module.AEval' L'.N.x1)]
    (ψ : ChartModule.Hom (twoChart O a).chartModule L.N)
    (ψ' : ChartModule.Hom (twoChart O a).chartModule L'.N)
    (hψα : ∀ n r, ((L.α (n + 1)).f1 (ψ.f1 r) : (input D.Sp hϖ hker).Y hθ.out n) =
      algebraMap (input D.Sp hϖ hker).B0 ((input D.Sp hϖ hker).Y hθ.out n) r)
    (hψα' : ∀ n r, ((L'.α (n + 1)).f1 (ψ'.f1 r) : (input D'.Sp hϖ hker).Y hθ.out n) =
      algebraMap (input D'.Sp hϖ hker).B0 ((input D'.Sp hϖ hker).Y hθ.out n) r)
    (r : R1 O a) :
    (algMap hϖ hker ha0 ha1 hO f L L').f1 (ψ.f1 r) = ψ'.f1 r :=
  (overlap D.Sp hϖ hker D.S0 D.om hO).map_f1_structure (overlap D'.Sp hϖ hker D'.S0 D'.om hO)
    hθ.out hO ϖ rfl rfl (systemMap hϖ hker ha0 ha1 hO f)
    (fun n ↦ yMap hϖ hker D.Sp D'.Sp f.φ1 n) (fun _ _ ↦ rfl)
    (baseMap D.Sp hϖ hker D.S0 D.om hO) (baseMap D'.Sp hϖ hker D'.S0 D'.om hO)
    (fun n r ↦ yMap_algebraMap hϖ hker D.Sp D'.Sp f.φ1 n r) L L' hϖu ψ ψ' hψα hψα' r

end Datum

end

end P1Three

end SemistableReduction
