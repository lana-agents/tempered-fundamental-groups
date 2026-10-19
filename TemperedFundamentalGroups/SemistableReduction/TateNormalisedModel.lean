/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NormalisedModel
import TemperedFundamentalGroups.SemistableReduction.TateReduced
import TemperedFundamentalGroups.SemistableReduction.TateStructureMap

/-!
# The algebraized Tate coverings are the normalised models (Blueprint §12.8, M2.5)

Chart-wise form of M2.5 for the Tate coverings: the flat algebraization `(N, B, α)` of a Tate
covering, with its structure map `ψ : (TateTwoChart.twoChart ..).algStr → B` to the Tate model
(`TateGlue0.exists_flat_algebraization_structureMap`), is the normalised model of the Tate
model in the covering: `B₀` (resp. `B₁`) is the integral closure of the chart ring `T0`
(resp. `T1`) of the Tate model in `B₀[1/ϖ]` (resp. `B₁[1/ϖ]`).

* **`NodeEtaleGlue.Overlap.isIntegralClosure_ring0`**, `isIntegralClosure_ring1` (generic): for
  a flat algebraization of a system `S = V.system` with reduced level-`0` rings and a morphism of
  chart algebras `D.algStr → B`, `B_i` is the integral closure of `D.R_i` in `B_i[1/ϖ]`
  (`TwoChartTower.isIntegralClosure_shift0/1`, transported along `S = V.system`);
* **`TateGlue0.exists_normalisedModel`** (coverings étale over `D(1 + h)`) and
  **`TateGlue0.exists_normalisedModel_cusp`** (coverings ramified at the cusp): the flat
  algebraization together with `ψ`, such that `B.Ring0` is the integral closure of `T0` in
  `Localization.Away (B.const0 ϖ)` and `B.Ring1` the integral closure of `T1` in
  `Localization.Away (B.const1 ϖ)`. The reducedness of the level-`0` rings is
  `TateGlue0.isReduced_overlap`, `isReduced_overlapCusp`.
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

/-- **The algebraized covering is the normalised model, first chart** (generic): for a flat
algebraization `(N, B, α)` of a system `S = V.system` whose level-`0` ring `R0` is reduced, and a
morphism of chart algebras `D.algStr → B` from a base model `D`, `B₀` is the integral closure of
`D.R0` in `B₀[1/ϖ]`. -/
theorem isIntegralClosure_ring0
    {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Flat O[X] (Module.AEval' N.x0)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n))
    (hϖ : (Polynomial.C V.ϖ : O[X]) ∈ nonZeroDivisors O[X])
    [IsReduced (V.twoChart hθ hO 0).R0]
    {D : ProjectiveLine.TwoChartRings O} {φ : ProjectiveLine.ChartModule.Hom D.chartModule N}
    (h : D.algStr.IsHom B φ) {L : Type u} [CommRing L] [Algebra B.Ring0 L]
    [IsLocalization.Away (B.const0 V.ϖ) L] :
    letI := B.algR0 h
    letI : Algebra D.R0 L := ((algebraMap B.Ring0 L).comp (algebraMap D.R0 B.Ring0)).toAlgebra
    IsIntegralClosure B.Ring0 D.R0 L := by
  subst hS
  exact TwoChartTower.isIntegralClosure_shift0 (E := fun n ↦ V.twoChart hθ hO n) hα hB hϖ h

/-- **The algebraized covering is the normalised model, second chart** (generic). -/
theorem isIntegralClosure_ring1
    {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x1)]
    [Module.Flat O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n))
    (hϖ : (Polynomial.C V.ϖ : O[X]) ∈ nonZeroDivisors O[X])
    [IsReduced (V.twoChart hθ hO 0).R1]
    {D : ProjectiveLine.TwoChartRings O} {φ : ProjectiveLine.ChartModule.Hom D.chartModule N}
    (h : D.algStr.IsHom B φ) {L : Type u} [CommRing L] [Algebra B.Ring1 L]
    [IsLocalization.Away (B.const1 V.ϖ) L] :
    letI := B.algR1 h
    letI : Algebra D.R1 L := ((algebraMap B.Ring1 L).comp (algebraMap D.R1 B.Ring1)).toAlgebra
    IsIntegralClosure B.Ring1 D.R1 L := by
  subst hS
  exact TwoChartTower.isIntegralClosure_shift1 (E := fun n ↦ V.twoChart hθ hO n) hα hB hϖ h

end Overlap

end NodeEtaleGlue

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
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsDomain O] [(Ideal.span {ϖ}).IsMaximal]
  [IsAdicComplete (Ideal.span {ϖ}) O] (hϖ0 : ϖ ≠ 0)

include hϖ0

omit [IsNoetherianRing O] [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) O] in
lemma C_mem_nonZeroDivisors : (Polynomial.C ϖ : O[X]) ∈ nonZeroDivisors O[X] :=
  mem_nonZeroDivisors_of_ne_zero (Polynomial.C_ne_zero.2 hϖ0)

/-- **M2.5 for the Tate covering étale over `D(1 + h)`: the algebraization is the normalised
model.** The flat algebraization `(N, B, α)` of the covering (`exists_flat_algebraization'`) with
its structure map `ψ` to the Tate model (`exists_flat_algebraization_structureMap`) such that
`B.Ring0` is the integral closure of `T0` in `B.Ring0[1/ϖ]` and `B.Ring1` is the integral closure
of `T1` in `B.Ring1[1/ϖ]` (the `T_i`-algebra structures given by `ψ`). -/
theorem exists_normalisedModel (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) ∧
      ∃ (ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N)
        (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ),
        (∀ n, (α (n + 1)).comp ψ =
          structureMaps hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω n) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          IsIntegralClosure B.Ring0 (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          IsIntegralClosure B.Ring1 (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα⟩ :=
    exists_flat_algebraization_structureMap hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sp0 ω
  obtain ⟨hr0, hr1⟩ := isReduced_overlap hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω
  refine ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, ?_, ?_⟩
  · haveI : IsLocalization.Away (B.const0 (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ)
        (Localization.Away (B.const0 ϖ)) :=
      (inferInstance : IsLocalization.Away (B.const0 ϖ) _)
    exact NodeEtaleGlue.Overlap.isIntegralClosure_ring0 hθ.out hO
      (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (C_mem_nonZeroDivisors hϖ0) hψ
      (L := Localization.Away (B.const0 ϖ))
  · haveI : IsLocalization.Away (B.const1 (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ)
        (Localization.Away (B.const1 ϖ)) :=
      (inferInstance : IsLocalization.Away (B.const1 ϖ) _)
    exact NodeEtaleGlue.Overlap.isIntegralClosure_ring1 hθ.out hO
      (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB (C_mem_nonZeroDivisors hϖ0) hψ
      (L := Localization.Away (B.const1 ϖ))

/-- **M2.5 for the Tate covering ramified at the cusp: the algebraization is the normalised
model.** As `exists_normalisedModel`, for `overlapCusp` (`exists_flat_algebraization_cusp'`,
`exists_flat_algebraization_structureMap_cusp`). -/
theorem exists_normalisedModel_cusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) ∧
      ∃ (ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N)
        (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ),
        (∀ n, (α (n + 1)).comp ψ =
          structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          IsIntegralClosure B.Ring0 (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          IsIntegralClosure B.Ring1 (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα⟩ :=
    exists_flat_algebraization_structureMap_cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sc ω
  obtain ⟨hr0, hr1⟩ := isReduced_overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω
  refine ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, ?_, ?_⟩
  · haveI : IsLocalization.Away (B.const0 (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ)
        (Localization.Away (B.const0 ϖ)) :=
      (inferInstance : IsLocalization.Away (B.const0 ϖ) _)
    exact NodeEtaleGlue.Overlap.isIntegralClosure_ring0 hθ.out hO
      (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (C_mem_nonZeroDivisors hϖ0) hψ
      (L := Localization.Away (B.const0 ϖ))
  · haveI : IsLocalization.Away (B.const1 (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ)
        (Localization.Away (B.const1 ϖ)) :=
      (inferInstance : IsLocalization.Away (B.const1 ϖ) _)
    exact NodeEtaleGlue.Overlap.isIntegralClosure_ring1 hθ.out hO
      (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB (C_mem_nonZeroDivisors hϖ0) hψ
      (L := Localization.Away (B.const1 ϖ))

end TateGlue0

end

end SemistableReduction
