/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.PowFlatTate
import TemperedFundamentalGroups.SemistableReduction.TateFibre

/-!
# Flat algebraization of the Tate coverings (Blueprint §12.8, M2.4, step 3f)

For `O` a Noetherian domain, `ϖ`-adically complete with `(ϖ)` maximal (e.g. a complete DVR), the
algebraizations of the Tate coverings (étale over `D(1 + h)`, resp. ramified at the cusp) are flat
over both charts `O[X]` of `ℙ¹_O`: `TateGlue0.exists_flat_algebraization` and
`exists_flat_algebraization_cusp` (`TateFibre`) with the `ϖ`-purity of the levels
(`TateGlue0.system_hpure0/1`, `systemCusp_hpure0/1`, `PowFlatTate`) — the fibrewise flatness
criterion (`NilpotentFlatness`) applied levelwise.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel

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
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsDomain O] [(Ideal.span {ϖ}).IsMaximal]
  [IsAdicComplete (Ideal.span {ϖ}) O] (hϖ0 : ϖ ≠ 0)

include hϖ0

/-- **Flat algebraization of a Tate covering étale over `D(1 + h)`**: a coherent chart algebra on
`ℙ¹_O`, flat over both charts, whose reductions modulo `ϖⁿ` are the levels of the covering. -/
theorem exists_flat_algebraization' (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) :
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
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) :=
  exists_flat_algebraization hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω
    (system_hpure0 hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sp0 ω)
    (system_hpure1 hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sp0 ω)

/-- **Flat algebraization of a Tate covering ramified at the cusp**: a coherent chart algebra on
`ℙ¹_O`, flat over both charts, whose reductions modulo `ϖⁿ` are the levels of the covering. -/
theorem exists_flat_algebraization_cusp'
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
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) :=
  exists_flat_algebraization_cusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω
    (systemCusp_hpure0 hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sc ω)
    (systemCusp_hpure1 hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sc ω)

end

end TateGlue0

end SemistableReduction
