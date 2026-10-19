/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0V0
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower

/-!
# The algebraization of the Tate coverings (Blueprint §12.8, M2.3 (f) → M2.4)

For special-fibre coverings `Sp` over `V₁`, `Sp0` over `V₀` (étale outside the nodes) with the
overlap datum `ω` (`TateGlue0.overlap`):

* **`TateGlue0.system`**: the adic system of chart algebras on `ℙ¹_O` of the levels of the
  covering (`NodeEtaleGlue.Overlap.system`);
* **`TateGlue0.exists_algebraization`**: for `O` Noetherian and `ϖ`-adically complete, a coherent
  chart algebra on `ℙ¹_O` whose reductions modulo `ϖⁿ` are the levels of the covering
  (`NodeEtaleGlue.Overlap.exists_algebraization`).
-/

universe u

namespace SemistableReduction

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift

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
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0) (Sp0 : Special0 θ π b₄ t κ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (ω : Omega hκ hπ Sp Sp0)

/-- **The adic system of chart algebras of the Tate covering.** -/
abbrev system : ProjectiveLine.AdicChartAlgSystem (Ideal.span {ϖ}) :=
  (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).system hθ.out hO

/-- **Algebraization of the Tate covering**: a coherent chart algebra on `ℙ¹_O` whose reductions
modulo `ϖⁿ` are the levels of the covering. -/
theorem exists_algebraization [IsAdicComplete (Ideal.span {ϖ}) O] :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite (Polynomial O) (Module.AEval' N.x0))
      (_ : Module.Finite (Polynomial O) (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).tr h).comp (α n) = α m) ∧
      ∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n) := by
  haveI : IsAdicComplete (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).exists_algebraization hθ.out hO

end

end TateGlue0

end SemistableReduction
