/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Tower
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Cusp
import TemperedFundamentalGroups.SemistableReduction.CuspInput

/-!
# The algebraization of Tate coverings ramified at the cusp (Blueprint §12.8, M2.3 (f) → M2.4)

For a special-fibre covering `Sp` over `V₁` (étale outside the nodes) and special-fibre data
`Sc : CuspTower.CuspSpecial` over `D(1 + h) ⊆ V₀` (an admissible covering without nodes and with
cusp factors along `h`, tamely ramified over the origin `[0:1:0]`), with the overlap datum
`ω : C0[1/h̄] ≃ₐ C1[1/h̄']`:

* **`TateGlue0.overlapCusp`**: the `NodeEtaleGlue.Overlap` whose piece over `D(1 + h)` is the cusp
  patch `CuspTower.cuspPiece` (the regularity of `h` on the levels: `isSMulRegular_h0`);
* **`TateGlue0.systemCusp`**, **`TateGlue0.exists_algebraization_cusp`**: the adic system of chart
  algebras on `ℙ¹_O` of the levels of the covering, and its algebraization (`O` Noetherian and
  `ϖ`-adically complete).
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
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0)
  (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (ω : OmegaC hκ hπ Sp Sc.C0)

/-- **The Tate covering ramified at the cusp over `V₀`**: the cusp patch over `D(1 + h)`. -/
def overlapCusp : NodeEtaleGlue.Overlap (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm) :=
  overlapP hκ hπ hε hϖ π' hπ' hker Sp hm Sc.C0 ω
    (CuspTower.cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO)

/-- **The adic system of chart algebras of the Tate covering ramified at the cusp.** -/
abbrev systemCusp : ProjectiveLine.AdicChartAlgSystem (Ideal.span {ϖ}) :=
  (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).system hθ.out hO

/-- **Algebraization of the Tate covering ramified at the cusp**: a coherent chart algebra on
`ℙ¹_O` whose reductions modulo `ϖⁿ` are the levels of the covering. -/
theorem exists_algebraization_cusp [IsAdicComplete (Ideal.span {ϖ}) O] :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite (Polynomial O) (Module.AEval' N.x0))
      (_ : Module.Finite (Polynomial O) (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).tr h).comp (α n) = α m) ∧
      ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n) := by
  haveI : IsAdicComplete (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).exists_algebraization hθ.out hO

end

end TateGlue0

end SemistableReduction
