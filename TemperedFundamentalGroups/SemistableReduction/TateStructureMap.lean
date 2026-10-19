/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Base
import TemperedFundamentalGroups.SemistableReduction.TateChartFinite
import TemperedFundamentalGroups.SemistableReduction.TateFlatAlgebraization

/-!
# The structure map of the algebraized Tate coverings to the Tate model (Blueprint §12.8, M2.5)

The charts `T0`, `T1` and the overlap `T01` of the Tate model (`TateTwoChart.twoChart`) are the
base charts `B0'`, `B0`, `W0` of the Tate coverings (`TateGlue0.overlapP`), so the identities form
a `NodeEtaleGlue.Overlap.BaseMap` (**`TateGlue0.baseMapP`**). Its structure maps
`β n : TwoChartMap (TateTwoChart.twoChart ..) (twoChart n)` (`T0 → T0n → R0`, `T1 → T1n → Y n`,
`T01 → T01n → Q n`) algebraize (`NodeEtaleGlue.Overlap.BaseMap.exists_structureMap`):

* **`TateGlue0.exists_flat_algebraization_structureMap`** (coverings étale over `D(1 + h)`) and
  **`exists_flat_algebraization_structureMap_cusp`** (coverings ramified at the cusp): the flat
  algebraization `(N, B, α)` of the covering together with a morphism of chart algebras
  `ψ : (TateTwoChart.twoChart ..).algStr → B` with `α (n + 1) ∘ ψ = β n` — the structure map
  `𝒴 → 𝒳` of the algebraized covering to the Tate model.
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

/-- **The Tate model maps to the charts of the Tate coverings by the identities**
(`T0 = B0'`, `T1 = B0`, `T01 = W0`). -/
def baseMapP (C0 : Type u) [CommRing C0] [Algebra (T0s θ π b₄ t κ) C0] (ω : OmegaC hκ hπ Sp C0)
    (P0 : NodeEtaleGlue.Piece0 θ (B ϖ π b₄ t κ) (EtaleTower.q (T0 π b₄ t κ) hϖ) C0
      (h0 π b₄ t κ) (c0 π b₄ t κ) (Ideal.Quotient.mk _ (h0 π b₄ t κ))
      (Ideal.Quotient.mk _ (c0 π b₄ t κ)) ϖ) :
    NodeEtaleGlue.Overlap.BaseMap (overlapP hκ hπ hε hϖ π' hπ' hker Sp hm C0 ω P0)
      (TateTwoChart.twoChart π b₄ t κ) where
  a0 := RingHom.id (T0 π b₄ t κ)
  a1 := RingHom.id (T1 π b₄ t κ)
  a01 := RingHom.id (T01 π b₄ t κ)
  hO0 _ := rfl
  hO1 _ := rfl
  hx := rfl
  hy := rfl
  h0 _ := rfl
  h1 _ := rfl

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- The base map for the Tate covering étale over `D(1 + h)` (`overlap`). -/
def baseMap (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) :
    NodeEtaleGlue.Overlap.BaseMap (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω)
      (TateTwoChart.twoChart π b₄ t κ) :=
  baseMapP hκ hπ hε hϖ π' hπ' hker Sp hm Sp0.C ω (piece0 (hϖ := hϖ) (hker := hker) (Sp0 := Sp0))

/-- The base map for the Tate covering ramified at the cusp (`overlapCusp`). -/
def baseMapCusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) :
    NodeEtaleGlue.Overlap.BaseMap (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω)
      (TateTwoChart.twoChart π b₄ t κ) :=
  baseMapP hκ hπ hε hϖ π' hπ' hker Sp hm Sc.C0 ω
    (CuspTower.cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO)

lemma system_eq (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) :
    (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).system hθ.out hO =
      system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω := rfl

lemma systemCusp_eq
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) :
    (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).system hθ.out hO =
      systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω := rfl

/-- **The structure maps of the levels of the Tate covering étale over `D(1 + h)` to the Tate
model**, as maps into the level `n + 1` of `system` (`β n` of `baseMap`, `T0 → T0n → R0`,
`T1 → T1n → Y n`, `T01 → T01n → Q n`). -/
def structureMaps (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) (n : ℕ) :
    ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule
      ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M (n + 1)) :=
  (baseMap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).βS hθ.out hO n
    (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω)

/-- **The structure maps of the levels of the Tate covering ramified at the cusp to the Tate
model**, as maps into the level `n + 1` of `systemCusp`. -/
def structureMapsCusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) (n : ℕ) :
    ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule
      ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M (n + 1)) :=
  (baseMapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω).βS hθ.out hO n
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω)

variable [IsDomain O] [(Ideal.span {ϖ}).IsMaximal]
  [IsAdicComplete (Ideal.span {ϖ}) O] (hϖ0 : ϖ ≠ 0)

include hϖ0

/-- **The structure map of the algebraized Tate covering étale over `D(1 + h)`**: the flat
algebraization `(N, B, α)` of the covering (`exists_flat_algebraization'`) receives a morphism
of chart algebras `ψ` from the Tate model reducing to the structure maps `β n` of the levels. -/
theorem exists_flat_algebraization_structureMap (Sp0 : Special0 θ π b₄ t κ)
    (ω : Omega hκ hπ Sp Sp0) :
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
      ∃ ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N,
        (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ ∧
        ∀ n, (α (n + 1)).comp ψ =
          structureMaps hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω n := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1⟩ :=
    exists_flat_algebraization' hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sp0 ω
  haveI := TateTwoChart.finite_x0 π b₄ t κ
  haveI := TateTwoChart.finite_x1 π b₄ t κ
  haveI : IsAdicComplete (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1,
    (baseMap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).exists_structureMap' hθ.out hO
      (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hc hB⟩

/-- **The structure map of the algebraized Tate covering ramified at the cusp**: the flat
algebraization `(N, B, α)` of the covering (`exists_flat_algebraization_cusp'`) receives a
morphism of chart algebras `ψ` from the Tate model reducing to the structure maps `β n`. -/
theorem exists_flat_algebraization_structureMap_cusp
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
      ∃ ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N,
        (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ ∧
        ∀ n, (α (n + 1)).comp ψ =
          structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1⟩ :=
    exists_flat_algebraization_cusp' hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sc ω
  haveI := TateTwoChart.finite_x0 π b₄ t κ
  haveI := TateTwoChart.finite_x1 π b₄ t κ
  haveI : IsAdicComplete
      (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1,
    (baseMapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω).exists_structureMap' hθ.out hO
      (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hc hB⟩

end

end TateGlue0

end SemistableReduction
