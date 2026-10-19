/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower
import TemperedFundamentalGroups.SemistableReduction.TwoChartStructureMap

/-!
# The structure maps of the levels of a covering to the base model (Blueprint §12.8, M2.5)

For `V : NodeEtaleGlue.Overlap I` the charts `V₀ = Spec B0'`, `V₁ = Spec B0` and their overlap
`W0` map to every level of the covering (`B0' → P0 n`, `B0 → Y n`, `W0 → Q n`). Given two-chart
rings `D` of the base model `𝒳` (over `ℙ¹_O`) with ring maps of its rings to `B0'`, `B0`, `W0`
compatible with the coordinates and the restriction maps (**`Overlap.BaseMap V D`**; in the
Tate case the identities, `D = TateTwoChart.twoChart`), this file builds:

* **`BaseMap.β n : TwoChartMap D (V.twoChart n)`**: the structure map of level `n` of the
  covering to the base model;
* `BaseMap.succ0/succ1/succ01`: compatibility with the successor maps `Overlap.succ`
  (elementwise, the form of `TwoChartTower.exists_structureMap`);
* **`BaseMap.exists_structureMap`**: for an algebraization `(N, B, α)` of `V.system`, a morphism
  of chart algebras `ψ : D.algStr → B` with `α (n+1) ∘ ψ = β n` (`BaseMap.βs`: `β n` as a map into
  the level `n + 1` of `V.system`) — the structure map `𝒴 → 𝒳`; `exists_structureMap'`: the same
  for a system `S` with `V.system = S` (`BaseMap.βS`).
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
  {I : Input θ cov₀ πL}

/-- **Maps of the base model to the charts of a covering**: ring maps of the rings of two-chart
rings `D` (the base model `𝒳` over `ℙ¹_O`) to the charts `B0'` (over `U₀`), `B0` (over `U₁`)
and the overlap `W0` of `V`, `O`-linear on the charts, sending the coordinates `x`, `y` to
`x₀`, `x₁` and compatible with the restriction maps. -/
structure BaseMap (V : Overlap I) (D : ProjectiveLine.TwoChartRings O) where
  /-- on `U₀` -/
  a0 : D.R0 →+* V.B0'
  /-- on `U₁` -/
  a1 : D.R1 →+* I.B0
  /-- on the overlap -/
  a01 : D.R01 →+* V.W0
  hO0 : ∀ o, a0 (algebraMap O D.R0 o) = algebraMap O V.B0' o
  hO1 : ∀ o, a1 (algebraMap O D.R1 o) = (letI := V.algOB0; algebraMap O I.B0 o)
  hx : a0 D.x = V.x0
  hy : a1 D.y = V.x1
  h0 : ∀ r, a01 (D.ρ0 r) = algebraMap V.B0' V.W0 (a0 r)
  h1 : ∀ r, a01 (D.ρ1 r) = algebraMap I.B0 V.W0 (a1 r)

namespace BaseMap

variable {V : Overlap I} {D : ProjectiveLine.TwoChartRings O} (b : BaseMap V D)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-- `a0` as a map of `O`-algebras. -/
def a0' : D.R0 →ₐ[O] V.B0' :=
  { b.a0 with commutes' := b.hO0 }

/-- `a1` as a map of `O`-algebras. -/
def a1' : letI := V.algOB0; D.R1 →ₐ[O] I.B0 :=
  letI := V.algOB0
  { b.a1 with commutes' := b.hO1 }

/-- **The structure map of level `n` over `U₀`**: `D.R0 → B0' → Q n ×_{M n} P0 n`. -/
def f0 : letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    letI := V.algOQ hθ n; haveI := V.towerOQ hθ n; haveI := V.towerOE n; haveI := V.towerOM n
    D.R0 →ₐ[O] ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n) := by
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  haveI := V.towerOE n
  haveI := V.towerOM n
  exact ((Algebra.ofId V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n))).restrictScalars O).comp
    b.a0'

lemma f0_apply (r : D.R0) : b.f0 hθ hO n r =
    (letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
     algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) (b.a0 r)) := rfl

/-- **The structure map of level `n` over `U₁`**: `D.R1 → B0 → Y n`. -/
def f1 : letI := V.algOY hθ n; D.R1 →ₐ[O] I.Y hθ n := by
  letI := V.algOB0
  letI := V.algOY hθ n
  haveI := V.towerOY hθ n
  exact (IsScalarTower.toAlgHom O I.B0 (I.Y hθ n)).comp b.a1'

lemma f1_apply (r : D.R1) : b.f1 hθ n r = algebraMap I.B0 (I.Y hθ n) (b.a1 r) := rfl

lemma a01_algebraMap (o : O) :
    b.a01 (algebraMap O D.R01 o) = algebraMap V.B0' V.W0 (algebraMap O V.B0' o) := by
  rw [← D.ρ0.commutes o, b.h0, b.hO0]

/-- **The structure map of level `n` over the overlap**: `D.R01 → W0 → Q n`. -/
def f01 : letI := V.algOQ hθ n; D.R01 →ₐ[O] V.Q hθ n :=
  letI := V.algOQ hθ n
  letI := V.algW0Q hθ n
  { (algebraMap V.W0 (V.Q hθ n)).comp b.a01 with
    commutes' := fun o ↦ by
      change algebraMap V.W0 (V.Q hθ n) (b.a01 (algebraMap O D.R01 o)) = _
      rw [b.a01_algebraMap]
      rfl }

lemma f01_apply (r : D.R01) :
    b.f01 hθ n r = (letI := V.algW0Q hθ n; algebraMap V.W0 (V.Q hθ n) (b.a01 r)) := rfl

/-- **The structure map of level `n` of the covering to the base model** `D`. -/
def β : TwoChartMap (A := O) D (V.twoChart hθ hO n) := by
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  letI := V.alg0'E n
  haveI := V.towerOE n
  letI := V.alg0'M n
  haveI := V.towerOM n
  letI := V.algOY hθ n
  letI := V.algW0Q hθ n
  exact
    { f0 := b.f0 hθ hO n
      f1 := b.f1 hθ n
      f01 := b.f01 hθ n
      hx := by
        change algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) (b.a0 D.x) =
          algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) V.x0
        rw [b.hx]
      hy := by
        change algebraMap I.B0 (I.Y hθ n) (b.a1 D.y) = algebraMap I.B0 (I.Y hθ n) V.x1
        rw [b.hy]
      hu := by
        change algebraMap V.W0 (V.Q hθ n) (b.a01 D.u) =
          algebraMap V.W0 (V.Q hθ n) (algebraMap V.B0' V.W0 V.x0)
        rw [← D.ρ0_x, b.h0, b.hx]
      h0 := fun r ↦ by
        change algebraMap V.W0 (V.Q hθ n) (b.a01 (D.ρ0 r)) =
          ZariskiTwo.fst (V.ρ0a hθ hO n) (V.ρ0b n) (algebraMap V.B0' _ (b.a0 r))
        rw [AlgHom.commutes, b.h0]
        rfl
      h1 := fun r ↦ by
        change algebraMap V.W0 (V.Q hθ n) (b.a01 (D.ρ1 r)) =
          algebraMap (I.Y hθ n) (V.Q hθ n) (algebraMap I.B0 (I.Y hθ n) (b.a1 r))
        rw [b.h1, V.algW0Q_algebraMap hθ n,
          ← IsScalarTower.algebraMap_apply I.B0 (I.Y hθ n) (V.Q hθ n)] }

lemma β_f0 (r : D.R0) : (b.β hθ hO n).f0 r = b.f0 hθ hO n r := rfl

lemma β_f1 (r : D.R1) : (b.β hθ hO n).f1 r = b.f1 hθ n r := rfl

lemma β_f01 (r : D.R01) : (b.β hθ hO n).f01 r = b.f01 hθ n r := rfl

/-! ### Compatibility with the successor maps -/

lemma succ0 (r : D.R0) :
    (V.succ hθ hO n).f0 ((b.β hθ hO (n + 1)).f0 r) = (b.β hθ hO n).f0 r := by
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'Q hθ n
  letI := V.alg0'E (n + 1)
  letI := V.alg0'E n
  letI := V.alg0'M (n + 1)
  letI := V.alg0'M n
  exact (V.f0 hθ hO n).commutes (b.a0 r)

lemma succ1 (r : D.R1) :
    (V.succ hθ hO n).f1 ((b.β hθ hO (n + 1)).f1 r) = (b.β hθ hO n).f1 r :=
  (I.Ymap hθ hO n).commutes (b.a1 r)

lemma succ01 (r : D.R01) :
    (V.succ hθ hO n).f01 ((b.β hθ hO (n + 1)).f01 r) = (b.β hθ hO n).f01 r :=
  V.qmap_W0 hθ hO n (b.a01 r)

/-! ### The structure map of the algebraization -/

/-- `β n` as a morphism of chart modules into the level `n + 1` of the shifted system
`Overlap.system` (the covering modulo `ϖⁿ⁺¹`). Stating the reductions of the structure map
with this ascribed type avoids defeq checks `(V.system ..).M (n + 1) = (V.twoChart n).chartModule`
at concrete instances. -/
def βs : ProjectiveLine.ChartModule.Hom D.chartModule ((V.system hθ hO).M (n + 1)) :=
  (b.β hθ hO n).toHom

lemma βs_eq : b.βs hθ hO n = (b.β hθ hO n).toHom := rfl

/-- **The structure map `𝒴 → 𝒳`**: an algebraization `(N, B, α)` of the tower of the covering
(`Overlap.system`) receives a morphism of chart algebras `ψ : D.algStr → B` from the base model
reducing to the structure maps `β n` of the levels. -/
theorem exists_structureMap [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x1)]
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((V.system hθ hO).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hc : ∀ m n (h : m ≤ n), ((V.system hθ hO).tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom ((V.system hθ hO).alg n) (α n)) :
    ∃ ψ : ProjectiveLine.ChartModule.Hom D.chartModule N, D.algStr.IsHom B ψ ∧
      ∀ n, (α (n + 1)).comp ψ = b.βs hθ hO n :=
  TwoChartTower.exists_structureMap (fun n ↦ V.succ hθ hO n) (b.succ0 hθ hO) (b.succ1 hθ hO)
    (b.succ01 hθ hO) hα hc hB

/-- `β n` as a morphism into the level `n + 1` of any system `S` equal to `V.system` (for
instances where `S` is a named abbreviation of `V.system`: comparing the levels of the two forms
by unfolding is expensive, the equation `S = V.system` at the top level is not). -/
def βS {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S) :
    ProjectiveLine.ChartModule.Hom D.chartModule (S.M (n + 1)) := by
  subst hS
  exact b.βs hθ hO n

lemma βS_rfl : b.βS hθ hO n rfl = b.βs hθ hO n := rfl

/-- **The structure map `𝒴 → 𝒳`** for an algebraization of a system `S = V.system`
(`exists_structureMap` transported along `hS`). -/
theorem exists_structureMap' [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x1)]
    {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) :
    ∃ ψ : ProjectiveLine.ChartModule.Hom D.chartModule N, D.algStr.IsHom B ψ ∧
      ∀ n, (α (n + 1)).comp ψ = b.βS hθ hO n hS := by
  subst hS
  exact b.exists_structureMap hθ hO hα hc hB

end BaseMap

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
