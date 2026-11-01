/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelSucc
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevelsFam
import TemperedFundamentalGroups.SemistableReduction.TwoChartMapOfCharts
import TemperedFundamentalGroups.SemistableReduction.TwoChartAlgebraizationIso

/-!
# Recognising the algebraization of a glued covering (MR12 T2 S6, G5)

Let `V : NodeEtaleGlue.Overlap I` be the datum of a covering glued over the two charts and `P`
two-chart rings (e.g. the normalisations of the charts in a field). Suppose given, for every `n`,
identifications `e1 n : X1 n ≃ Y n`, `e0 n : X0 n ≃ R0 n` of the levels of the covering with
algebras `X1 n`, `X0 n`, commuting with successor maps `μ1`, `μ0`, and surjections
`q1 n : P.R1 → X1 n`, `q0 n : P.R0 → X0 n` with kernels `ϖⁿ⁺¹`, compatible with `μ1`, `μ0`, with
the coordinates and with the restrictions to the overlaps. Then:

* `NodeEtaleGlue.Overlap.f1Of`, `f0Of`: the maps `P.R1 → Y n`, `P.R0 → R0 n` (`e ∘ q`);
* **`NodeEtaleGlue.Overlap.βOf`**: the maps of two-chart rings `P → V.twoChart n`
  (`TwoChartMap.ofCharts`);
* **`NodeEtaleGlue.Overlap.exists_iso_of_levels`**: every algebraization of the covering
  (`Overlap.system`) is isomorphic to `P` as a chart algebra, compatibly with the reductions
  (`TwoChartTower.exists_iso_of_algebraization_shift`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ProjectiveLine ProjectiveLine.ChartModule

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (P : TwoChartRings O)

section Charts

variable {X1 : ℕ → Type u} [∀ n, CommRing (X1 n)] [∀ n, Algebra I.B0 (X1 n)]
  {μ1 : ∀ n, X1 (n + 1) →+* X1 n} (e1 : I.LevelEquivFam hθ hO X1 μ1)
  (q1 : ∀ n, P.R1 →+* X1 n)
  (hq1O : ∀ n o, q1 n (algebraMap O P.R1 o) =
    algebraMap I.B0 (X1 n) (letI := V.algOB0; algebraMap O I.B0 o))

/-- **The map `P.R1 → X1 n ≃ Y n`** over `O`. -/
def f1Of (n : ℕ) : P.R1 →ₐ[O] (V.twoChart hθ hO n).R1 :=
  letI := V.algOB0
  letI := V.algOY hθ n
  { ((e1.equiv n : X1 n →+* I.Y hθ n)).comp (q1 n) with
    commutes' := fun o ↦ by
      change e1.equiv n (q1 n (algebraMap O P.R1 o)) = _
      rw [hq1O, AlgEquiv.commutes]
      rfl }

lemma f1Of_apply (n : ℕ) (r : P.R1) : V.f1Of hθ hO P e1 q1 hq1O n r = e1.equiv n (q1 n r) := rfl

variable {X0 : ℕ → Type u} [∀ n, CommRing (X0 n)] [∀ n, Algebra V.B0' (X0 n)]
  (e0 : ∀ n, letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    X0 n ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n))
  (q0 : ∀ n, P.R0 →+* X0 n)
  (hq0O : ∀ n o, q0 n (algebraMap O P.R0 o) = algebraMap V.B0' (X0 n) (algebraMap O V.B0' o))

/-- **The map `P.R0 → X0 n ≃ R0 n`** over `O`. -/
def f0Of (n : ℕ) : P.R0 →ₐ[O] (V.twoChart hθ hO n).R0 := by
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  haveI := V.towerOE n
  haveI := V.towerOM n
  letI : Algebra O (X0 n) := ((algebraMap V.B0' (X0 n)).comp (algebraMap O V.B0')).toAlgebra
  haveI : IsScalarTower O V.B0' (X0 n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ((e0 n).toAlgHom.restrictScalars O).comp { q0 n with commutes' := hq0O n }

lemma f0Of_apply (n : ℕ) (r : P.R0) : V.f0Of hθ hO P e0 q0 hq0O n r = e0 n (q0 n r) := rfl

variable (hx : ∀ n, q0 n P.x = algebraMap V.B0' (X0 n) V.x0)
  (hy : ∀ n, q1 n P.y = algebraMap I.B0 (X1 n) V.x1)

include hx in
lemma f0Of_x (n : ℕ) : V.f0Of hθ hO P e0 q0 hq0O n P.x = (V.twoChart hθ hO n).x := by
  rw [f0Of_apply, hx, AlgEquiv.commutes]
  rfl

include hy in
lemma f1Of_y (n : ℕ) : V.f1Of hθ hO P e1 q1 hq1O n P.y = (V.twoChart hθ hO n).y := by
  rw [f1Of_apply, hy, AlgEquiv.commutes]
  rfl

variable (hρ : ∀ n a m (k : ℕ), P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m →
    (V.twoChart hθ hO n).ρ0 (V.f0Of hθ hO P e0 q0 hq0O n a) *
        (V.twoChart hθ hO n).ρ1 (V.twoChart hθ hO n).y ^ k =
      (V.twoChart hθ hO n).ρ1 (V.f1Of hθ hO P e1 q1 hq1O n m))

/-- **The maps of two-chart rings `P → V.twoChart n`** (`TwoChartMap.ofCharts`). -/
def βOf (n : ℕ) : TwoChartMap P (V.twoChart hθ hO n) :=
  TwoChartMap.ofCharts (V.f0Of hθ hO P e0 q0 hq0O n) (V.f1Of hθ hO P e1 q1 hq1O n)
    (V.f0Of_x hθ hO P e0 q0 hq0O hx n) (V.f1Of_y hθ hO P e1 q1 hq1O hy n) (hρ n)

variable {μ0 : ∀ n, X0 (n + 1) →+* X0 n}
  (he0 : ∀ n x, V.f0 hθ hO n (e0 (n + 1) x) = e0 n (μ0 n x))
  (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)

include he0 hμ0 in
lemma βOf_succ0 (n : ℕ) : (V.succ hθ hO n).f0.comp (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ
    (n + 1)).f0 = (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).f0 :=
  AlgHom.ext fun r ↦ (he0 n (q0 (n + 1) r)).trans (congrArg (e0 n) (hμ0 n r))

include hμ1 in
lemma βOf_succ1 (n : ℕ) : (V.succ hθ hO n).f1.comp (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ
    (n + 1)).f1 = (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).f1 :=
  AlgHom.ext fun r ↦ (e1.succ n (q1 (n + 1) r)).trans (congrArg (e1.equiv n) (hμ1 n r))

include hμ1 in
lemma βOf_succ01 (n : ℕ) : (V.succ hθ hO n).f01.comp (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ
    (n + 1)).f01 = (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).f01 :=
  TwoChartMap.comp_f01_of_f1 _ _ _ (V.βOf_succ1 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hμ1 n)

lemma ker_βOf0 (n : ℕ) : RingHom.ker (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).f0 =
    RingHom.ker (q0 n) := by
  ext r
  simp only [RingHom.mem_ker]
  exact map_eq_zero_iff (e0 n) (e0 n).injective

lemma ker_βOf1 (n : ℕ) : RingHom.ker (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).f1 =
    RingHom.ker (q1 n) := by
  ext r
  simp only [RingHom.mem_ker]
  exact map_eq_zero_iff (e1.equiv n) (e1.equiv n).injective

lemma surjective_βOf0 (hs : ∀ n, Function.Surjective (q0 n)) (n : ℕ) :
    Function.Surjective (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).f0 :=
  (e0 n).surjective.comp (hs n)

lemma surjective_βOf1 (hs : ∀ n, Function.Surjective (q1 n)) (n : ℕ) :
    Function.Surjective (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).f1 :=
  (e1.equiv n).surjective.comp (hs n)

include he0 hμ0 hμ1 in
/-- **The covering is the algebraization of `P`**: every algebraization `(N, B, α)` of the
covering (`Overlap.system`) is isomorphic to `P` as a chart algebra, compatibly with the
reductions `α n` and the maps `βOf` (shifted by one level). -/
theorem exists_iso_of_levels [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
    (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R0))
    (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R1))
    {N : ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N ((V.system hθ hO).M n)} {B : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), ((V.system hθ hO).tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom ((V.system hθ hO).alg n) (α n)) :
    ∃ (γ : Hom P.chartModule N) (δ : Hom N P.chartModule), γ.comp δ = Hom.id N ∧
      δ.comp γ = Hom.id P.chartModule ∧
      (∀ n, (α n).comp γ = (TwoChartTower.shiftCone (fun n ↦ V.twoChart hθ hO n)
        (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ) n).toHom) ∧
      (∀ n, (TwoChartTower.shiftCone (fun n ↦ V.twoChart hθ hO n)
        (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ) n).toHom.comp δ = α n) ∧
      P.algStr.IsHom B γ ∧ B.IsHom P.algStr δ :=
  TwoChartTower.exists_iso_of_algebraization_shift
    (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ)
    (V.βOf_succ0 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ he0 hμ0)
    (V.βOf_succ1 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hμ1)
    (V.βOf_succ01 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hμ1)
    (fun n ↦ V.surjective_f0 hθ hO n) (fun n ↦ I.surjective_Ymap hθ hO n)
    (fun n ↦ V.ker_f0' hθ hO n) (fun n ↦ V.ker_f1 hθ hO n) (V.kill0 hθ hO) (V.kill1 hθ hO)
    (fun n ↦ V.finite0 hθ hO n) (fun n ↦ V.finite1 hθ hO n)
    (V.surjective_βOf0 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hs0)
    (V.surjective_βOf1 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hs1)
    (fun n ↦ (V.ker_βOf0 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).trans (hk0 n))
    (fun n ↦ (V.ker_βOf1 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).trans (hk1 n))
    hα hαc hB

end Charts

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
