/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormLevels
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSpecialHom

/-!
# Two-chart rings with level data as algebraizations, and their morphisms (generic; MR12 I3)

Let `V : NodeEtaleGlue.Overlap I` be a covering glued over the two charts and `P` two-chart rings
with level data as in `NodeEtaleGlue.Overlap.exists_iso_of_levels` (identifications `e1`, `e0`
of the levels with quotients `X1 n`, `X0 n` of the charts of `P`, reductions `q1`, `q0` with
kernels `ϖⁿ⁺¹`).

* **`NodeEtaleGlue.Overlap.algOfLevels`**: `P` itself is an algebraization of the adic system
  `V.systemAt ϖ` of the covering, with reductions `α (n + 1) = βOf n` (`algOfLevels_α_succ`), so
  a morphism of adic systems induces a morphism of chart algebras between two such `P`
  (`AdicChartAlgSystem.Algebraization.map`);
* `algOfLevels_f1_succ`, `algOfLevels_f0_succ`: the reductions on the charts;
* **`AdicChartAlgSystem.Algebraization.map_f1_eq`**: the second chart of such a morphism is
  determined by its reductions, if the second chart of the target is `ϖ`-adically separated
  (`algOfLevels_sep1` for `P`, from `⋂ₙ ϖⁿ⁺¹ P.R1 = 0`);
* **`NodeEtaleGlue.Overlap.map_f1_succ`**: the reductions of the morphism induced by
  `Overlap.systemMap … y …` on the second chart are given by `y`.
-/

universe u

open Polynomial

namespace ProjectiveLine.AdicChartAlgSystem.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} [IsAdicComplete I A]
  {S S' : AdicChartAlgSystem I}

/-- **The second chart of a morphism of algebraizations is determined by its reductions**: if
the second chart of `L'` is separated for the reductions `α (n + 1)` and `u' ∈ L'.N.M1` has the
reductions of `γ (u)` for `u ∈ L.N.M1`, then `(map γ L L').f1 u = u'`. -/
theorem map_f1_eq (γ : Hom S S') (L : Algebraization S) (L' : Algebraization S')
    (hsep : ∀ x : L'.N.M1, (∀ n, (L'.α (n + 1)).f1 x = 0) → x = 0) (u : L.N.M1)
    (u' : L'.N.M1) (hu : ∀ n, (γ.f (n + 1)).f1 ((L.α (n + 1)).f1 u) = (L'.α (n + 1)).f1 u') :
    (map γ L L').f1 u = u' := by
  rw [← sub_eq_zero]
  refine hsep _ fun n ↦ ?_
  have e := LinearMap.congr_fun (congrArg ChartModule.Hom.f1 (comp_map γ L L' (n + 1))) u
  rw [map_sub, sub_eq_zero]
  exact e.trans (hu n)

end ProjectiveLine.AdicChartAlgSystem.Algebraization

namespace SemistableReduction

open ProjectiveLine ProjectiveLine.ChartModule AdmissibleLift

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
  {X0 : ℕ → Type u} [∀ n, CommRing (X0 n)] [∀ n, Algebra V.B0' (X0 n)]
  (e0 : ∀ n, letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    X0 n ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n))
  (q0 : ∀ n, P.R0 →+* X0 n)
  (hq0O : ∀ n o, q0 n (algebraMap O P.R0 o) = algebraMap V.B0' (X0 n) (algebraMap O V.B0' o))
  (hx : ∀ n, q0 n P.x = algebraMap V.B0' (X0 n) V.x0)
  (hy : ∀ n, q1 n P.y = algebraMap I.B0 (X1 n) V.x1)
  (hρ : ∀ n a m (k : ℕ), P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m →
    (V.twoChart hθ hO n).ρ0 (V.f0Of hθ hO P e0 q0 hq0O n a) *
        (V.twoChart hθ hO n).ρ1 (V.twoChart hθ hO n).y ^ k =
      (V.twoChart hθ hO n).ρ1 (V.f1Of hθ hO P e1 q1 hq1O n m))
  {μ0 : ∀ n, X0 (n + 1) →+* X0 n}
  (he0 : ∀ n x, V.f0 hθ hO n (e0 (n + 1) x) = e0 n (μ0 n x))
  (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)
  (ϖ : O) (h : V.ϖ = ϖ)
  [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
  [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
  (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
  (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R0))
  (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R1))

/-- **Two-chart rings with level data are an algebraization of the covering**: `P` with the
reductions `shiftCone (βOf …)` (level `n + 1`: `βOf n = (e0 n ∘ q0 n, e1 n ∘ q1 n)`) is an
algebraization of `V.systemAt ϖ`. -/
def algOfLevels : AdicChartAlgSystem.Algebraization (V.systemAt hθ hO ϖ h) where
  N := P.chartModule
  B := P.algStr
  α n := (TwoChartTower.shiftCone (fun n ↦ V.twoChart hθ hO n)
    (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ) n).toHom
  hα n := ⟨TwoChartTower.shiftCone_surj0 _
      (V.surjective_βOf0 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hs0) n,
    TwoChartTower.shiftCone_surj1 _
      (V.surjective_βOf1 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hs1) n,
    TwoChartTower.shiftCone_ker0 _
      (fun n ↦ (V.ker_βOf0 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).trans (hk0 n)) n,
    TwoChartTower.shiftCone_ker1 _
      (fun n ↦ (V.ker_βOf1 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).trans (hk1 n)) n⟩
  hc _ _ hmn := TwoChartTower.shiftCone_comp _
    (V.βOf_succ0 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ he0 hμ0)
    (V.βOf_succ1 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hμ1)
    (V.βOf_succ01 hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ hμ1) hmn
  hB n := TwoChartTower.shiftCone_isHom _ n

lemma algOfLevels_N :
    (V.algOfLevels hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ he0 hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).N =
      P.chartModule := rfl

lemma algOfLevels_α_succ (n : ℕ) :
    (V.algOfLevels hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ he0 hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α
      (n + 1) = (V.βOf hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ n).toHom := rfl

/-- The reductions of `algOfLevels` on the second chart: `e1 n ∘ q1 n`. -/
lemma algOfLevels_f1_succ (n : ℕ) (b : P.R1) :
    ((V.algOfLevels hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ he0 hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α
      (n + 1)).f1 b = e1.equiv n (q1 n b) := rfl

/-- The reductions of `algOfLevels` on the first chart: `e0 n ∘ q0 n`. -/
lemma algOfLevels_f0_succ (n : ℕ) (b : P.R0) :
    ((V.algOfLevels hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ he0 hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α
      (n + 1)).f0 b = e0 n (q0 n b) := rfl

include hk1 in
/-- **The second chart of `algOfLevels` is separated** if `⋂ₙ ϖⁿ⁺¹ P.R1 = 0`. -/
theorem algOfLevels_sep1
    (hK : ∀ b : P.R1, (∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R1)) → b = 0)
    (b : P.R1)
    (hb : ∀ n, ((V.algOfLevels hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy hρ he0 hμ0 hμ1 ϖ h hs0 hs1
      hk0 hk1).α (n + 1)).f1 b = 0) : b = 0 := by
  refine hK b fun n ↦ ?_
  rw [← hk1 n, RingHom.mem_ker]
  have e := hb n
  rw [algOfLevels_f1_succ] at e
  exact (map_eq_zero_iff (e1.equiv n) (e1.equiv n).injective).mp e

end Charts

section Map

variable {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O} {I' : Input θ cov₀' πL'}
  (V' : Overlap I') [IsNoetherianRing O] (ϖ : O) (h : V.ϖ = ϖ) (h' : V'.ϖ = ϖ)
  [IsAdicComplete (Ideal.span {ϖ}) O]

/-- **The reductions of the morphism induced by `Overlap.systemMap … y …` on the
second chart are given by `y`.** -/
theorem map_f1_succ (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ n (o : O), y n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : ∀ n, V.P0.P n →+* V'.P0.P n)
    (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ n z, V'.ψ hθ hO n (y n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z))
    (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
    (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e))
    (L : AdicChartAlgSystem.Algebraization (V.systemAt hθ hO ϖ h))
    (L' : AdicChartAlgSystem.Algebraization (V'.systemAt hθ hO ϖ h')) (n : ℕ) (b : L.N.M1) :
    ((L'.α (n + 1)).f1 ((AdicChartAlgSystem.Algebraization.map
        (V.systemMap V' hθ hO ϖ h h' y hy1 hyO p hp0 hpO hψ hyS hpS) L L').f1 b) : I'.Y hθ n) =
      y n ((L.α (n + 1)).f1 b) :=
  LinearMap.congr_fun (congrArg ChartModule.Hom.f1
    (AdicChartAlgSystem.Algebraization.comp_map _ L L' (n + 1))) b

end Map

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
