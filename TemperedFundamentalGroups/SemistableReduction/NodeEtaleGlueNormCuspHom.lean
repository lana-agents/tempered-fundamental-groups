/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormCusp
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormHom

/-!
# Two-chart rings with cusp level data as algebraizations (generic; MR12 I3)

In the setting of `NodeEtaleGlueNormCusp` (a covering `V` whose piece over `D(c₀)` is a cusp
patch, two-chart rings `P` with level data over `V₁` and `V₀`):

* **`NodeEtaleGlue.Overlap.algOfCuspLevels`**, **`algOfCuspLevelsW`**: `P` as an algebraization
  of `V.systemAt ϖ` (`algOfLevels` with `e0 = e0Cusp`; the `W` version with the common witnesses
  from `hW`, as in `exists_iso_of_cuspLevelsW`);
* `algOfCuspLevelsW_f1_succ`, `algOfCuspLevelsW_f0_succ`: its reductions; `algOfCuspLevelsW_sep1`:
  its second chart is separated if `⋂ₙ ϖⁿ⁺¹ P.R1 = 0`.
-/

universe u

open TensorProduct Polynomial ProjectiveLine ProjectiveLine.ChartModule

namespace SemistableReduction

namespace NodeEtaleGlue

namespace Overlap

noncomputable section

open FormalKummer AdmissibleLift FormalLevel FormalCuspLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]
  {R₁ : Type u} [CommRing R₁] [Algebra k R₁] {f₁ : R₁}
  {φ₁ : Node k (0 : k) →ₐ[k] Admissible.Hat f₁} {ψ₁ : Polynomial k →ₐ[k] Admissible.Hat f₁}
  {cov₁ : Admissible.Covering φ₁ ψ₁} {πL₁ : cov₁.ι → O}
  {I : Input θ cov₁ πL₁} (V : Overlap I) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  {hJ : ∀ j, J θ (R := R) ≤ 𝔪 j} {s : R} {E : ι → ℕ}
  {D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (E j) (𝔪 j)} {g : R}
  {hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j)}
  {hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j)}
  {hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g)}
  {ψk : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g)}
  {hψ : ψk Polynomial.X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s)}
  {hfin : Module.Finite (Rs θ R) (Cs θ R B)}
  {het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale}
  {hk : ∀ j i, ((D j).d i : k) ≠ 0}
  {πL : (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).ι → O}
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
  (Dp : PatchInput θ V.B' V.qB' V.C0 V.x0 V.c0 V.x0s V.c0s V.ϖ
    (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL)
  [algRI : ∀ l, Algebra R (Dp.R l)] [towerORI : ∀ l, IsScalarTower O R (Dp.R l)]
  [towerRII : ∀ l, IsScalarTower R (Dp.R (l + 1)) (Dp.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    LevelTower.Data (θ := θ) Dp.R (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL}
  {he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Dp.R l) r)}
  (Vc : CuspLevels 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T' he)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)) = Dp.algkR) (hT : HEq T' Dp.T)


variable (hP0 : V.P0 = Dp.piece hθ.out hO) (P : TwoChartRings O)
  {X1 : ℕ → Type u} [∀ n, CommRing (X1 n)] [∀ n, Algebra I.B0 (X1 n)] [∀ n, Algebra (I.B n) (X1 n)]
  {μ1 : ∀ n, X1 (n + 1) →+* X1 n} (e1 : I.LevelEquivFam hθ.out hO X1 μ1)
  {X0 : ℕ → Type u} [∀ n, CommRing (X0 n)] [∀ n, Algebra V.B0' (X0 n)]
  (μ0 : ∀ n, X0 (n + 1) →+* X0 n)
  (ωn : ∀ n, haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0 n) V.x0
    letI := awayAlg (W := V.W0) (C := X1 n) V.x1
    Localization.Away (algebraMap V.B0' (X0 n) V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 (X1 n) V.x1))
  (t : ∀ n, X0 n →+* Dp.R n ⊗[R] B)
  (ht : ∀ n r, t n (algebraMap V.B0' (X0 n) r) = algebraMap (Dp.R n) (Dp.R n ⊗[R] B)
    (algebraMap (V.B' n) (Dp.R n) (algebraMap V.B0' (V.B' n) r)))
  (htloc : ∀ n, letI := (t n).toAlgebra
    IsLocalization.Away (algebraMap V.B0' (X0 n) V.c0) (Dp.R n ⊗[R] B))
  (ρX1 : ∀ n, letI := algC1 I.B I.qB I.C1 n; X1 n →ₐ[I.B n] I.C1) (ρX0 : ∀ n, X0 n →+* V.C0)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ n x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he n (t n x) =
      Dp.ι₀ (ρX0 n x))
  {mJ : ℕ → ℕ} (hJm : ∀ n, J θ (R := V.B' n) ^ mJ n = ⊥)
  (hψ1 : ∀ n y, (letI := V.algBM n; Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
    (V.ψ hθ.out hO n (e1.equiv n y))) = V.γM n (ρX1 n y))
  (hx1 : ∀ n, ρX1 n (algebraMap I.B0 (X1 n) V.x1) = algebraMap I.Bs I.C1 V.x1s)
  (hω : ∀ n (x : X0 n), ∃ (y : X1 n) (k : ℕ),
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0 n) V.x0
      letI := awayAlg (W := V.W0) (C := X1 n) V.x1
      ωn n (algebraMap (X0 n) _ x) *
        algebraMap (X1 n) (Localization.Away (algebraMap I.B0 (X1 n) V.x1))
          (algebraMap I.B0 (X1 n) V.x1) ^ k = algebraMap (X1 n) _ y) ∧
    V.ω (algebraMap V.C0 _ (ρX0 n x)) *
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
          (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 n y))


variable (q0 : ∀ n, P.R0 →+* X0 n)
  (hq0O : ∀ n o, q0 n (algebraMap O P.R0 o) = algebraMap V.B0' (X0 n) (algebraMap O V.B0' o))
  (q1 : ∀ n, P.R1 →+* X1 n)
  (hq1O : ∀ n o, q1 n (algebraMap O P.R1 o) =
    algebraMap I.B0 (X1 n) (letI := V.algOB0; algebraMap O I.B0 o))
  (hx : ∀ n, q0 n P.x = algebraMap V.B0' (X0 n) V.x0)
  (hy : ∀ n, q1 n P.y = algebraMap I.B0 (X1 n) V.x1)
  (hW : ∀ n a m (k : ℕ), P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m →
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0 n) V.x0
      letI := awayAlg (W := V.W0) (C := X1 n) V.x1
      ωn n (algebraMap (X0 n) _ (q0 n a)) *
        algebraMap (X1 n) (Localization.Away (algebraMap I.B0 (X1 n) V.x1))
          (algebraMap I.B0 (X1 n) V.x1) ^ k = algebraMap (X1 n) _ (q1 n m)))
  (hμt : ∀ n x, t n (μ0 n x) = levelMap Dp.R n (t (n + 1) x))
  (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)
  (ϖ : O) (h : V.ϖ = ϖ)
  (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
  (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R0))
  (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R1))

omit hθ [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII
  [∀ n, Algebra (I.B n) (X1 n)] in
include hW hs0 hμ0 hμ1 in
/-- The common witnesses of consecutive levels (the hypothesis `hω2` of
`exists_iso_of_cuspLevels`) from the witnesses `hW` on the overlap of `P`. -/
theorem hω2_of_hW (n : ℕ) (x : X0 (n + 1)) : ∃ (y : X1 (n + 1)) (k : ℕ),
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0 (n + 1)) V.x0
      letI := awayAlg (W := V.W0) (C := X1 (n + 1)) V.x1
      ωn (n + 1) (algebraMap (X0 (n + 1)) _ x) *
        algebraMap (X1 (n + 1)) (Localization.Away (algebraMap I.B0 (X1 (n + 1)) V.x1))
          (algebraMap I.B0 (X1 (n + 1)) V.x1) ^ k = algebraMap (X1 (n + 1)) _ y) ∧
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0 n) V.x0
      letI := awayAlg (W := V.W0) (C := X1 n) V.x1
      ωn n (algebraMap (X0 n) _ (μ0 n x)) *
        algebraMap (X1 n) (Localization.Away (algebraMap I.B0 (X1 n) V.x1))
          (algebraMap I.B0 (X1 n) V.x1) ^ k = algebraMap (X1 n) _ (μ1 n y)) := by
  obtain ⟨b, rfl⟩ := hs0 (n + 1) x
  obtain ⟨m, k, hm⟩ := P.exists1 (P.ρ0 b)
  have h' : P.ρ0 b * P.ρ1 P.y ^ k = P.ρ1 m := by rw [P.ρ1_y, mul_comm]; exact hm
  refine ⟨q1 (n + 1) m, k, hW (n + 1) b m k h', ?_⟩
  rw [hμ0, hμ1]
  exact hW n b m k h'

/-- **Two-chart rings with cusp level data are an algebraization of the covering**
(`algOfLevels` with `e0 = e0Cusp`, the common witnesses from `hW`). -/
def algOfCuspLevelsW [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)] :
    AdicChartAlgSystem.Algebraization (V.systemAt hθ.out hO ϖ h) :=
  V.algOfLevels hθ.out hO P e1 q1 hq1O
    (V.e0Cusp hO Dp Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω) q0 hq0O hx hy
    (V.hρ_e0Cusp hO Dp Vc hkI hT hP0 P e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0 hq0O q1 hq1O
      hW)
    (fun n x ↦ V.f0_levelEquiv0P hO Dp Vc hkI hT hP0 n (e1.equiv n) (ωn n) (t n) (ht n) (htloc n)
      (ρX1 n) (ρX0 n) (hρ n) (hJm n) (hψ1 n) (hx1 n) (hω n) (e1.equiv (n + 1)) (ωn (n + 1))
      (t (n + 1)) (ht (n + 1)) (htloc (n + 1)) (ρX1 (n + 1)) (ρX0 (n + 1)) (hρ (n + 1))
      (hJm (n + 1)) (hψ1 (n + 1)) (hx1 (n + 1)) (hω (n + 1)) (μ1 n) (μ0 n) (e1.succ n) (hμt n)
      (V.hω2_of_hW P μ0 ωn q0 q1 hW hμ0 hμ1 hs0 n) x)
    hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- The reductions of `algOfCuspLevelsW` on the second chart: `e1 n ∘ q1 n`. -/
lemma algOfCuspLevelsW_f1_succ [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)] (n : ℕ) (b : P.R1) :
    ((V.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0
      hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α (n + 1)).f1 b =
      e1.equiv n (q1 n b) := rfl

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- The reductions of `algOfCuspLevelsW` on the first chart: `e0Cusp n ∘ q0 n`. -/
lemma algOfCuspLevelsW_f0_succ [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)] (n : ℕ) (b : P.R0) :
    ((V.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0
      hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α (n + 1)).f0 b =
      V.e0Cusp hO Dp Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω n (q0 n b) := rfl

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include hk1 in
/-- **The second chart of `algOfCuspLevelsW` is separated** if `⋂ₙ ϖⁿ⁺¹ P.R1 = 0`. -/
theorem algOfCuspLevelsW_sep1 [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    (hK : ∀ b : P.R1, (∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R1)) → b = 0)
    (b : P.R1)
    (hb : ∀ n, ((V.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1
      hx1 hω q0 hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α (n + 1)).f1 b = 0) :
    b = 0 :=
  V.algOfLevels_sep1 hθ.out hO P e1 q1 hq1O _ q0 hq0O hx hy _ _ hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1 hK b hb

end

end Overlap

end NodeEtaleGlue

end SemistableReduction
