/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormCuspHom
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevel0

/-!
# The reductions of `algOfCuspLevelsW` at the bottom level (generic; MR12 I3)

For two-chart rings `P` with cusp level data (`NodeEtaleGlue.Overlap.algOfCuspLevelsW`) whose
level-`0` identification over `V₁` is the special-fibre one (`e1 0 = yEquiv ∘ ρX1 0`, L2):

* **`NodeEtaleGlue.Overlap.algOfCuspLevelsW_f1_one`**: the reduction at level `1` on the second
  chart is `yEquiv ∘ ρX1 0 ∘ q1 0`;
* **`NodeEtaleGlue.Overlap.algOfCuspLevelsW_f0_one`**: the reduction at level `1` on the first
  chart is `r0Equiv' ∘ ρX0 0 ∘ q0 0` (L3, `r0Equiv'_symm_levelEquiv0P`);
* **`NodeEtaleGlue.Overlap.algOfCuspLevelsW_base`**: a map `ψ1 : B0 → P.R1` compatible with the
  reductions `q1` reduces to the structure maps `B0 → Y n`.

These are the hypotheses `hA1`, `hA0`, `hψ1` of `NodeEtaleGlue.Overlap.mapH_spec` for
`A = algOfCuspLevelsW …`, stated generically so that concrete instances (the Tate curve) only
pass terms.
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
  {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing R]
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


omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **The reduction of `algOfCuspLevelsW` at level `1` on the second chart** is
`yEquiv ∘ ρX1 0 ∘ q1 0` (if `e1 0 = yEquiv ∘ ρX1 0`). -/
theorem algOfCuspLevelsW_f1_one [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)] (hJ0 : J θ (R := I.B 0) = ⊥)
    (he1 : letI := algC1 I.B I.qB I.C1 0
      ∀ y, e1.equiv 0 y = I.yEquiv hθ.out hO hJ0 (ρX1 0 y)) (b : P.R1) :
    (((V.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0
      hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α 1).f1 b : I.Y hθ.out 0) =
      I.yEquiv hθ.out hO hJ0 (ρX1 0 (q1 0 b)) :=
  he1 (q1 0 b)

omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **The reduction of `algOfCuspLevelsW` at level `1` on the first chart** is
`r0Equiv' ∘ ρX0 0 ∘ q0 0` for the bottom identification `bot` of the cusp patch (if
`e1 0 = yEquiv ∘ ρX1 0`; L3). -/
theorem algOfCuspLevelsW_f0_one [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)] (hJ0 : J θ (R := I.B 0) = ⊥)
    (hJ0' : J θ (R := Dp.R 0) = ⊥) (bot : V.P0.Bottom 0)
    (hbot : HEq bot (Dp.bottom hθ.out hO hJ0'))
    (he1 : letI := algC1 I.B I.qB I.C1 0
      ∀ y, e1.equiv 0 y = I.yEquiv hθ.out hO hJ0 (ρX1 0 y)) (b : P.R0) :
    (V.r0Equiv' hθ.out hO hJ0 bot).symm
      (((V.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω
        q0 hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α 1).f0 b) =
      ρX0 0 (q0 0 b) :=
  V.r0Equiv'_symm_levelEquiv0P hO Dp Vc hkI hT hP0 0 (e1.equiv 0) (ωn 0) (t 0) (ht 0) (htloc 0)
    (ρX1 0) (ρX0 0) (hρ 0) (hJm 0) (hψ1 0) (hx1 0) (hω 0) hJ0 hJ0' bot hbot he1 (q0 0 b)

omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **Maps of the base into the second chart compatible with the reductions reduce to the
structure maps** `B0 → Y n` under `algOfCuspLevelsW`. -/
theorem algOfCuspLevelsW_base [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)] (ψ1 : I.B0 → P.R1)
    (hψq : ∀ n r, q1 n (ψ1 r) = algebraMap I.B0 (X1 n) r) (n : ℕ) (r : I.B0) :
    (((V.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0
      hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1).α (n + 1)).f1 (ψ1 r) :
        I.Y hθ.out n) = algebraMap I.B0 (I.Y hθ.out n) r := by
  change e1.equiv n (q1 n (ψ1 r)) = _
  rw [hψq]
  exact (e1.equiv n).commutes r

set_option hygiene false in
/-- `algOfCuspLevelsW` with the variables of this section. -/
local notation "𝒜" => V.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm
  hψ1 hx1 hω q0 hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1

omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include hk1 in
/-- **The hypotheses `hsep`, `hψ1`, `hA1`, `hA0` of `mapH_spec` for `A = algOfCuspLevelsW …`**
(`algOfCuspLevelsW_sep1`, `_base`, `_f1_one`, `_f0_one`), for one instantiation at concrete data. -/
theorem algOfCuspLevelsW_spec [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    (hK : ∀ b : P.R1, (∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R1)) → b = 0)
    (hJ0 : J θ (R := I.B 0) = ⊥) (hJ0' : J θ (R := Dp.R 0) = ⊥) (bot : V.P0.Bottom 0)
    (hbot : HEq bot (Dp.bottom hθ.out hO hJ0'))
    (he1 : letI := algC1 I.B I.qB I.C1 0
      ∀ y, e1.equiv 0 y = I.yEquiv hθ.out hO hJ0 (ρX1 0 y))
    (ψ1 : I.B0 → P.R1) (hψq : ∀ n r, q1 n (ψ1 r) = algebraMap I.B0 (X1 n) r) :
    (∀ x : (𝒜).N.M1, (∀ n, ((𝒜).α (n + 1)).f1 x = 0) → x = 0) ∧
    (∀ n r, (((𝒜).α (n + 1)).f1 (ψ1 r) : I.Y hθ.out n) = algebraMap I.B0 (I.Y hθ.out n) r) ∧
    (∀ u, (((𝒜).α 1).f1 u : I.Y hθ.out 0) = I.yEquiv hθ.out hO hJ0 (ρX1 0 (q1 0 u))) ∧
    (∀ b, (V.r0Equiv' hθ.out hO hJ0 bot).symm (((𝒜).α 1).f0 b) = ρX0 0 (q0 0 b)) :=
  ⟨V.algOfCuspLevelsW_sep1 hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0
      hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1 hK,
    V.algOfCuspLevelsW_base hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0
      hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1 ψ1 hψq,
    V.algOfCuspLevelsW_f1_one hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω
      q0 hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1 hJ0 he1,
    V.algOfCuspLevelsW_f0_one hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω
      q0 hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ h hs0 hs1 hk0 hk1 hJ0 hJ0' bot hbot he1⟩

end

end Overlap

end NodeEtaleGlue

end SemistableReduction
