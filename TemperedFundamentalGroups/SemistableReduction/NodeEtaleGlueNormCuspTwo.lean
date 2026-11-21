/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormCuspSpec
import TemperedFundamentalGroups.SemistableReduction.OverlapNodeHomHMap

/-!
# Lifting morphisms of special-fibre data to two-chart rings with cusp level data (generic; MR12 I3)

For two overlaps `V`, `V'` of node-only coverings whose pieces over `D(c₀)` are cusp patches, two
two-chart rings `P`, `P'` with cusp level data (`NodeEtaleGlue.Overlap.algOfCuspLevelsW`, with
the level-`0` identifications of the special fibre, L2) and the data of a morphism
`NodeEtaleGlue.Overlap.systemMapH` of the adic systems of `V` and `V'`:

* **`NodeEtaleGlue.Overlap.exists_hom_of_cuspLevelsW`**: there is a morphism
  `Φ : P.chartModule → P'.chartModule` of chart algebras which is `β0` on the base (for maps
  `ψ1`, `ψ1'` of the bases into the second charts compatible with the reductions) and reduces to
  `φ1` on the second chart and to `φ0` on the first chart (at level `0`).

The statement mentions only `P`, `P'`, their level-`0` reductions and `φ0`, `φ1`, not the
algebraizations: concrete instances (the Tate curve, MR12 I3 surjectivity) apply it in one step.
Proof: `algOfCuspLevelsW_spec` for both sides and `mapH_spec`.
-/

universe u

open TensorProduct Polynomial ProjectiveLine ProjectiveLine.ChartModule

namespace SemistableReduction

namespace NodeEtaleGlue

namespace Overlap

noncomputable section

open FormalKummer AdmissibleLift FormalLevel FormalCuspLevel LevelTower

-- the overlaps and the data of `systemMapH` (as in `OverlapNodeHomHMap`)
variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]
  {R₀ : Type u} [cR₀ : CommRing R₀] [aR₀ : Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
variable {I : Input θ cov₀ πL} {I' : Input θ cov₀' πL'} (V : Overlap I) (V' : Overlap I')
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hR : I'.R = I.R) (hc : HEq I'.commRingR I.commRingR) (ha : HEq I'.algOR I.algOR)
  (hk : HEq I'.algkR I.algkR) (hs : HEq I'.algSuccR I.algSuccR) (hF : HEq I'.T.f I.T.f)
  (hE : HEq I'.T.e I.T.e)
  [hκ₀ : IsEmpty cov₀.κ] [hκ₀' : IsEmpty cov₀'.κ] (φ : cov₀.C →ₐ[R₀] cov₀'.C)
  {cu cv : ∀ n, FormalPatchLevel.Hat (I.T.f n)}
  (hcd : ∀ n, NodeCoord (I.T.level n) (cu n) (cv n))
  {cu' cv' : ∀ n, FormalPatchLevel.Hat (I'.T.f n)}
  (hcd' : ∀ n, NodeCoord (I'.T.level n) (cu' n) (cv' n))
  (hcu : ∀ n, HEq (cu' n) (cu n)) (hcv : ∀ n, HEq (cv' n) (cv n))
  (hbal : ∀ n, NodeBalanced I.T.hfe πL πL' φ n)
  (e : ∀ n, I.E n →+* I'.E n)
  (he : ∀ n, e n (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n))
  (β : ∀ n, I.B n →+* I'.B n) (hβJ : ∀ n, (J θ (R := I.B n)).map (β n) ≤ J θ (R := I'.B n))
  (hβa : ∀ n, β n (I.a n) = I'.a n)
  (heβ : ∀ n r, e n (algebraMap (I.B n) (I.E n) r) = algebraMap (I'.B n) (I'.E n) (β n r))
  (hβR : ∀ n r, HEq (algebraMap (I'.B n) (I'.R n) (β n r)) (algebraMap (I.B n) (I.R n) r))
  (φ1 : I.C1 →+* I'.C1) (hφc : ∀ c, φ (I.ι₀ c) = I'.ι₀ (φ1 c))
  (ℓb : Localization.Away (algebraMap I.Bs I.C1 I.bbar) →+*
    Localization.Away (algebraMap I'.Bs I'.C1 I'.bbar))
  (hℓb : ∀ c, ℓb (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
  (hσE : ∀ n x, (letI := NodeEtaleGlue.algC1 I'.B I'.qB I'.C1 n
      I'.σE n (Ideal.Quotient.mk _ (e n x))) =
    ℓb (letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n; I.σE n (Ideal.Quotient.mk _ x)))
  (heS : ∀ n x, I'.sE n (e (n + 1) x) = e n (I.sE n x))
  (β0 : I.B0 →+* I'.B0)
  (hβ0 : ∀ n b, β n (algebraMap I.B0 (I.B n) b) = algebraMap I'.B0 (I'.B n) (β0 b))
  (hx1 : β0 V.x1 = V'.x1) (hg0 : β0 V.g = V'.g)
  (hβ0O : ∀ o, β0 (letI := V.algOB0; algebraMap O I.B0 o) =
    (letI := V'.algOB0; algebraMap O I'.B0 o))
  (p : ∀ n, V.P0.P n →+* V'.P0.P n)
  (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
    algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
  (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
  (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e))
  (hpB : ∀ n b, V.mM V' n (p n) (hp0 n) (letI := V.alg0M n; algebraMap I.B0 (V.M n) b) =
    (letI := V'.alg0M n; algebraMap I'.B0 (V'.M n) (β0 b)))
  (hJ0 : J θ (R := I.B 0) = ⊥) (hJ0' : J θ (R := I'.B 0) = ⊥)
  (hpγ : ∀ c m, Ideal.Quotient.mk (letI := V.algBM 0; EtaleNil.JB (J θ (R := I.B 0)) (V.M 0)) m =
      V.γM 0 c →
    Ideal.Quotient.mk (letI := V'.algBM 0; EtaleNil.JB (J θ (R := I'.B 0)) (V'.M 0))
      (V.mM V' 0 (p 0) (hp0 0) m) = V'.γM 0 (φ1 c))
  [IsNoetherianRing O] (ϖ : O) (h : V.ϖ = ϖ) (h' : V'.ϖ = ϖ) [IsAdicComplete (Ideal.span {ϖ}) O]

-- the overlaps of the cusp level data, spelled independently (equal to `V`, `V'` up to `HEq`)
variable {R₀s : Type u} [cR₀s : CommRing R₀s] [aR₀s : Algebra k R₀s] {f₀s : R₀s}
  {φ₀s φ₀s' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀s}
  {ψ₀s : Polynomial k →ₐ[k] Admissible.Hat f₀s}
  {cov₀s : Admissible.Covering φ₀s ψ₀s} {cov₀s' : Admissible.Covering φ₀s' ψ₀s}
  {πLs : cov₀s.ι → O} {πLs' : cov₀s'.ι → O}
  {Is : Input θ cov₀s πLs} {Is' : Input θ cov₀s' πLs'} (Vs : Overlap Is) (Vs' : Overlap Is')

-- the cusp level data of the first side (as in `NodeEtaleGlueNormCuspSpec`)
variable {Rc : Type u} [CommRing Rc] [Algebra O Rc]
  {Bc : Type u} [CommRing Bc] [Algebra Rc Bc] [IsNoetherianRing Rc]
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪 : ι → Ideal Rc} [∀ j, (𝔪 j).IsMaximal]
  {hJ : ∀ j, J θ (R := Rc) ≤ 𝔪 j} {sc : Rc} {Ec : ι → ℕ}
  {Dc : ∀ j, PointCuspFormData (θ := θ) (B := Bc) sc (Ec j) (𝔪 j)} {gc : Rc}
  {hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j)}
  {hfk : ∀ j, fbar θ gc ∈ sIdeal (θ := θ) (𝔪 j)}
  {hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ gc}).radical}
  {φc : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ gc)}
  {ψk : Polynomial k →ₐ[k] Admissible.Hat (fbar θ gc)}
  {hψ : ψk Polynomial.X = algebraMap (Rs θ Rc) _ (Ideal.Quotient.mk _ sc)}
  {hfin : Module.Finite (Rs θ Rc) (Cs θ Rc Bc)}
  {het : (Localization.awayMap (algebraMap (Rs θ Rc) (Cs θ Rc Bc)) (fbar θ gc)).Etale}
  {hkc : ∀ j i, ((Dc j).d i : k) ≠ 0}
  {πc : (FormalCuspLevel.cov₀ 𝔪 hJ Dc hinjk hfk hradk φc ψk hψ hfin het hkc).ι → O}
  (Dp : PatchInput θ Vs.B' Vs.qB' Vs.C0 Vs.x0 Vs.c0 Vs.x0s Vs.c0s Vs.ϖ
    (FormalCuspLevel.cov₀ 𝔪 hJ Dc hinjk hfk hradk φc ψk hψ hfin het hkc) πc)
  [algRI : ∀ l, Algebra Rc (Dp.R l)] [towerORI : ∀ l, IsScalarTower O Rc (Dp.R l)]
  [towerRII : ∀ l, IsScalarTower Rc (Dp.R (l + 1)) (Dp.R l)]
  {Tc : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    LevelTower.Data (θ := θ) Dp.R
      (FormalCuspLevel.cov₀ 𝔪 hJ Dc hinjk hfk hradk φc ψk hψ hfin het hkc) πc}
  {hec : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ l (r : Rc), Tc.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap Rc (Dp.R l) r)}
  (Vc : CuspLevels 𝔪 hJ Dc hinjk hfk hradk φc ψk hψ hfin het hkc Dp.R Tc hec)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)) = Dp.algkR) (hT : HEq Tc Dp.T)
  (hP0 : Vs.P0 = Dp.piece hθ.out hO) (P : TwoChartRings O)
  {X1 : ℕ → Type u} [∀ n, CommRing (X1 n)] [instX10 : ∀ n, Algebra Is.B0 (X1 n)]
  [instX1 : ∀ n, Algebra (Is.B n) (X1 n)]
  {μ1 : ∀ n, X1 (n + 1) →+* X1 n} (e1 : Is.LevelEquivFam hθ.out hO X1 μ1)
  {X0 : ℕ → Type u} [∀ n, CommRing (X0 n)] [instX0 : ∀ n, Algebra Vs.B0' (X0 n)]
  (μ0 : ∀ n, X0 (n + 1) →+* X0 n)
  (ωn : ∀ n, haveI := Vs.hW0; haveI := Vs.hW0'
    letI := awayAlg (W := Vs.W0) (C := X0 n) Vs.x0
    letI := awayAlg (W := Vs.W0) (C := X1 n) Vs.x1
    Localization.Away (algebraMap Vs.B0' (X0 n) Vs.x0) ≃ₐ[Vs.W0]
      Localization.Away (algebraMap Is.B0 (X1 n) Vs.x1))
  (t : ∀ n, X0 n →+* Dp.R n ⊗[Rc] Bc)
  (ht : ∀ n r, t n (algebraMap Vs.B0' (X0 n) r) = algebraMap (Dp.R n) (Dp.R n ⊗[Rc] Bc)
    (algebraMap (Vs.B' n) (Dp.R n) (algebraMap Vs.B0' (Vs.B' n) r)))
  (htloc : ∀ n, letI := (t n).toAlgebra
    IsLocalization.Away (algebraMap Vs.B0' (X0 n) Vs.c0) (Dp.R n ⊗[Rc] Bc))
  (ρX1 : ∀ n, letI := algC1 Is.B Is.qB Is.C1 n; X1 n →ₐ[Is.B n] Is.C1) (ρX0 : ∀ n, X0 n →+* Vs.C0)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ n x, FormalCuspLevel.ρ 𝔪 hJ Dc hinjk hfk hradk φc ψk hψ hfin het hkc Dp.R Tc.hfe hec n
      (t n x) = Dp.ι₀ (ρX0 n x))
  {mJ : ℕ → ℕ} (hJm : ∀ n, J θ (R := Vs.B' n) ^ mJ n = ⊥)
  (hψ1 : ∀ n y, (letI := Vs.algBM n; Ideal.Quotient.mk (EtaleNil.JB (J θ (R := Is.B n)) (Vs.M n))
    (Vs.ψ hθ.out hO n (e1.equiv n y))) = Vs.γM n (ρX1 n y))
  (hx1c : ∀ n, ρX1 n (algebraMap Is.B0 (X1 n) Vs.x1) = algebraMap Is.Bs Is.C1 Vs.x1s)
  (hω : ∀ n (x : X0 n), ∃ (y : X1 n) (k : ℕ),
    (haveI := Vs.hW0; haveI := Vs.hW0'
      letI := awayAlg (W := Vs.W0) (C := X0 n) Vs.x0
      letI := awayAlg (W := Vs.W0) (C := X1 n) Vs.x1
      ωn n (algebraMap (X0 n) _ x) *
        algebraMap (X1 n) (Localization.Away (algebraMap Is.B0 (X1 n) Vs.x1))
          (algebraMap Is.B0 (X1 n) Vs.x1) ^ k = algebraMap (X1 n) _ y) ∧
    Vs.ω (algebraMap Vs.C0 _ (ρX0 n x)) *
        algebraMap Is.C1 (Localization.Away (algebraMap Is.Bs Is.C1 Vs.x1s))
          (algebraMap Is.Bs Is.C1 Vs.x1s) ^ k = algebraMap Is.C1 _ (ρX1 n y))
  (q0 : ∀ n, P.R0 →+* X0 n)
  (hq0O : ∀ n o, q0 n (algebraMap O P.R0 o) = algebraMap Vs.B0' (X0 n) (algebraMap O Vs.B0' o))
  (q1 : ∀ n, P.R1 →+* X1 n)
  (hq1O : ∀ n o, q1 n (algebraMap O P.R1 o) =
    algebraMap Is.B0 (X1 n) (letI := Vs.algOB0; algebraMap O Is.B0 o))
  (hx : ∀ n, q0 n P.x = algebraMap Vs.B0' (X0 n) Vs.x0)
  (hy : ∀ n, q1 n P.y = algebraMap Is.B0 (X1 n) Vs.x1)
  (hW : ∀ n a m (k : ℕ), P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m →
    (haveI := Vs.hW0; haveI := Vs.hW0'
      letI := awayAlg (W := Vs.W0) (C := X0 n) Vs.x0
      letI := awayAlg (W := Vs.W0) (C := X1 n) Vs.x1
      ωn n (algebraMap (X0 n) _ (q0 n a)) *
        algebraMap (X1 n) (Localization.Away (algebraMap Is.B0 (X1 n) Vs.x1))
          (algebraMap Is.B0 (X1 n) Vs.x1) ^ k = algebraMap (X1 n) _ (q1 n m)))
  (hμt : ∀ n x, t n (μ0 n x) = levelMap Dp.R n (t (n + 1) x))
  (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)
  (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
  (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R0))
  (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R1))

-- the cusp level data of the second side
variable {Rc' : Type u} [CommRing Rc'] [Algebra O Rc']
  {Bc' : Type u} [CommRing Bc'] [Algebra Rc' Bc'] [IsNoetherianRing Rc']
  {ι' : Type} [Fintype ι'] [DecidableEq ι'] {𝔪' : ι' → Ideal Rc'} [∀ j, (𝔪' j).IsMaximal]
  {hJ' : ∀ j, J θ (R := Rc') ≤ 𝔪' j} {sc' : Rc'} {Ec' : ι' → ℕ}
  {Dc' : ∀ j, PointCuspFormData (θ := θ) (B := Bc') sc' (Ec' j) (𝔪' j)} {gc' : Rc'}
  {hinjk' : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪' j)}
  {hfk' : ∀ j, fbar θ gc' ∈ sIdeal (θ := θ) (𝔪' j)}
  {hradk' : ⨅ j, sIdeal (θ := θ) (𝔪' j) ≤ (Ideal.span {fbar θ gc'}).radical}
  {φc' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ gc')}
  {ψk' : Polynomial k →ₐ[k] Admissible.Hat (fbar θ gc')}
  {hψ' : ψk' Polynomial.X = algebraMap (Rs θ Rc') _ (Ideal.Quotient.mk _ sc')}
  {hfin' : Module.Finite (Rs θ Rc') (Cs θ Rc' Bc')}
  {het' : (Localization.awayMap (algebraMap (Rs θ Rc') (Cs θ Rc' Bc')) (fbar θ gc')).Etale}
  {hkc' : ∀ j i, ((Dc' j).d i : k) ≠ 0}
  {πc' : (FormalCuspLevel.cov₀ 𝔪' hJ' Dc' hinjk' hfk' hradk' φc' ψk' hψ' hfin' het' hkc').ι → O}
  (Dp' : PatchInput θ Vs'.B' Vs'.qB' Vs'.C0 Vs'.x0 Vs'.c0 Vs'.x0s Vs'.c0s Vs'.ϖ
    (FormalCuspLevel.cov₀ 𝔪' hJ' Dc' hinjk' hfk' hradk' φc' ψk' hψ' hfin' het' hkc') πc')
  [algRI' : ∀ l, Algebra Rc' (Dp'.R l)] [towerORI' : ∀ l, IsScalarTower O Rc' (Dp'.R l)]
  [towerRII' : ∀ l, IsScalarTower Rc' (Dp'.R (l + 1)) (Dp'.R l)]
  {Tc' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp'.R l)
    LevelTower.Data (θ := θ) Dp'.R
      (FormalCuspLevel.cov₀ 𝔪' hJ' Dc' hinjk' hfk' hradk' φc' ψk' hψ' hfin' het' hkc') πc'}
  {hec' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp'.R l)
    ∀ l (r : Rc'), Tc'.e l (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap Rc' (Dp'.R l) r)}
  (Vc' : CuspLevels 𝔪' hJ' Dc' hinjk' hfk' hradk' φc' ψk' hψ' hfin' het' hkc' Dp'.R Tc' hec')
  (hkI' : (fun l ↦ QuadNodeTower.algK (θ := θ) (Dp'.R l)) = Dp'.algkR) (hT' : HEq Tc' Dp'.T)
  (hP0' : Vs'.P0 = Dp'.piece hθ.out hO) (P' : TwoChartRings O)
  {X1' : ℕ → Type u} [∀ n, CommRing (X1' n)] [instX10' : ∀ n, Algebra Is'.B0 (X1' n)]
  [instX1' : ∀ n, Algebra (Is'.B n) (X1' n)]
  {μ1' : ∀ n, X1' (n + 1) →+* X1' n} (e1' : Is'.LevelEquivFam hθ.out hO X1' μ1')
  {X0' : ℕ → Type u} [∀ n, CommRing (X0' n)] [instX0' : ∀ n, Algebra Vs'.B0' (X0' n)]
  (μ0' : ∀ n, X0' (n + 1) →+* X0' n)
  (ωn' : ∀ n, haveI := Vs'.hW0; haveI := Vs'.hW0'
    letI := awayAlg (W := Vs'.W0) (C := X0' n) Vs'.x0
    letI := awayAlg (W := Vs'.W0) (C := X1' n) Vs'.x1
    Localization.Away (algebraMap Vs'.B0' (X0' n) Vs'.x0) ≃ₐ[Vs'.W0]
      Localization.Away (algebraMap Is'.B0 (X1' n) Vs'.x1))
  (t' : ∀ n, X0' n →+* Dp'.R n ⊗[Rc'] Bc')
  (ht' : ∀ n r, t' n (algebraMap Vs'.B0' (X0' n) r) = algebraMap (Dp'.R n) (Dp'.R n ⊗[Rc'] Bc')
    (algebraMap (Vs'.B' n) (Dp'.R n) (algebraMap Vs'.B0' (Vs'.B' n) r)))
  (htloc' : ∀ n, letI := (t' n).toAlgebra
    IsLocalization.Away (algebraMap Vs'.B0' (X0' n) Vs'.c0) (Dp'.R n ⊗[Rc'] Bc'))
  (ρX1' : ∀ n, letI := algC1 Is'.B Is'.qB Is'.C1 n; X1' n →ₐ[Is'.B n] Is'.C1)
  (ρX0' : ∀ n, X0' n →+* Vs'.C0)
  (hρ' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp'.R l)
    ∀ n x, FormalCuspLevel.ρ 𝔪' hJ' Dc' hinjk' hfk' hradk' φc' ψk' hψ' hfin' het' hkc' Dp'.R
      Tc'.hfe hec' n (t' n x) = Dp'.ι₀ (ρX0' n x))
  {mJ' : ℕ → ℕ} (hJm' : ∀ n, J θ (R := Vs'.B' n) ^ mJ' n = ⊥)
  (hψ1' : ∀ n y, (letI := Vs'.algBM n
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := Is'.B n)) (Vs'.M n))
    (Vs'.ψ hθ.out hO n (e1'.equiv n y))) = Vs'.γM n (ρX1' n y))
  (hx1c' : ∀ n, ρX1' n (algebraMap Is'.B0 (X1' n) Vs'.x1) = algebraMap Is'.Bs Is'.C1 Vs'.x1s)
  (hω' : ∀ n (x : X0' n), ∃ (y : X1' n) (k : ℕ),
    (haveI := Vs'.hW0; haveI := Vs'.hW0'
      letI := awayAlg (W := Vs'.W0) (C := X0' n) Vs'.x0
      letI := awayAlg (W := Vs'.W0) (C := X1' n) Vs'.x1
      ωn' n (algebraMap (X0' n) _ x) *
        algebraMap (X1' n) (Localization.Away (algebraMap Is'.B0 (X1' n) Vs'.x1))
          (algebraMap Is'.B0 (X1' n) Vs'.x1) ^ k = algebraMap (X1' n) _ y) ∧
    Vs'.ω (algebraMap Vs'.C0 _ (ρX0' n x)) *
        algebraMap Is'.C1 (Localization.Away (algebraMap Is'.Bs Is'.C1 Vs'.x1s))
          (algebraMap Is'.Bs Is'.C1 Vs'.x1s) ^ k = algebraMap Is'.C1 _ (ρX1' n y))
  (q0' : ∀ n, P'.R0 →+* X0' n)
  (hq0O' : ∀ n o, q0' n (algebraMap O P'.R0 o) =
    algebraMap Vs'.B0' (X0' n) (algebraMap O Vs'.B0' o))
  (q1' : ∀ n, P'.R1 →+* X1' n)
  (hq1O' : ∀ n o, q1' n (algebraMap O P'.R1 o) =
    algebraMap Is'.B0 (X1' n) (letI := Vs'.algOB0; algebraMap O Is'.B0 o))
  (hx' : ∀ n, q0' n P'.x = algebraMap Vs'.B0' (X0' n) Vs'.x0)
  (hy' : ∀ n, q1' n P'.y = algebraMap Is'.B0 (X1' n) Vs'.x1)
  (hW' : ∀ n a m (k : ℕ), P'.ρ0 a * P'.ρ1 P'.y ^ k = P'.ρ1 m →
    (haveI := Vs'.hW0; haveI := Vs'.hW0'
      letI := awayAlg (W := Vs'.W0) (C := X0' n) Vs'.x0
      letI := awayAlg (W := Vs'.W0) (C := X1' n) Vs'.x1
      ωn' n (algebraMap (X0' n) _ (q0' n a)) *
        algebraMap (X1' n) (Localization.Away (algebraMap Is'.B0 (X1' n) Vs'.x1))
          (algebraMap Is'.B0 (X1' n) Vs'.x1) ^ k = algebraMap (X1' n) _ (q1' n m)))
  (hμt' : ∀ n x, t' n (μ0' n x) = levelMap Dp'.R n (t' (n + 1) x))
  (hμ0' : ∀ n r, μ0' n (q0' (n + 1) r) = q0' n r)
  (hμ1' : ∀ n r, μ1' n (q1' (n + 1) r) = q1' n r)
  (hs0' : ∀ n, Function.Surjective (q0' n)) (hs1' : ∀ n, Function.Surjective (q1' n))
  (hk0' : ∀ n, RingHom.ker (q0' n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P'.R0))
  (hk1' : ∀ n, RingHom.ker (q1' n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P'.R1))

set_option hygiene false in
/-- `systemMapH` with the variables of this section. -/
local notation "𝔰" => systemMapH V V' hθ.out hO hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal e he
  β hβJ hβa heβ hβR φ1 hφc ℓb hℓb hσE heS β0 hβ0 hx1 hg0 hβ0O p hp0 hpO hpS hpB hJ0 hJ0' hpγ ϖ h h'

include hR hc ha hk hs hF hE hcd hcd' hcu hcv hbal he hβJ hβa heβ hβR hφc hℓb hσE heS hβ0 hx1 hg0
  hβ0O hp0 hpO hpS hpB hJ0 hJ0' hpγ h h' Vc hkI hT hP0 e1 μ0 ωn t ht htloc hρ hJm hψ1 hx1c hω hq0O
  hq1O hx hy hW hμt hμ0 hμ1 hs0 hs1 hk0 hk1 Vc' hkI' hT' hP0' e1' μ0' ωn' t' ht' htloc' hρ' hJm'
  hψ1' hx1c' hω' hq0O' hq1O' hx' hy' hW' hμt' hμ0' hμ1' hs0' hs1' hk0' hk1' in
/-- **Lifting a morphism of special-fibre data to two-chart rings with cusp level data**: the
morphism `systemMapH` of the adic systems of `V`, `V'` induces `Φ : P → P'` (a morphism of chart
algebras) which is `β0` on the bases and reduces to `φ1` on the second and to `φ0` on the first
chart. The cusp level data are given over overlaps `Vs`, `Vs'` which are `HEq` to `V`, `V'` (the
same overlaps, possibly spelled differently: concrete instances pass `rfl`/`HEq.rfl`, so no
statement relating the two spellings has to be elaborated). The statement mentions only `P`,
`P'` and their level-`0` reductions (`algOfCuspLevelsW_spec` for both sides and `mapH_spec`). -/
theorem exists_hom_of_cuspLevelsW [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    [Module.Finite O[X] (Module.AEval' P'.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P'.chartModule.x1)]
    (hR₀ : R₀s = R₀) (hcR : HEq cR₀s cR₀) (haR : HEq aR₀s aR₀) (hf₀ : HEq f₀s f₀)
    (hφ₀ : HEq φ₀s φ₀) (hφ₀' : HEq φ₀s' φ₀') (hψ₀ : HEq ψ₀s ψ₀) (hcov : HEq cov₀s cov₀)
    (hcov' : HEq cov₀s' cov₀') (hπ : HEq πLs πL) (hπ' : HEq πLs' πL') (hIs : HEq Is I)
    (hIs' : HEq Is' I') (hVs : HEq Vs V) (hVs' : HEq Vs' V')
    (hϖs : Vs.ϖ = ϖ) (hϖs' : Vs'.ϖ = ϖ)
    (hJ0s : J θ (R := Is.B 0) = ⊥) (hJ0s' : J θ (R := Is'.B 0) = ⊥)
    (hK : ∀ b : P.R1, (∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P.R1)) → b = 0)
    (hK' : ∀ b : P'.R1, (∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O P'.R1)) → b = 0)
    (hJ0D : J θ (R := Dp.R 0) = ⊥) (bot : Vs.P0.Bottom 0)
    (hbot : HEq bot (Dp.bottom hθ.out hO hJ0D))
    (hJ0D' : J θ (R := Dp'.R 0) = ⊥) (bot' : Vs'.P0.Bottom 0)
    (hbot' : HEq bot' (Dp'.bottom hθ.out hO hJ0D'))
    (he1 : letI := algC1 Is.B Is.qB Is.C1 0
      ∀ y, e1.equiv 0 y = Is.yEquiv hθ.out hO hJ0s (ρX1 0 y))
    (he1' : letI := algC1 Is'.B Is'.qB Is'.C1 0
      ∀ y, e1'.equiv 0 y = Is'.yEquiv hθ.out hO hJ0s' (ρX1' 0 y))
    (ψ1 : Is.B0 → P.R1) (hψq : ∀ n r, q1 n (ψ1 r) = algebraMap Is.B0 (X1 n) r)
    (ψ1' : Is'.B0 → P'.R1) (hψq' : ∀ n r, q1' n (ψ1' r) = algebraMap Is'.B0 (X1' n) r)
    (β0s : Is.B0 →+* Is'.B0) (hβ0s : HEq β0s β0)
    (φ1s : Is.C1 →+* Is'.C1) (hφ1s : HEq φ1s φ1)
    (φ0 : V.C0 →+* V'.C0) (φ0s : Vs.C0 →+* Vs'.C0) (hφ0s : HEq φ0s φ0)
    (bot₂ : V.P0.Bottom 0) (hbot₂ : HEq bot bot₂) (bot₂' : V'.P0.Bottom 0) (hbot₂' : HEq bot' bot₂')
    (hpb : ∀ c, p 0 (bot₂.toP c) = bot₂'.toP (φ0 c))
    (Lx0 : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) →+*
      Localization.Away (algebraMap V'.Bs' V'.C0 V'.x0s))
    (hLx0 : ∀ c, Lx0 (algebraMap V.C0 _ c) = algebraMap V'.C0 _ (φ0 c))
    (Lx1 : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 V'.x1s))
    (hLx1 : ∀ c, Lx1 (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hωL : ∀ z, V'.ω (Lx0 z) = Lx1 (V.ω z)) :
    ∃ Φ : ChartModule.Hom P.chartModule P'.chartModule,
      P.algStr.IsHom P'.algStr Φ ∧ (∀ r, Φ.f1 (ψ1 r) = ψ1' (β0s r)) ∧
      (∀ u, ρX1' 0 (q1' 0 (Φ.f1 u)) = φ1s (ρX1 0 (q1 0 u))) ∧
      (∀ b, ρX0' 0 (q0' 0 (Φ.f0 b)) = φ0s (ρX0 0 (q0 0 b))) := by
  subst hR₀
  obtain rfl := eq_of_heq hcR
  obtain rfl := eq_of_heq haR
  obtain rfl := eq_of_heq hf₀
  obtain rfl := eq_of_heq hφ₀
  obtain rfl := eq_of_heq hφ₀'
  obtain rfl := eq_of_heq hψ₀
  obtain rfl := eq_of_heq hcov
  obtain rfl := eq_of_heq hcov'
  obtain rfl := eq_of_heq hπ
  obtain rfl := eq_of_heq hπ'
  obtain rfl := eq_of_heq hIs
  obtain rfl := eq_of_heq hIs'
  obtain rfl := eq_of_heq hVs
  obtain rfl := eq_of_heq hVs'
  obtain rfl := eq_of_heq hβ0s
  obtain rfl := eq_of_heq hφ1s
  obtain rfl := eq_of_heq hφ0s
  obtain rfl := eq_of_heq hbot₂
  obtain rfl := eq_of_heq hbot₂'
  have s := Vs.algOfCuspLevelsW_spec hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1
    hx1c hω q0 hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ hϖs hs0 hs1 hk0 hk1 hK hJ0s hJ0D bot hbot he1 ψ1
    hψq
  have s' := Vs'.algOfCuspLevelsW_spec hO Dp' Vc' hkI' hT' hP0' P' e1' μ0' ωn' t' ht' htloc' ρX1'
    ρX0' hρ' hJm' hψ1' hx1c' hω' q0' hq0O' q1' hq1O' hx' hy' hW' hμt' hμ0' hμ1' ϖ hϖs' hs0' hs1'
    hk0' hk1' hK' hJ0s' hJ0D' bot' hbot' he1' ψ1' hψq'
  have r := mapH_spec Vs Vs' hθ.out hO hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa
    heβ hβR φ1s hφc ℓb hℓb hσE heS β0s hβ0 hx1 hg0 hβ0O p hp0 hpO hpS hpB hJ0 hJ0' hpγ ϖ h h'
    (Vs.algOfCuspLevelsW hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1c hω q0
      hq0O q1 hq1O hx hy hW hμt hμ0 hμ1 ϖ hϖs hs0 hs1 hk0 hk1)
    (Vs'.algOfCuspLevelsW hO Dp' Vc' hkI' hT' hP0' P' e1' μ0' ωn' t' ht' htloc' ρX1' ρX0' hρ'
      hJm' hψ1' hx1c' hω' q0' hq0O' q1' hq1O' hx' hy' hW' hμt' hμ0' hμ1' ϖ hϖs' hs0' hs1' hk0' hk1')
    s'.1 ψ1 ψ1' s.2.1 s'.2.1 (fun u ↦ ρX1 0 (q1 0 u)) s.2.2.1 (fun u ↦ ρX1' 0 (q1' 0 u))
    s'.2.2.1 bot bot' φ0s hpb Lx0 hLx0 Lx1 hLx1 hωL (fun b ↦ ρX0 0 (q0 0 b)) s.2.2.2
    (fun b ↦ ρX0' 0 (q0' 0 b)) s'.2.2.2
  exact ⟨_, r.1, r.2.1, r.2.2.1, r.2.2.2⟩

end

end Overlap

end NodeEtaleGlue

end SemistableReduction
