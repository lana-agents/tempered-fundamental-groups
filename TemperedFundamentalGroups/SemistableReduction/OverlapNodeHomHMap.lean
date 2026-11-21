/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.OverlapNodeHomH
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormHom

/-!
# The morphisms of algebraizations induced by `systemMapH` (generic; MR12 I3)

For the morphism `NodeEtaleGlue.Overlap.systemMapH` of the adic systems of two overlaps of
node-only coverings (`OverlapNodeHomH`) and algebraizations `A`, `A'` of the two systems, the
induced morphism `Φ = Algebraization.map (systemMapH …) A A'` of chart algebras:

* **`NodeEtaleGlue.Overlap.mapH_f1_base`**: is `β0` on the second chart over the base `B0`, if
  the second chart of `A'` is separated for its reductions (e.g. `algOfLevels_sep1`);
* **`NodeEtaleGlue.Overlap.mapH_f1_one`**: reduces to `φ1 : C1 → C1'` on the second chart
  (under reductions `A.α 1` given by `yEquiv : C1 ≃ Y 0`);
* **`NodeEtaleGlue.Overlap.mapH_f0_one`**: reduces to `φ0 : C0 → C0'` on the first chart (under
  reductions `A.α 1` given by `r0Equiv' : C0 ≃ R0 0`; `r0Equiv'_symm_map`);
* **`NodeEtaleGlue.Overlap.mapH_spec`**: all of these at once (for a single instantiation at
  concrete overlaps).

These are the generic steps of I3 surjectivity: applied to the normalisations `P_L`, `P_L'` of
two covers (`algOfLevels`), `Φ` is a morphism of the normalisations reducing to the given
morphism of special-fibre data.
-/

universe u

namespace SemistableReduction

open AdmissibleLift LevelTower ProjectiveLine

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
variable {I : Input θ cov₀ πL} {I' : Input θ cov₀' πL'} (V : Overlap I) (V' : Overlap I')
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hR : I'.R = I.R) (hc : HEq I'.commRingR I.commRingR) (ha : HEq I'.algOR I.algOR)
  (hk : HEq I'.algkR I.algkR) (hs : HEq I'.algSuccR I.algSuccR) (hF : HEq I'.T.f I.T.f)
  (hE : HEq I'.T.e I.T.e)
  [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ] (φ : cov₀.C →ₐ[R₀] cov₀'.C)
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
  (A : AdicChartAlgSystem.Algebraization (V.systemAt hθ hO ϖ h))
  (A' : AdicChartAlgSystem.Algebraization (V'.systemAt hθ hO ϖ h'))

set_option hygiene false in
/-- `systemMapH` with the variables of this section. -/
local notation "𝔰" => systemMapH V V' hθ hO hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal e he β
  hβJ hβa heβ hβR φ1 hφc ℓb hℓb hσE heS β0 hβ0 hx1 hg0 hβ0O p hp0 hpO hpS hpB hJ0 hJ0' hpγ ϖ h h'

/-- **The morphism induced by `systemMapH` is `β0` over the base on the second chart.** -/
theorem mapH_f1_base (hsep : ∀ x : A'.N.M1, (∀ n, (A'.α (n + 1)).f1 x = 0) → x = 0) (r : I.B0)
    (u : A.N.M1) (u' : A'.N.M1)
    (hu : ∀ n, ((A.α (n + 1)).f1 u : I.Y hθ n) = algebraMap I.B0 (I.Y hθ n) r)
    (hu' : ∀ n, ((A'.α (n + 1)).f1 u' : I'.Y hθ n) = algebraMap I'.B0 (I'.Y hθ n) (β0 r)) :
    (AdicChartAlgSystem.Algebraization.map 𝔰 A A').f1 u = u' :=
  AdicChartAlgSystem.Algebraization.map_f1_eq _ A A' hsep u u' fun n ↦
    (congrArg (I.yH I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE n) (hu n)).trans
      ((Input.yH_algebraMap I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ
        hβR φ1 hφc ℓb hℓb hσE β0 hβ0 n r).trans (hu' n).symm)

/-- **The morphism induced by `systemMapH` reduces to `φ1` on the second chart**, for
reductions `A.α 1`, `A'.α 1` given by `ρ1`, `ρ1'` under `yEquiv : C1 ≃ Y 0`. -/
theorem mapH_f1_one (ρ1 : A.N.M1 → I.C1)
    (hA : ∀ u, ((A.α 1).f1 u : I.Y hθ 0) = I.yEquiv hθ hO hJ0 (ρ1 u))
    (ρ1' : A'.N.M1 → I'.C1)
    (hA' : ∀ u, ((A'.α 1).f1 u : I'.Y hθ 0) = I'.yEquiv hθ hO hJ0' (ρ1' u)) (u : A.N.M1) :
    ρ1' ((AdicChartAlgSystem.Algebraization.map 𝔰 A A').f1 u) = φ1 (ρ1 u) := by
  letI := I'.algC10 0
  refine (I'.yEquiv hθ hO hJ0').injective ?_
  rw [← hA']
  refine (LinearMap.congr_fun (congrArg ChartModule.Hom.f1
    (AdicChartAlgSystem.Algebraization.comp_map _ A A' 1)) u).trans ?_
  exact (congrArg (I.yH I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR
      φ1 hφc ℓb hℓb hσE 0) (hA u)).trans
    (Input.yH_yEquiv I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE hO 0 hJ0 hJ0' (ρ1 u))

/-- **The morphism induced by `systemMapH` reduces to `φ0` on the first chart**, for
reductions `A.α 1`, `A'.α 1` given by `ρ0`, `ρ0'` under `r0Equiv' : C0 ≃ R0 0`, `φ0`
compatible with the bottom identifications `bot`, `bot'` and with the overlap identifications. -/
theorem mapH_f0_one (bot : V.P0.Bottom 0) (bot' : V'.P0.Bottom 0) (φ0 : V.C0 →+* V'.C0)
    (hpb : ∀ c, p 0 (bot.toP c) = bot'.toP (φ0 c))
    (Lx0 : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) →+*
      Localization.Away (algebraMap V'.Bs' V'.C0 V'.x0s))
    (hLx0 : ∀ c, Lx0 (algebraMap V.C0 _ c) = algebraMap V'.C0 _ (φ0 c))
    (Lx1 : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 V'.x1s))
    (hLx1 : ∀ c, Lx1 (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hω : ∀ z, V'.ω (Lx0 z) = Lx1 (V.ω z))
    (ρ0 : A.N.M0 → V.C0) (hA : ∀ b, (V.r0Equiv' hθ hO hJ0 bot).symm ((A.α 1).f0 b) = ρ0 b)
    (ρ0' : A'.N.M0 → V'.C0)
    (hA' : ∀ b, (V'.r0Equiv' hθ hO hJ0' bot').symm ((A'.α 1).f0 b) = ρ0' b) (b : A.N.M0) :
    ρ0' ((AdicChartAlgSystem.Algebraization.map 𝔰 A A').f0 b) = φ0 (ρ0 b) := by
  rw [← hA', ← hA]
  exact V.r0Equiv'_symm_map V' hθ hO ϖ h h'
    (I.yH I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1 hφc ℓb hℓb
      hσE)
    (fun n ↦ (Input.yH_algebraMap I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ
      hβa heβ hβR φ1 hφc ℓb hℓb hσE β0 hβ0 n V.x1).trans (by rw [hx1]))
    (fun n o ↦ yH_algebraMapO V V' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa
      heβ hβR φ1 hφc ℓb hℓb hσE β0 hβ0 hβ0O n o)
    p hp0 hpO
    (fun n z ↦ hψH V V' hθ hO hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR
      φ1 hφc ℓb hℓb hσE heS β0 hβ0 hg0 p hp0 hpS hpB hJ0 hJ0' hpγ n z)
    (Input.yH_succ I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE hO hs heS)
    hpS A A' hJ0 hJ0' bot bot' φ0 hpb Lx0 hLx0 φ1 Lx1 hLx1 hω
    (Input.yH_yEquiv I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE hO 0 hJ0 hJ0') b

/-- **The morphism induced by `systemMapH`, all properties used for I3 surjectivity**: it is a
morphism of chart algebras, `β0` over the base on the second chart (`mapH_f1_base`, for maps
`ψ1`, `ψ1'` of the base into the second charts reducing to the structure maps), and it reduces to
`φ1` and `φ0` (`mapH_f1_one`, `mapH_f0_one`). -/
theorem mapH_spec (hsep : ∀ x : A'.N.M1, (∀ n, (A'.α (n + 1)).f1 x = 0) → x = 0)
    (ψ1 : I.B0 → A.N.M1) (ψ1' : I'.B0 → A'.N.M1)
    (hψ1 : ∀ n r, ((A.α (n + 1)).f1 (ψ1 r) : I.Y hθ n) = algebraMap I.B0 (I.Y hθ n) r)
    (hψ1' : ∀ n r, ((A'.α (n + 1)).f1 (ψ1' r) : I'.Y hθ n) = algebraMap I'.B0 (I'.Y hθ n) r)
    (ρ1 : A.N.M1 → I.C1)
    (hA1 : ∀ u, ((A.α 1).f1 u : I.Y hθ 0) = I.yEquiv hθ hO hJ0 (ρ1 u))
    (ρ1' : A'.N.M1 → I'.C1)
    (hA1' : ∀ u, ((A'.α 1).f1 u : I'.Y hθ 0) = I'.yEquiv hθ hO hJ0' (ρ1' u))
    (bot : V.P0.Bottom 0) (bot' : V'.P0.Bottom 0) (φ0 : V.C0 →+* V'.C0)
    (hpb : ∀ c, p 0 (bot.toP c) = bot'.toP (φ0 c))
    (Lx0 : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) →+*
      Localization.Away (algebraMap V'.Bs' V'.C0 V'.x0s))
    (hLx0 : ∀ c, Lx0 (algebraMap V.C0 _ c) = algebraMap V'.C0 _ (φ0 c))
    (Lx1 : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 V'.x1s))
    (hLx1 : ∀ c, Lx1 (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hω : ∀ z, V'.ω (Lx0 z) = Lx1 (V.ω z))
    (ρ0 : A.N.M0 → V.C0) (hA0 : ∀ b, (V.r0Equiv' hθ hO hJ0 bot).symm ((A.α 1).f0 b) = ρ0 b)
    (ρ0' : A'.N.M0 → V'.C0)
    (hA0' : ∀ b, (V'.r0Equiv' hθ hO hJ0' bot').symm ((A'.α 1).f0 b) = ρ0' b) :
    A.B.IsHom A'.B (AdicChartAlgSystem.Algebraization.map 𝔰 A A') ∧
      (∀ r, (AdicChartAlgSystem.Algebraization.map 𝔰 A A').f1 (ψ1 r) = ψ1' (β0 r)) ∧
      (∀ u, ρ1' ((AdicChartAlgSystem.Algebraization.map 𝔰 A A').f1 u) = φ1 (ρ1 u)) ∧
      (∀ b, ρ0' ((AdicChartAlgSystem.Algebraization.map 𝔰 A A').f0 b) = φ0 (ρ0 b)) :=
  ⟨AdicChartAlgSystem.Algebraization.isHom_map _ A A',
    fun r ↦ mapH_f1_base V V' hθ hO hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa
      heβ hβR φ1 hφc ℓb hℓb hσE heS β0 hβ0 hx1 hg0 hβ0O p hp0 hpO hpS hpB hJ0 hJ0' hpγ ϖ h h' A A'
      hsep r (ψ1 r) (ψ1' (β0 r)) (fun n ↦ hψ1 n r) (fun n ↦ hψ1' n (β0 r)),
    mapH_f1_one V V' hθ hO hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE heS β0 hβ0 hx1 hg0 hβ0O p hp0 hpO hpS hpB hJ0 hJ0' hpγ ϖ h h' A A' ρ1 hA1 ρ1'
      hA1',
    mapH_f0_one V V' hθ hO hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE heS β0 hβ0 hx1 hg0 hβ0O p hp0 hpO hpS hpB hJ0 hJ0' hpγ ϖ h h' A A' bot bot' φ0
      hpb Lx0 hLx0 Lx1 hLx1 hω ρ0 hA0 ρ0' hA0'⟩

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
