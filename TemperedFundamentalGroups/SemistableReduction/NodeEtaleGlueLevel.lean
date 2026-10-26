/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueInput
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoLoc

/-!
# An algebra with the node patch and the étale piece as localizations is the glued covering
(MR12 T2 S6, step G4)

Setting: an input `I : NodeEtaleGlue.Input` (node patches `G n` over `D(a)`, étale pieces `E n`
over `D(b)` of the base chart `B n`, glued along `E n[1/a]` to `Y n`). Let `X` be a `B n`-algebra
with `B n`-algebra maps `φG : X → G n`, `φE : X → E n` and a reduction `ρX : X → C1` to the
special-fibre covering, compatible with the identifications of the special fibres
(`σPn` on the étale part of `G n`, `σE` on `E n`). Then:

* **`NodeEtaleGlue.Input.ρa_φG`**: `ρa (φG x) = φE x` in `E n[1/a]` (if `φE` is a localization
  away from `b`): both maps `E n → E n[1/a]` lift the same map modulo the nilpotent ideal `J`
  (`EtaleNil.ext`), computed through `OverlapFibre.χ`;
* **`NodeEtaleGlue.Input.levelEquiv`**: if moreover `φG`, `φE` are localizations away from
  `a`, `b`, then `X ≃ₐ[B0] Y n` (`ZariskiTwo.liftEquiv`), with components `φG`, `φE`.

For the Tate covering over `V₁` (`TateGlue1.input`), `X` is the level `B₁/ϖⁿ⁺¹` of the
normalisation, `φG` the node level patch (`TateTwoChartNode.levelPatchEquiv_NR`) and `φE` the
étale level (`EtaleTower.levelEquiv`).
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} (I : Input θ cov₀ πL)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)
  {X : Type u} [CommRing X] [Algebra (I.B n) X]
  (φG : letI := algBG I.T hθ I.B n; X →ₐ[I.B n] I.T.G hθ n) (φE : X →ₐ[I.B n] I.E n)
  (ρX : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n; X →ₐ[I.B n] I.C1)
  (hG : ∀ x, (letI := algBP I.T I.B n; σPn I.T I.B n (Ideal.Quotient.mk _ (fstP I.T hθ n (φG x)))) =
    algebraMap (Cc I.T n) _ (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n (ρX x)))
  (hE : ∀ x, I.σE n (Ideal.Quotient.mk _ (φE x)) =
    algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX x))
  (hlocE : letI := φE.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) X (I.b n)) (I.E n))

include hG hE hlocE in
/-- **The node patch and the étale piece of `X` agree on the overlap**: `ρa (φG x) = φE x` in
`E n[1/a]`. -/
theorem ρa_φG (x : X) :
    ρa I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv I.hJB n
        (φG x) = algebraMap (I.E n) (EtaleOverlap.Bab (I.a n) (I.E n)) (φE x) := by
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBC I.T I.B n
  haveI := towerBC I.T I.B n
  letI := algBG I.T hθ I.B n
  haveI := towerBG I.T hθ I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  letI := φE.toRingHom.toAlgebra
  haveI := hlocE
  have hu : IsUnit (((ρa I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB n).comp φG) (algebraMap (I.B n) X (I.b n))) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (I.B n) (I.E n)
      (EtaleOverlap.Bab (I.a n) (I.E n))]
    exact (I.hbE n).map _
  let h₀ : I.E n →+* EtaleOverlap.Bab (I.a n) (I.E n) :=
    IsLocalization.Away.lift (algebraMap (I.B n) X (I.b n)) hu
  have hh₀ : ∀ y, h₀ (φE y) = (ρa I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E
      I.σE I.hbE I.hdiv I.hJB n) (φG y) := IsLocalization.Away.lift_eq _ hu
  let h : I.E n →ₐ[I.B n] EtaleOverlap.Bab (I.a n) (I.E n) :=
    { h₀ with
      commutes' := fun r ↦ by
        have h1 := hh₀ (algebraMap (I.B n) X r)
        simp only [AlgHom.commutes] at h1
        exact h1 }
  have key : h = IsScalarTower.toAlgHom (I.B n) (I.E n) (EtaleOverlap.Bab (I.a n) (I.E n)) := by
    refine EtaleNil.ext (J θ (R := I.B n)) (I.hJB n) fun e ↦ ?_
    -- both sides are ring maps `E n → Bab/J`, determined on the image of `X`
    have hext : (Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n))
        (EtaleOverlap.Bab (I.a n) (I.E n)))).comp h₀ =
        (Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n))
          (EtaleOverlap.Bab (I.a n) (I.E n)))).comp
          (algebraMap (I.E n) (EtaleOverlap.Bab (I.a n) (I.E n))) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap (I.B n) X (I.b n)))
        (RingHom.ext fun y ↦ ?_)
      simp only [RingHom.comp_apply]
      change Ideal.Quotient.mk _ (h₀ (φE y)) =
        Ideal.Quotient.mk _ (algebraMap (I.E n) (EtaleOverlap.Bab (I.a n) (I.E n)) (φE y))
      rw [hh₀]
      change Ideal.Quotient.mk _ (EtaleOverlap.κ (J θ (R := I.B n)) (I.hJB n) (I.a n) (I.R n)
        (χn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv n)
          (fstP I.T hθ n (φG y))) = _
      rw [← EtaleNil.red_mk, EtaleOverlap.red_κ]
      change OverlapFibre.μ (J θ (R := I.B n)) (I.a n) (I.b n)
        (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n) (I.T.f n) (I.σE n)
        (isLocalization_ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.ha I.hι n) (I.hbE n) (I.hdiv n)
        (σPn I.T I.B n (Ideal.Quotient.mk _ (fstP I.T hθ n (φG y)))) = _
      rw [hG, OverlapFibre.μ_algebraMap, OverlapFibre.γc_ι]
      change EtaleNil.red _ _ ((I.σE n).symm (algebraMap I.C1 _ (ρX y))) = _
      rw [← hE, AlgEquiv.symm_apply_apply, EtaleNil.red_mk]
      rfl
    exact RingHom.congr_fun hext e
  have h2 := hh₀ x
  change h (φE x) = _ at h2
  rw [key] at h2
  exact h2.symm

variable [Algebra I.B0 X] [IsScalarTower I.B0 (I.B n) X]

/-- `φG` over the base `B0`. -/
def φG0 : letI := alg0G I.T hθ I.B I.B0 n; X →ₐ[I.B0] I.T.G hθ n :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := algBG I.T hθ I.B n
  haveI : IsScalarTower I.B0 (I.B n) (I.T.G hθ n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  φG.restrictScalars I.B0

/-- `φE` over the base `B0`. -/
def φE0 : letI := alg0 I.B I.B0 n (I.E n); X →ₐ[I.B0] I.E n :=
  letI := alg0 I.B I.B0 n (I.E n)
  haveI : IsScalarTower I.B0 (I.B n) (I.E n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  φE.restrictScalars I.B0

variable (hlocG : letI := algBG I.T hθ I.B n; letI := φG.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) X (I.a n)) (I.T.G hθ n))

include ρX hG hE hlocE hlocG hO in
/-- **G4: an algebra with the node patch and the étale piece as localizations is the glued
covering** `Y n = G n ×_{E n[1/a]} E n`: `X ≃ₐ[B0] Y n` with components `φG`, `φE`
(`ZariskiTwo.liftEquiv`). -/
def levelEquiv : X ≃ₐ[I.B0] I.Y hθ n := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  haveI := locFst I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
    I.hdiv I.hJB I.B0 (fun _ ↦ rfl) n
  haveI := locSnd I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
    I.hdiv I.hbb I.hJB I.B0 (fun _ ↦ rfl) n
  haveI : IsLocalizedModule (Submonoid.powers I.a0) (I.φG0 hθ n φG).toLinearMap := by
    refine ZariskiTwo.isLocalizedModule_of_away I.a0 (I.φG0 hθ n φG) ?_
    rw [IsScalarTower.algebraMap_apply I.B0 (I.B n) X]
    exact hlocG
  haveI : IsLocalizedModule (Submonoid.powers I.b0) (I.φE0 n φE).toLinearMap := by
    refine ZariskiTwo.isLocalizedModule_of_away I.b0 (I.φE0 n φE) ?_
    rw [IsScalarTower.algebraMap_apply I.B0 (I.B n) X]
    exact hlocE
  exact ZariskiTwo.liftEquiv I.a0 I.b0 I.hab (I.φG0 hθ n φG) (I.φE0 n φE)
    (fun x ↦ I.ρa_φG hθ n φG φE ρX hG hE hlocE x)

lemma levelEquiv_fst (x : X) :
    (I.levelEquiv hθ hO n φG φE ρX hG hE hlocE hlocG x).1.1 = φG x := rfl

lemma levelEquiv_snd (x : X) :
    (I.levelEquiv hθ hO n φG φE ρX hG hE hlocE hlocG x).1.2 = φE x := rfl

end Input

end NodeEtaleGlue

end

end SemistableReduction
