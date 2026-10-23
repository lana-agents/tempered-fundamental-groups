/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueInput
import TemperedFundamentalGroups.SemistableReduction.PatchSpecialFibre
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoLoc

/-!
# The bottom level of the glued coverings is the given covering (Blueprint §12.8, M2.5 (b))

In the setting of `NodeEtaleGlue.Input` (node patches `G n` on the node charts `R n = B n[1/a]`,
étale pieces `E n` over `D(b)`, glued to `Y n = G n ×_{E n[1/a]} E n` over the base charts `B n`),
at a level `n` where `J = 0` on `B n` (the bottom level `n = 0` of a tower `B n = B/ϖⁿ⁺¹` with
`ker θ = (ϖ)`), the glued covering is the given special-fibre covering `C1`:

* **`LevelTower.Level.cEquiv`**: the node patch is the covering `cov₀` of the node chart
  (`FormalPatchLevel.patchEquivOfEqBot`);
* **`NodeEtaleGlue.Input.yEquiv`**: `C1 ≃ₐ[B0] Y n`, with components `C1 → cov₀.C ≃ G n` and
  `C1 → C1[1/b̄] ≃ E n` (uniqueness of the Zariski glueing, `ZariskiTwo.liftEquiv`; the two maps
  agree on the overlap `E n[1/a]` because both reduce to `γ1 = redE ∘ σE⁻¹`, and reduction is
  injective for `J = 0`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **At a level with `J = 0` the node patch is the given covering** of the node chart. -/
def Level.cEquiv {n : ℕ} (D : Level R cov₀ πL hfe n) (hJ0 : J θ (R := R n) = ⊥) :
    (cov₀.transport (h := hfe n)).C ≃ₐ[R n] D.G hθ :=
  haveI := flat_NFall D.L D.M hO D.hflat D.hidem D.hfχ D.hcidem
  FormalPatchLevel.patchEquivOfEqBot hJ0 (f n) D.hJ D.σP (kappaF D.L D.M hθ) D.hfP
    (noTorsion_NFall D.L D.M D.hflat D.hidem D.hfχ D.hcidem D.hreg)

lemma Level.cEquiv_fst {n : ℕ} (D : Level R cov₀ πL hfe n) (hJ0 : J θ (R := R n) = ⊥)
    (c : (cov₀.transport (h := hfe n)).C) :
    ((D.cEquiv hθ hO hJ0 c : D.G hθ) : D.P × NFall D.L D.M).1 =
      FormalPatchLevel.toP hJ0 (f n) D.σP c := rfl

end LevelTower

namespace NodeEtaleGlue.Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} (I : Input θ cov₀ πL)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ}
  (hJ0 : J θ (R := I.B n) = ⊥)

include hJ0 in
lemma J_R_eq_bot : J θ (R := I.R n) = ⊥ := by
  rw [J, IsScalarTower.algebraMap_eq O (I.B n) (I.R n), ← Ideal.map_map]
  change Ideal.map _ (J θ (R := I.B n)) = ⊥
  rw [hJ0, Ideal.map_bot]

/-- `C1` over `B0` (through `B0 → B n → Bs`). -/
@[reducible] def algC10 (n : ℕ) : Algebra I.B0 I.C1 :=
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  NodeEtaleGlue.alg0 I.B I.B0 n I.C1

lemma algebraMap_C10 (x : I.B0) : (letI := I.algC10 n; algebraMap I.B0 I.C1 x) =
    algebraMap I.Bs I.C1 (I.qB n (algebraMap I.B0 (I.B n) x)) := rfl

/-- `C1 → cov₀.C ≃ G n`. -/
def φG : letI := I.algC10 n; letI := NodeEtaleGlue.alg0G I.T hθ I.B I.B0 n
    I.C1 →ₐ[I.B0] I.T.G hθ n :=
  letI := I.algC10 n
  letI := NodeEtaleGlue.alg0G I.T hθ I.B I.B0 n
  { RingHom.comp ((I.T.level n).cEquiv hθ hO (I.J_R_eq_bot hJ0)).toRingHom I.ι₀ with
    commutes' := fun x ↦ by
      change (I.T.level n).cEquiv hθ hO (I.J_R_eq_bot hJ0)
        (I.ι₀ (algebraMap I.Bs I.C1 (I.qB n (algebraMap I.B0 (I.B n) x)))) = _
      rw [NodeEtaleGlue.ι₀_algebraMap I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n]
      exact ((I.T.level n).cEquiv hθ hO (I.J_R_eq_bot hJ0)).commutes _ }

lemma φG_apply (c : I.C1) : I.φG hθ hO hJ0 c =
    (I.T.level n).cEquiv hθ hO (I.J_R_eq_bot hJ0) (I.ι₀ c) := rfl

/-- `C1 → C1[1/b̄] ≃ E n/J = E n`. -/
def φE : letI := I.algC10 n; letI := NodeEtaleGlue.alg0 I.B I.B0 n (I.E n)
    I.C1 →ₐ[I.B0] I.E n := by
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  letI := I.algC10 n
  letI := NodeEtaleGlue.alg0 I.B I.B0 n (I.E n)
  let g : I.C1 →ₐ[I.B n] I.E n :=
    ((FormalPatchLevel.quotEquivOfEqBot hJ0 (I.B n) (I.E n)).toAlgHom.comp
      (I.σE n).symm.toAlgHom).comp
      (IsScalarTower.toAlgHom (I.B n) I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)))
  exact { (g : I.C1 →+* I.E n) with commutes' := fun x ↦ g.commutes (algebraMap I.B0 (I.B n) x) }

lemma mk_φE (c : I.C1) : (letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (I.E n)) (I.φE hJ0 c) =
      (I.σE n).symm (algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) c)) :=
  FormalPatchLevel.mk_quotEquivOfEqBot hJ0 _

/-- **The two maps agree on the overlap** `E n[1/a]`. -/
lemma φG_compat (c : I.C1) :
    NodeEtaleGlue.ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv
      I.hJB I.B0 n (I.φG hθ hO hJ0 c) = NodeEtaleGlue.ρb0 I.B I.a I.E I.B0 n (I.φE hJ0 c) := by
  have hbot : NodeEtaleGlue.JZ (θ := θ) I.B I.a I.E n = ⊥ := by
    rw [NodeEtaleGlue.JZ, EtaleNil.JB, hJ0, Ideal.map_bot]
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hbot, ← Ideal.Quotient.eq]
  change Ideal.Quotient.mk (NodeEtaleGlue.JZ (θ := θ) I.B I.a I.E n)
      (NodeEtaleGlue.κn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv
        I.hJB n
        (FormalPatchLevel.toP (I.J_R_eq_bot hJ0) (I.T.f n) (I.T.level n).σP (I.ι₀ c))) =
    Ideal.Quotient.mk (NodeEtaleGlue.JZ (θ := θ) I.B I.a I.E n)
      (algebraMap (I.E n) (EtaleOverlap.Bab (I.a n) (I.E n)) (I.φE hJ0 c))
  rw [NodeEtaleGlue.mk_κn, FormalPatchLevel.mk_toP]
  letI := NodeEtaleGlue.algBC I.T I.B n
  haveI := NodeEtaleGlue.towerBC I.T I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  rw [OverlapFibre.μ_algebraMap]
  change OverlapFibre.γc _ _ _ _ _ (NodeEtaleGlue.ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n c) = _
  rw [OverlapFibre.γc_ι]
  change OverlapFibre.redE _ (I.a n) ((I.σE n).symm (algebraMap I.C1 _ c)) =
    OverlapFibre.redE _ (I.a n) (Ideal.Quotient.mk _ (I.φE hJ0 c))
  rw [mk_φE]

/-- `φG` is a localization away from `a0`. -/
lemma isLocalizedModule_φG :
    letI := I.algC10 n; letI := NodeEtaleGlue.alg0G I.T hθ I.B I.B0 n
    IsLocalizedModule (Submonoid.powers I.a0) (I.φG hθ hO hJ0).toLinearMap := by
  letI := I.algC10 n
  letI := NodeEtaleGlue.alg0G I.T hθ I.B I.B0 n
  refine ZariskiTwo.isLocalizedModule_of_away I.a0 _ ?_
  letI := (I.φG hθ hO hJ0).toRingHom.toAlgebra
  letI : Algebra I.C1 cov₀.C := I.ι₀.toAlgebra
  haveI := I.hι
  have e : cov₀.C ≃ₐ[I.C1] I.T.G hθ n := AlgEquiv.ofRingEquiv
    (f := ((I.T.level n).cEquiv hθ hO (I.J_R_eq_bot hJ0)).toRingEquiv) fun _ ↦ rfl
  have h := IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap I.Bs I.C1 I.abar)) e
  rw [algebraMap_C10, I.ha n]
  exact h

/-- `φE` is a localization away from `b0`. -/
lemma isLocalizedModule_φE :
    letI := I.algC10 n; letI := NodeEtaleGlue.alg0 I.B I.B0 n (I.E n)
    IsLocalizedModule (Submonoid.powers I.b0) (I.φE hJ0).toLinearMap := by
  letI := I.algC10 n
  letI := NodeEtaleGlue.alg0 I.B I.B0 n (I.E n)
  refine ZariskiTwo.isLocalizedModule_of_away I.b0 _ ?_
  letI := (I.φE hJ0).toRingHom.toAlgebra
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  have e : Localization.Away (algebraMap I.Bs I.C1 I.bbar) ≃ₐ[I.C1] I.E n := AlgEquiv.ofRingEquiv
    (f := ((I.σE n).symm.trans (FormalPatchLevel.quotEquivOfEqBot hJ0 (I.B n) (I.E n))).toRingEquiv)
    fun _ ↦ rfl
  have h := IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap I.Bs I.C1 I.bbar)) e
  rw [algebraMap_C10, I.hbb n]
  exact h

/-- **The glued covering at a level with `J = 0` is the given covering `C1`**:
`C1 ≃ₐ[B0] Y n`. -/
def yEquiv : letI := I.algC10 n; I.C1 ≃ₐ[I.B0] I.Y hθ n := by
  letI := I.algC10 n
  letI := NodeEtaleGlue.alg0G I.T hθ I.B I.B0 n
  letI := NodeEtaleGlue.alg0 I.B I.B0 n (I.E n)
  letI := NodeEtaleGlue.alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  haveI := I.isLocalizedModule_φG hθ hO hJ0
  haveI := I.isLocalizedModule_φE hJ0
  haveI := NodeEtaleGlue.locFst I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE
    I.hbE I.hdiv I.hJB I.B0 (fun _ ↦ rfl) n
  haveI := NodeEtaleGlue.locSnd I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E
    I.σE I.hbE I.hdiv I.hbb I.hJB I.B0 (fun _ ↦ rfl) n
  exact ZariskiTwo.liftEquiv I.a0 I.b0 I.hab (I.φG hθ hO hJ0) (I.φE hJ0) (I.φG_compat hθ hO hJ0)

end NodeEtaleGlue.Input

end

end SemistableReduction
