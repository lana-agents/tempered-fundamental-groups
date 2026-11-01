/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevels
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelEquiv

/-!
# The special fibre of `ψ` on the levels `levelEquivX` (MR12 T2 S6, G4 over `V₀`)

For the identification `levelEquivX : X ≃ Y l` of `FormalLevel.NodeLevels` and an overlap datum
`Vo : NodeEtaleGlue.Overlap I`, the restriction `ψ : Y l → M l` to the overlap reduces modulo `J`
to `γM ∘ ρX` (**`FormalLevel.NodeLevels.mk_ψ_levelEquivX`**, from `Input.mk_ψ`, `hGX` and the
compatibility `hE` of the étale piece): the hypothesis `hψ` of `Overlap.φQn_compat`.
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

namespace FormalLevel

open KummerEtale FormalKummer AdmissibleLift NodeEtaleGlue

attribute [local instance] KummerNormAtData.algO

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ϖ : O} {n M' : ℕ} {x y : R}
  {hxy : x * y = algebraMap O R (ϖ ^ n)} {hϖ : θ ϖ = 0} {hn0 : 0 < n}
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  {hJ : ∀ j, J θ (R := R) ≤ 𝔪 j}
  {hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R))}
  {D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)} {g : R}
  {hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j)}
  {hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j)}
  {hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical}
  {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g)}
  {hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x)}
  {hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g)}
  {hfin : Module.Finite (Rs θ R) (Cs θ R B)}
  {het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale}
  {hk : ∀ j i, ((D j).d i : k) ≠ 0}
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]

variable
  (I : Input θ (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk) (πK 𝔪 D))
  [algRI : ∀ l, Algebra R (I.R l)] [towerORI : ∀ l, IsScalarTower O R (I.R l)]
  [towerRII : ∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    LevelTower.Data (θ := θ) I.R (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
      het hk) (πK 𝔪 D)}
  (V : NodeLevels hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T')
  (he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (I.R l) r))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)) = I.algkR) (hT : HEq T' I.T)

namespace NodeLevels

variable {l : ℕ} {X : Type u} [CommRing X] [Algebra (I.B l) X]
  (t : X →+* I.R l ⊗[R] B)
  (ht : ∀ r, t (algebraMap (I.B l) X r) =
    algebraMap (I.R l) (I.R l ⊗[R] B) (algebraMap (I.B l) (I.R l) r))
  (ρX : letI := algC1 I.B I.qB I.C1 l; X →ₐ[I.B l] I.C1)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ x, ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T'.hfe he l
      (t x) = I.ι₀ (ρX x))
  [Algebra I.B0 X] [towerX : IsScalarTower I.B0 (I.B l) X]
  (htloc : letI := t.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.a l)) (I.R l ⊗[R] B))
  (φE : X →ₐ[I.B l] I.E l)
  (hE : ∀ x, I.σE l (Ideal.Quotient.mk _ (φE x)) =
    algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX x))
  (hlocE : letI := φE.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.b l)) (I.E l))
  (Vo : Overlap I)

omit [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)] in
set_option maxRecDepth 20000 in
/-- **The special fibre of `ψ` on `levelEquivX`**: `ψ (levelEquivX x) ≡ γM (ρX x)` modulo `J`. -/
theorem mk_ψ_levelEquivX (x : X) : letI := Vo.algBM l
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B l)) (Vo.M l))
      (Vo.ψ hθ.out hO l (V.levelEquivX I he hO hkI hT t ht ρX hρ htloc φE hE hlocE x)) =
    Vo.γM l (ρX x) := by
  letI := Vo.algBM l
  letI := Vo.alg0M l
  haveI := Vo.formallyEtale_M l
  haveI := Vo.tower0M l
  exact I.mk_ψ hθ.out hO l Vo.g (Vo.hfg l) (Vo.γM l) (Vo.isLocalization_γM l) _ (ρX x)
    (V.hGX I he hO hkI hT t ht ρX hρ x) (hE x)

end NodeLevels

end FormalLevel

end

end SemistableReduction
