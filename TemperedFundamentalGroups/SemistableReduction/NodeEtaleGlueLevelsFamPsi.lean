/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevelsFam
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelPsi

/-!
# The special fibre of `ψ` on a family `levelEquivXFam` (MR12 T2 S6, G5)

**`FormalLevel.NodeLevels.mk_ψ_levelEquivXFam`**: `mk_ψ_levelEquivX` for the identifications of
the family `levelEquivXFam` (the hypothesis `hψ1` of
`NodeEtaleGlue.Overlap.exists_iso_of_cuspLevels`), stated with the family itself, so that at
concrete data the family is not unfolded to its components.
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

variable {X : ℕ → Type u} [∀ l, CommRing (X l)] [∀ l, Algebra (I.B l) (X l)]
  [∀ l, Algebra I.B0 (X l)] [towerX : ∀ l, IsScalarTower I.B0 (I.B l) (X l)]
  (t : ∀ l, X l →+* I.R l ⊗[R] B)
  (ht : ∀ l r, t l (algebraMap (I.B l) (X l) r) =
    algebraMap (I.R l) (I.R l ⊗[R] B) (algebraMap (I.B l) (I.R l) r))
  (ρX : ∀ l, letI := algC1 I.B I.qB I.C1 l; X l →ₐ[I.B l] I.C1)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ l x, ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T'.hfe he l
      (t l x) = I.ι₀ (ρX l x))
  (htloc : ∀ l, letI := (t l).toAlgebra
    IsLocalization.Away (algebraMap (I.B l) (X l) (I.a l)) (I.R l ⊗[R] B))
  (φE : ∀ l, X l →ₐ[I.B l] I.E l)
  (hE : ∀ l x, I.σE l (Ideal.Quotient.mk _ (φE l x)) =
    algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX l x))
  (hlocE : ∀ l, letI := (φE l).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) (X l) (I.b l)) (I.E l))
  (μ : ∀ l, X (l + 1) →+* X l) (hμt : ∀ l x, t l (μ l x) = levelMap I.R l (t (l + 1) x))
  (hμE : ∀ l x, I.sE l (φE (l + 1) x) = φE l (μ l x)) (Vo : Overlap I)

/-- **The special fibre of `ψ` on the family `levelEquivXFam`**: `ψ (equiv l x) ≡ γM (ρX l x)`
modulo `J` (`mk_ψ_levelEquivX`). -/
theorem mk_ψ_levelEquivXFam (l : ℕ) (x : X l) : letI := Vo.algBM l
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B l)) (Vo.M l))
      (Vo.ψ hθ.out hO l
        ((V.levelEquivXFam I he hO hkI hT t ht ρX hρ htloc φE hE hlocE μ hμt hμE).equiv l x)) =
    Vo.γM l (ρX l x) :=
  V.mk_ψ_levelEquivX I he hO hkI hT (t l) (ht l) (ρX l) (hρ l) (htloc l) (φE l) (hE l)
    (hlocE l) Vo x

end NodeLevels

end FormalLevel

end

end SemistableReduction
