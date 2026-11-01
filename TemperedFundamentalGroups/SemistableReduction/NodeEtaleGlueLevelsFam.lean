/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevels

/-!
# Families of identifications with the glued coverings (MR12 T2 S6, step G4)

* **`NodeEtaleGlue.Input.LevelEquivFam`**: identifications `X l ≃ₐ[B0] Y l` of a family of
  `B0`-algebras with the glued coverings of an input, together with their compatibility with
  given successor maps `μ l : X (l + 1) → X l` and the successor maps `Ymap` of the coverings;
* **`FormalLevel.NodeLevels.levelEquivXFam`**: such a family from families of the data of
  `levelEquivX` (the successor compatibility is `levelEquivX_succ`).

A concrete tower (the Tate curve over `V₁`) instantiates `levelEquivXFam` once with its families;
its successor compatibility is then the field `succ`, so that the concrete types never have to
unify an application of `levelEquivX_succ` at the levels `n + 1`, `n` with a concrete goal.
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

namespace NodeEtaleGlue.Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}

/-- **A family of identifications with the glued coverings**: `B0`-algebra isomorphisms
`X l ≃ Y l` commuting with the successor maps `μ l : X (l + 1) → X l` and `Ymap l`. -/
structure LevelEquivFam (I : Input θ cov₀ πL) (hθ : Function.Surjective θ)
    (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (X : ℕ → Type u) [∀ l, CommRing (X l)]
    [∀ l, Algebra I.B0 (X l)] (μ : ∀ l, X (l + 1) →+* X l) where
  /-- The identification at level `l`. -/
  equiv : ∀ l, X l ≃ₐ[I.B0] I.Y hθ l
  /-- The identifications commute with the successor maps. -/
  succ : ∀ l (x : X (l + 1)), I.Ymap hθ hO l (equiv (l + 1) x) = equiv l (μ l x)

end NodeEtaleGlue.Input

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
  (hμE : ∀ l x, I.sE l (φE (l + 1) x) = φE l (μ l x))

/-- **G4 for a family of levels**: the identifications `levelEquivX` of the levels `X l` with the
glued coverings `Y l`, compatible with the successor maps `μ` (`levelEquivX_succ`). -/
def levelEquivXFam : I.LevelEquivFam hθ.out hO X μ where
  equiv l := V.levelEquivX I he hO hkI hT (t l) (ht l) (ρX l) (hρ l) (htloc l) (φE l) (hE l)
    (hlocE l)
  succ l x := V.levelEquivX_succ I he hO hkI hT (t l) (ht l) (ρX l) (hρ l) (htloc l) (φE l) (hE l)
    (hlocE l) (t (l + 1)) (ht (l + 1)) (ρX (l + 1)) (hρ (l + 1)) (htloc (l + 1)) (φE (l + 1))
    (hE (l + 1)) (hlocE (l + 1)) (μ l) (hμt l) (hμE l) x

lemma levelEquivXFam_equiv (l : ℕ) :
    (V.levelEquivXFam I he hO hkI hT t ht ρX hρ htloc φE hE hlocE μ hμt hμE).equiv l =
      V.levelEquivX I he hO hkI hT (t l) (ht l) (ρX l) (hρ l) (htloc l) (φE l) (hE l)
        (hlocE l) := rfl

end NodeLevels

end FormalLevel

end

end SemistableReduction
