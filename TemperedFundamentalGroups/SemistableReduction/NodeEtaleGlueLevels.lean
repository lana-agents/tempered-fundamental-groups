/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevel
import TemperedFundamentalGroups.SemistableReduction.FormalLevelPatchTr
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapGlue

/-!
# The levels of a glued covering from the level data of its node patches (MR12 T2 S6, step G4)

Let `I : NodeEtaleGlue.Input` be the input of a glueing whose node patches are the levels of the
M2 lift of a covering `covOf …` (`FormalLevel.NodeLevels V` over a tower `T'` on the node charts
`I.R` of the input, with `T'` equal to `I.T` and the `k`-algebra structures on the special fibres
equal). Let `X` be a `B n`-algebra with a localization `t : X → I.R n ⊗_R B` away from `a`, an
étale piece `φE : X → E n` (localization away from `b`) and a reduction `ρX : X → C1` compatible
with the reduction `ρ` of `V` and with `σE`. Then:

* **`LevelTower.Data.GEquivOfInst`**: the patched algebras of equal towers with equal
  `k`-algebra structures are isomorphic (the identity after substitution), with
  `GEquivOfInst_σP` (compatibility with `σP`) and `GEquivOfInst_tr` (with the transition maps);
* **`FormalLevel.NodeLevels.inputEquiv`**: `I.R n ⊗_R B ≃ G n` (the level patch of `V`);
* **`FormalLevel.NodeLevels.levelEquivX`**: `X ≃ₐ[B0] I.Y n` (`NodeEtaleGlue.Input.levelEquiv`);
* **`FormalLevel.NodeLevels.levelEquivX_succ`**: compatibility with the successor maps.

These are stated generically so that concrete towers (the Tate curve over `V₁`) never compare the
patched algebras of the input's tower with those of the tower of the level data.
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

namespace LevelTower.Data

open AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)] [∀ n, IsNoetherianRing (R n)]
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (i1 i2 : ∀ n, Algebra k (R n ⧸ J θ (R := R n))) (h : i1 = i2)
  (T1 : letI := i1; Data (θ := θ) R cov₀ πL) (T2 : letI := i2; Data (θ := θ) R cov₀ πL)
  (hT : HEq T1 T2) (hθ : Function.Surjective θ)

/-- **The patched algebras of equal towers** (with equal `k`-algebra structures on the special
fibres, which need not be syntactically equal) are isomorphic: the identity after substitution. -/
def GEquivOfInst (n : ℕ) : (letI := i1; T1.G hθ n) ≃ₐ[R n] (letI := i2; T2.G hθ n) := by
  subst h
  subst hT
  exact AlgEquiv.refl

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
/-- `GEquivOfInst` is compatible with the identifications `σP` of the étale parts. -/
theorem GEquivOfInst_σP (n : ℕ) (x : letI := i1; T1.G hθ n) (c : cov₀.C)
    (hx : letI := i1; (T1.level n).σP (Ideal.Quotient.mk _ x.1.1) =
      algebraMap (cov₀.transport (h := T1.hfe n)).C _ c) :
    letI := i2; (T2.level n).σP (Ideal.Quotient.mk _ (GEquivOfInst i1 i2 h T1 T2 hT hθ n x).1.1) =
      algebraMap (cov₀.transport (h := T2.hfe n)).C _ c := by
  subst h
  subst hT
  exact hx

/-- `GEquivOfInst` is compatible with the transition maps. -/
theorem GEquivOfInst_tr (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)
    (x : letI := i1; T1.G hθ (n + 1)) :
    (letI := i2; T2.tr hθ hO n) (GEquivOfInst i1 i2 h T1 T2 hT hθ (n + 1) x) =
      GEquivOfInst i1 i2 h T1 T2 hT hθ n ((letI := i1; T1.tr hθ hO n) x) := by
  subst h
  subst hT
  rfl

end LevelTower.Data

namespace NodeEtaleGlue.Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}

/-- A map `X → G n` over the base level `B n`, from an identification `M ≃ G n` over the node
chart `R n` and a ring map `X → M` compatible with `B n → R n`. -/
def φGOf (I : Input θ cov₀ πL) (hθ : Function.Surjective θ) (n : ℕ) {X M : Type u}
    [CommRing X] [Algebra (I.B n) X] [CommRing M] [Algebra (I.R n) M]
    (e : M ≃ₐ[I.R n] I.T.G hθ n) (t : X →+* M)
    (ht : ∀ r, t (algebraMap (I.B n) X r) = algebraMap (I.R n) M (algebraMap (I.B n) (I.R n) r)) :
    letI := NodeEtaleGlue.algBG I.T hθ I.B n
    X →ₐ[I.B n] I.T.G hθ n :=
  letI := NodeEtaleGlue.algBG I.T hθ I.B n
  { e.toRingEquiv.toRingHom.comp t with
    commutes' := fun r ↦ by
      change e (t (algebraMap (I.B n) X r)) = _
      rw [ht, AlgEquiv.commutes]
      rfl }

lemma φGOf_apply (I : Input θ cov₀ πL) (hθ : Function.Surjective θ) (n : ℕ) {X M : Type u}
    [CommRing X] [Algebra (I.B n) X] [CommRing M] [Algebra (I.R n) M]
    (e : M ≃ₐ[I.R n] I.T.G hθ n) (t : X →+* M)
    (ht : ∀ r, t (algebraMap (I.B n) X r) = algebraMap (I.R n) M (algebraMap (I.B n) (I.R n) r))
    (x : X) : I.φGOf hθ n e t ht x = e (t x) := rfl

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
  (I : Input θ (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk) (πK 𝔪 D))
  [∀ l, Algebra R (I.R l)] [∀ l, IsScalarTower O R (I.R l)]
  [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    LevelTower.Data (θ := θ) I.R (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
      het hk) (πK 𝔪 D)}
  (V : NodeLevels hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T')
  (he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (I.R l) r))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)) = I.algkR) (hT : HEq T' I.T)

namespace NodeLevels

/-- **The level patches of `V` as the node patches of the input**: `I.R l ⊗_R B ≃ I.T.G l`. -/
def inputEquiv (l : ℕ) : I.R l ⊗[R] B ≃ₐ[I.R l] I.T.G hθ.out l :=
  (V.equiv he hO l).trans
    (LevelTower.Data.GEquivOfInst _ I.algkR hkI T' I.T hT hθ.out l)

set_option maxRecDepth 20000 in
/-- **The level patches of `V` as the node patches of the input form a tower.** -/
theorem inputEquiv_tr (l : ℕ) (z : I.R (l + 1) ⊗[R] B) :
    I.T.tr hθ.out hO l (V.inputEquiv I he hO hkI hT (l + 1) z) =
      V.inputEquiv I he hO hkI hT l (levelMap I.R l z) :=
  (LevelTower.Data.GEquivOfInst_tr _ I.algkR hkI T' I.T hT hθ.out hO l
    (V.equiv he hO (l + 1) z)).trans
    (congrArg (LevelTower.Data.GEquivOfInst _ I.algkR hkI T' I.T hT hθ.out l)
      (V.equiv_tr he hO l z))

variable {l : ℕ} {X : Type u} [CommRing X] [Algebra (I.B l) X]
  (t : X →+* I.R l ⊗[R] B)
  (ht : ∀ r, t (algebraMap (I.B l) X r) =
    algebraMap (I.R l) (I.R l ⊗[R] B) (algebraMap (I.B l) (I.R l) r))

/-- **The node side of `X`**: `X → I.R l ⊗_R B ≃ G l`. -/
def φGX : letI := algBG I.T hθ.out I.B l; X →ₐ[I.B l] I.T.G hθ.out l :=
  I.φGOf hθ.out l (V.inputEquiv I he hO hkI hT l) t ht

variable (ρX : letI := algC1 I.B I.qB I.C1 l; X →ₐ[I.B l] I.C1)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ x, ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T'.hfe he l
      (t x) = I.ι₀ (ρX x))

set_option maxRecDepth 20000 in
omit [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)] in
include hρ in
/-- The node side of `X` is compatible with the reductions to the special fibre. -/
theorem hGX (x : X) :
    (letI := algBP I.T I.B l; σPn I.T I.B l (Ideal.Quotient.mk _
      (fstP I.T hθ.out l (V.φGX I he hO hkI hT t ht x)))) =
    algebraMap (Cc I.T l) _ (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ l (ρX x)) := by
  have h := V.σP_φ₁ he l (t x)
  rw [hρ] at h
  exact LevelTower.Data.GEquivOfInst_σP _ I.algkR hkI T' I.T hT hθ.out l
    (V.equiv he hO l (t x)) (I.ι₀ (ρX x)) h

omit [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)] in
include ht in
/-- The node side of `X` is a localization away from `a`. -/
theorem hlocGX (htloc : letI := t.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.a l)) (I.R l ⊗[R] B)) :
    letI := algBG I.T hθ.out I.B l
    letI := (V.φGX I he hO hkI hT t ht).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.a l)) (I.T.G hθ.out l) :=
  RingHomAway.equiv _ (V.inputEquiv I he hO hkI hT l).toRingEquiv _ htloc

variable [Algebra I.B0 X] [IsScalarTower I.B0 (I.B l) X]
  (htloc : letI := t.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.a l)) (I.R l ⊗[R] B))
  (φE : X →ₐ[I.B l] I.E l)
  (hE : ∀ x, I.σE l (Ideal.Quotient.mk _ (φE x)) =
    algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX x))
  (hlocE : letI := φE.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.b l)) (I.E l))

/-- **G4 from the level data of the node patches: `X` is the glued covering**,
`X ≃ₐ[B0] Y l` (`NodeEtaleGlue.Input.levelEquiv`), with components `φGX`, `φE`. -/
def levelEquivX : X ≃ₐ[I.B0] I.Y hθ.out l :=
  I.levelEquiv hθ.out hO l (V.φGX I he hO hkI hT t ht) φE ρX (V.hGX I he hO hkI hT t ht ρX hρ) hE
    hlocE (V.hlocGX I he hO hkI hT t ht htloc)

omit [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)] in
lemma levelEquivX_fst (x : X) :
    (V.levelEquivX I he hO hkI hT t ht ρX hρ htloc φE hE hlocE x).1.1 =
      V.inputEquiv I he hO hkI hT l (t x) := rfl

omit [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)] in
lemma levelEquivX_snd (x : X) :
    (V.levelEquivX I he hO hkI hT t ht ρX hρ htloc φE hE hlocE x).1.2 = φE x := rfl

set_option maxHeartbeats 1000000 in
-- unfolding `Ymap` to the transition maps of the components
set_option maxRecDepth 20000 in
/-- **The identifications `levelEquivX` form a tower**: for `μ : X' → X` (at levels `l + 1`, `l`)
compatible with the maps `t`, `levelMap` and with the étale pieces and their successor maps `sE`,
`levelEquivX` commutes with the successor maps `Ymap` of the glued coverings. -/
theorem levelEquivX_succ {X' : Type u} [CommRing X'] [Algebra (I.B (l + 1)) X'] [Algebra I.B0 X']
    [IsScalarTower I.B0 (I.B (l + 1)) X'] (t' : X' →+* I.R (l + 1) ⊗[R] B)
    (ht' : ∀ r, t' (algebraMap (I.B (l + 1)) X' r) =
      algebraMap (I.R (l + 1)) (I.R (l + 1) ⊗[R] B) (algebraMap (I.B (l + 1)) (I.R (l + 1)) r))
    (ρX' : letI := algC1 I.B I.qB I.C1 (l + 1); X' →ₐ[I.B (l + 1)] I.C1)
    (hρ' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
      ∀ x, ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T'.hfe he
        (l + 1) (t' x) = I.ι₀ (ρX' x))
    (htloc' : letI := t'.toAlgebra
      IsLocalization.Away (algebraMap (I.B (l + 1)) X' (I.a (l + 1))) (I.R (l + 1) ⊗[R] B))
    (φE' : X' →ₐ[I.B (l + 1)] I.E (l + 1))
    (hE' : ∀ x, I.σE (l + 1) (Ideal.Quotient.mk _ (φE' x)) =
      algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX' x))
    (hlocE' : letI := φE'.toRingHom.toAlgebra
      IsLocalization.Away (algebraMap (I.B (l + 1)) X' (I.b (l + 1))) (I.E (l + 1)))
    (μ : X' →+* X) (hμt : ∀ x, t (μ x) = levelMap I.R l (t' x))
    (hμE : ∀ x, I.sE l (φE' x) = φE (μ x)) (x : X') :
    I.Ymap hθ.out hO l
        (V.levelEquivX I he hO hkI hT t' ht' ρX' hρ' htloc' φE' hE' hlocE' x) =
      V.levelEquivX I he hO hkI hT t ht ρX hρ htloc φE hE hlocE (μ x) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact (V.inputEquiv_tr I he hO hkI hT l (t' x)).trans
      (congrArg (V.inputEquiv I he hO hkI hT l) (hμt x).symm)
  · exact hμE x

end NodeLevels

end FormalLevel

end

end SemistableReduction
