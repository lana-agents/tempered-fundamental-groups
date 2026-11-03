/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerHomH
import TemperedFundamentalGroups.SemistableReduction.OverlapHom

/-!
# Maps of glueing inputs from heterogeneous node level maps (generic; MR12 I3)

For two glueing inputs `I`, `I'` (`NodeEtaleGlue.Input`) of node-only coverings over equal but
differently spelled base data (`hR : I'.R = I.R`, `HEq` of the instance families, of `f` and of
`e`), and a map `φ : cov₀.C → cov₀'.C` of the special-fibre coverings balanced at every level:

* **`NodeEtaleGlue.Input.gH`**: the maps of the node patches `I.T.G n → I'.T.G n`
  (`LevelTower.nodeLevelMapH` between `I.T.level n` and `I'.T.level n`);
* `fstP_gH` (the first component is `pMapH`), **`hg_gH`** (the overlap condition `hg` of
  `Input.yMap`, by `Input.hg_of_special`), **`tr_gH`** (compatibility with the transition maps,
  the hypothesis `hgS` of `Input.yMap_succ`), `gH_algebraMap` (the hypothesis `hgβ` of
  `Input.yMap_algebraMap`).

All statements are generic, so that at a concrete pair of inputs (the Tate inputs
`TateGlue1.input … Sp`, `… Sp'`) they are applied with explicit arguments only: elaborating
statements such as `(g x).1.1 = p x.1.1` or `p (algebraMap _ _ r) = …` directly at the concrete
inputs does not terminate (the unifier unfolds the `abbrev` chains of the patched levels down
to the concrete charts, MR12 c48/c49).
-/

universe u

namespace SemistableReduction

open AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue.Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  (I : Input θ cov₀ πL) (I' : Input θ cov₀' πL') (hθ : Function.Surjective θ)
  (hR : I'.R = I.R) (hc : HEq I'.commRingR I.commRingR) (ha : HEq I'.algOR I.algOR)
  (hk : HEq I'.algkR I.algkR) (hF : HEq I'.T.f I.T.f) (hE : HEq I'.T.e I.T.e)
  [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ] (φ : cov₀.C →ₐ[R₀] cov₀'.C)
  {cu cv : ∀ n, FormalPatchLevel.Hat (I.T.f n)}
  (hcd : ∀ n, NodeCoord (I.T.level n) (cu n) (cv n))
  {cu' cv' : ∀ n, FormalPatchLevel.Hat (I'.T.f n)}
  (hcd' : ∀ n, NodeCoord (I'.T.level n) (cu' n) (cv' n))
  (hcu : ∀ n, HEq (cu' n) (cu n)) (hcv : ∀ n, HEq (cv' n) (cv n))
  (hbal : ∀ n, NodeBalanced I.T.hfe πL πL' φ n)

/-- **The maps of the node patches** `I.T.G n → I'.T.G n` induced by a balanced `φ`
(`LevelTower.nodeLevelMapH`). -/
def gH (n : ℕ) : I.T.G hθ n →+* I'.T.G hθ n :=
  nodeLevelMapH hθ hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ (hcd n) (hcd' n) (hcu n)
    (hcv n) (hbal n)

/-- The first component of `gH` is `pMapH`. -/
lemma fstP_gH (n : ℕ) (x : I.T.G hθ n) :
    fstP I'.T hθ n (gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n x) =
      pMapH hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ (fstP I.T hθ n x) :=
  fst_nodeLevelMapH hθ hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ (hcd n) (hcd' n)
    (hcu n) (hcv n) (hbal n) x

/-- **The overlap condition `hg` of `Input.yMap` for `gH`** (`Input.hg_of_special` with
`p := pMapH`, `ℓf := nfMapH`). -/
theorem hg_gH (n : ℕ) (e : I.E n →+* I'.E n)
    (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n))
    (β : I.B n →+* I'.B n) (hβJ : (J θ (R := I.B n)).map β ≤ J θ (R := I'.B n))
    (hβa : β (I.a n) = I'.a n)
    (heβ : ∀ r, e (algebraMap (I.B n) (I.E n) r) = algebraMap (I'.B n) (I'.E n) (β r))
    (hβR : ∀ r, HEq (algebraMap (I'.B n) (I'.R n) (β r)) (algebraMap (I.B n) (I.R n) r))
    (φ1 : I.C1 →+* I'.C1) (hφc : ∀ c, φ (I.ι₀ c) = I'.ι₀ (φ1 c))
    (ℓb : Localization.Away (algebraMap I.Bs I.C1 I.bbar) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 I'.bbar))
    (hℓb : ∀ c, ℓb (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hσE : ∀ x, (letI := NodeEtaleGlue.algC1 I'.B I'.qB I'.C1 n
        I'.σE n (Ideal.Quotient.mk _ (e x))) =
      ℓb (letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n; I.σE n (Ideal.Quotient.mk _ x)))
    (x : I.T.G hθ n) :
    ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE
      I'.hbE I'.hdiv I'.hJB I'.B0 n (gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n x) =
    I.eab I' n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB I.B0 n x) :=
  I.hg_of_special I' hθ n (gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n) e he β hβJ hβa
    heβ (pMapH hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ)
    (fstP_gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n)
    (fun r ↦ pMapH_algebraMap hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ _ _ (hβR r))
    φ.toRingHom (nfMapH (n := n) hR hc ha hk hF hE (hfe := I.T.hfe) (hfe' := I'.T.hfe) φ)
    (fun c ↦ nfMapH_algebraMap hR hc ha hk hF hE φ c)
    (fun y ↦ σP_pMapH hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ y)
    φ1 hφc ℓb hℓb hσE x

/-- `gH` is compatible with a map `β0 : B0 → B0'` of the bases (the hypothesis `hgβ` of
`Input.yMap_algebraMap`). -/
lemma gH_algebraMap (n : ℕ) (β0 : I.B0 →+* I'.B0)
    (hβ0 : ∀ b, HEq (algebraMap (I'.B n) (I'.R n) (algebraMap I'.B0 (I'.B n) (β0 b)))
      (algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) b))) (b : I.B0) :
    gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n
        (letI := alg0G I.T hθ I.B I.B0 n; algebraMap I.B0 (I.T.G hθ n) b) =
      (letI := alg0G I'.T hθ I'.B I'.B0 n; algebraMap I'.B0 (I'.T.G hθ n) (β0 b)) :=
  nodeLevelMapH_algebraMap hθ hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ (hcd n) (hcd' n)
    (hcu n) (hcv n) (hbal n) _ _ (hβ0 b)

/-- **`gH` commutes with the transition maps** (the hypothesis `hgS` of `Input.yMap_succ`). -/
theorem tr_gH (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (hs : HEq I'.algSuccR I.algSuccR) (n : ℕ)
    (x : I.T.G hθ (n + 1)) :
    I'.T.tr hθ hO n (gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal (n + 1) x) =
      gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n (I.T.tr hθ hO n x) :=
  tr_nodeLevelMapH hθ hO I.T.hq I.T.hf I.T.he I.T.level I.T.hcχ
    (hεε_mk I.T.hfe I.T.hπ I.T.χ I.T.hχ I.T.t I.T.ht I.T.hJ I.T.hflat I.T.hfχ I.T.hreg I.T.hf
      I.T.he)
    (hδδ_mk I.T.hfe I.T.hπ I.T.χ I.T.hχ I.T.t I.T.ht I.T.hJ I.T.hflat I.T.hfχ I.T.hreg I.T.hf
      I.T.he) I.T.hct I'.T.hq I'.T.hf I'.T.he I'.T.level I'.T.hcχ
    (hεε_mk I'.T.hfe I'.T.hπ I'.T.χ I'.T.hχ I'.T.t I'.T.ht I'.T.hJ I'.T.hflat I'.T.hfχ
      I'.T.hreg I'.T.hf I'.T.he)
    (hδδ_mk I'.T.hfe I'.T.hπ I'.T.χ I'.T.hχ I'.T.t I'.T.ht I'.T.hJ I'.T.hflat I'.T.hfχ
      I'.T.hreg I'.T.hf I'.T.he) I'.T.hct hR hc ha hk hs hF hE φ hcd hcd' hcu hcv hbal n x

end NodeEtaleGlue.Input

end

end SemistableReduction
