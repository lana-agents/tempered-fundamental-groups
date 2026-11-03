/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.InputNodeHomH
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSystemMap

/-!
# Morphisms of the adic systems of two overlaps of node-only coverings (generic; MR12 I3)

For two overlaps `V : Overlap I`, `V' : Overlap I'` whose inputs have node-only coverings over
equal but differently spelled base data (as in `InputNodeHomH`), a balanced map `φ` of the
coverings of the node charts, maps `e n` of the étale pieces reducing to `φ1 : C1 → C1'`, and
maps `p n` of the pieces over the second chart reducing to `φ1` through the overlap
identifications:

* **`NodeEtaleGlue.Input.yH`**: the maps of the coverings over the first chart
  (`Input.yMap` of `gH` and `e n`, the overlap condition by `hg_gH`), `yH_algebraMap`,
  `yH_succ`, `yH_yEquiv`;
* **`NodeEtaleGlue.Overlap.systemMapH`**: the morphism of the adic systems of chart algebras
  (`Overlap.systemMap`; the overlap condition `hψ` by `Overlap.hψ_of_bottom`).

At a concrete pair of overlaps (the Tate coverings) `systemMapH` is applied once with explicit
arguments; no statement relating the patched levels of the two inputs is elaborated there
(MR12 c49: such statements do not terminate at the Tate charts).
-/

universe u

namespace SemistableReduction

open AdmissibleLift LevelTower ProjectiveLine

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}

namespace Input

variable (I : Input θ cov₀ πL) (I' : Input θ cov₀' πL') (hθ : Function.Surjective θ)
  (hR : I'.R = I.R) (hc : HEq I'.commRingR I.commRingR) (ha : HEq I'.algOR I.algOR)
  (hk : HEq I'.algkR I.algkR) (hF : HEq I'.T.f I.T.f) (hE : HEq I'.T.e I.T.e)
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

/-- **The maps of the coverings over the first chart** (`Input.yMap` of `gH` and `e n`). -/
def yH (n : ℕ) : I.Y hθ n →+* I'.Y hθ n :=
  I.yMap I' hθ n (gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n) (e n) (he n)
    (hg_gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n (e n) (he n) (β n) (hβJ n)
      (hβa n) (heβ n) (hβR n) φ1 hφc ℓb hℓb (hσE n))

/-- `yH` is compatible with a map `β0 : B0 → B0'` compatible with the `β n`. -/
lemma yH_algebraMap (β0 : I.B0 →+* I'.B0)
    (hβ0 : ∀ n b, β n (algebraMap I.B0 (I.B n) b) = algebraMap I'.B0 (I'.B n) (β0 b)) (n : ℕ)
    (b : I.B0) :
    yH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1 hφc ℓb hℓb
        hσE n (algebraMap I.B0 (I.Y hθ n) b) =
      algebraMap I'.B0 (I'.Y hθ n) (β0 b) := by
  refine I.yMap_algebraMap I' hθ n _ _ _ _ β0
    (gH_algebraMap I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n β0 fun b ↦ ?_)
    (fun b ↦ ?_) b
  · have h := hβR n (algebraMap I.B0 (I.B n) b)
    rwa [hβ0] at h
  · change e n (algebraMap (I.B n) (I.E n) (algebraMap I.B0 (I.B n) b)) =
      algebraMap (I'.B n) (I'.E n) (algebraMap I'.B0 (I'.B n) (β0 b))
    rw [heβ, hβ0]

/-- `yH` commutes with the successor maps. -/
lemma yH_succ (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (hs : HEq I'.algSuccR I.algSuccR)
    (heS : ∀ n x, I'.sE n (e (n + 1) x) = e n (I.sE n x)) (n : ℕ) (z : I.Y hθ (n + 1)) :
    I'.Ymap hθ hO n (yH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR
        φ1 hφc ℓb hℓb hσE (n + 1) z) =
      yH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1 hφc ℓb hℓb
        hσE n (I.Ymap hθ hO n z) :=
  I.yMap_succ I' hθ hO (fun n ↦ gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n) e he
    (fun n ↦ hg_gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n (e n) (he n) (β n)
      (hβJ n) (hβa n) (heβ n) (hβR n) φ1 hφc ℓb hℓb (hσE n))
    (fun n x ↦ tr_gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal hO hs n x) heS n z

/-- At a level with `J = 0`, `yH` is `φ1` on the identifications `yEquiv : C1 ≃ Y n`. -/
lemma yH_yEquiv (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ) (hJ0 : J θ (R := I.B n) = ⊥)
    (hJ0' : J θ (R := I'.B n) = ⊥) (c : I.C1) :
    yH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1 hφc ℓb hℓb
        hσE n (I.yEquiv hθ hO hJ0 c) = I'.yEquiv hθ hO hJ0' (φ1 c) :=
  I.yMap_yEquiv I' hθ n (gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n) (e n) (he n)
    (pMapH hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ)
    (fstP_gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n)
    φ.toRingHom (nfMapH (n := n) hR hc ha hk hF hE (hfe := I.T.hfe) (hfe' := I'.T.hfe) φ)
    (fun c ↦ nfMapH_algebraMap hR hc ha hk hF hE φ c)
    (fun y ↦ σP_pMapH hR hc ha hk hF hE (I.T.level n) (I'.T.level n) φ y)
    φ1 hφc ℓb hℓb (hσE n) hO hJ0 hJ0'
    (hg_gH I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal n (e n) (he n) (β n) (hβJ n)
      (hβa n) (heβ n) (hβR n) φ1 hφc ℓb hℓb (hσE n)) c

end Input

namespace Overlap

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

include hβ0 hβ0O in
/-- `yH` is compatible with the `O`-structures of the overlaps. -/
lemma yH_algebraMapO (n : ℕ) (o : O) :
    I.yH I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1 hφc ℓb hℓb
        hσE n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o) := by
  change I.yH I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1 hφc ℓb
      hℓb hσE n (algebraMap I.B0 (I.Y hθ n) (letI := V.algOB0; algebraMap O I.B0 o)) =
    algebraMap I'.B0 (I'.Y hθ n) (letI := V'.algOB0; algebraMap O I'.B0 o)
  rw [Input.yH_algebraMap I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ
    hβR φ1 hφc ℓb hℓb hσE β0 hβ0, hβ0O]

include hs heS hβ0 hg0 hpS hpB hJ0 hJ0' hpγ in
/-- **The overlap condition `hψ` of `Overlap.twoChartMap`** for `yH` and `p` (from the bottom
level, `Overlap.hψ_of_bottom`). -/
theorem hψH (n : ℕ) (z : I.Y hθ n) :
    V'.ψ hθ hO n (I.yH I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z) :=
  V.hψ_of_bottom V' hθ hO
    (I.yH I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1 hφc ℓb hℓb
      hσE)
    (fun n ↦ (Input.yH_algebraMap I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ
      hβa heβ hβR φ1 hφc ℓb hℓb hσE β0 hβ0 n V.g).trans (by rw [hg0]))
    (Input.yH_succ I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE hO hs heS)
    p hp0 hpS β0
    (Input.yH_algebraMap I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ
      hβR φ1 hφc ℓb hℓb hσE β0 hβ0)
    hpB hJ0 hJ0' φ1
    (Input.yH_yEquiv I I' hθ hR hc ha hk hF hE φ hcd hcd' hcu hcv hbal e he β hβJ hβa heβ hβR φ1
      hφc ℓb hℓb hσE hO 0 hJ0 hJ0')
    hpγ n z

/-- **The morphism of the adic systems of chart algebras of two overlaps of node-only
coverings** (`Overlap.systemMap` of `yH` and `p`). -/
def systemMapH (ϖ : O) (h : V.ϖ = ϖ) (h' : V'.ϖ = ϖ) :
    AdicChartAlgSystem.Hom (V.systemAt hθ hO ϖ h) (V'.systemAt hθ hO ϖ h') :=
  V.systemMap V' hθ hO ϖ h h'
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
    hpS

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
