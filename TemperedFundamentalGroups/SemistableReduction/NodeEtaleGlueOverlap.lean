/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLoc
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapGlue

/-!
# Étale algebras over an overlap with the covering over a base chart (Blueprint §12.8, M2.3 (f))

For an input `I : NodeEtaleGlue.Input` (the covering `Y n = G n ×_{E n[1/a]} E n` over the base
`B0`), `g ∈ B0` with `f n ∣ gᵏ` on the node chart (`D(g)` misses the nodes) and a formally étale
`B n`-algebra `M` with `M/JM = C1[1/ḡ]` (`γM : C1 → M/JM` a localization away from `ḡ`; an étale
algebra over `D(g)` with the special fibre of the covering):

* **`NodeEtaleGlue.Input.glueM`**: `M ≃ₐ[B0]` the glueing of the localized pieces
  `G n[1/g] ×_{E n[1/a][1/g]} E n[1/g]` (`EtaleOverlap.glueEquiv`);
* **`NodeEtaleGlue.Input.ψ`**, **`isLocalization_ψ`**: the map `Y n → M`, a localization away
  from `g` (`Input.isLocalization_Yloc`).

Tate case: `g = h'(1 + h')`, `M = E0 n[1/h₀]` (the étale piece over `D(1 + h₀) ⊆ V₀` restricted to
the overlap with `V₁`); this is the glueing datum `ρ0a` of `TwoChartGlue.Patch0`.
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
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (n : ℕ) (g : I.B0) {kg : ℕ}
  (hfg : I.T.f n ∣ algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) g) ^ kg)
  {M : Type u} [CommRing M] [Algebra (I.B n) M] [Algebra.FormallyEtale (I.B n) M]
  [Algebra I.B0 M] [IsScalarTower I.B0 (I.B n) M]
  (γM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    I.C1 →ₐ[I.B n] M ⧸ EtaleNil.JB (J θ (R := I.B n)) M)
  (hM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := γM.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) I.C1 (algebraMap I.B0 (I.B n) g))
      (M ⧸ EtaleNil.JB (J θ (R := I.B n)) M))

/-- The localization `P n[1/g]` of the étale part of the node patch. -/
abbrev Pg : Type u :=
  letI := algBP I.T I.B n
  Localization.Away (algebraMap (I.B n) (I.T.level n).P (algebraMap I.B0 (I.B n) g))


/-- The localized glueing `G n[1/g] ×_{E n[1/a][1/g]} E n[1/g]` (`Input.isLocalization_Yloc`;
a `def` with explicit instances: instance search through the glued subalgebra is slow). -/
def Yg : Type u :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  ZariskiTwo.glued (ZariskiTwo.ρaL g (ρa := I.ρA hθ n)) (ZariskiTwo.ρbL g (ρb := I.ρB n))

instance : CommRing (I.Yg hθ n g) :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  (ZariskiTwo.glued (ZariskiTwo.ρaL g (ρa := I.ρA hθ n))
    (ZariskiTwo.ρbL g (ρb := I.ρB n))).toCommRing

instance : Algebra I.B0 (I.Yg hθ n g) :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  (ZariskiTwo.glued (ZariskiTwo.ρaL g (ρa := I.ρA hθ n)) (ZariskiTwo.ρbL g (ρb := I.ρB n))).algebra

lemma isLocalization_LcG : letI := alg0G I.T hθ I.B I.B0 n; letI := algBG I.T hθ I.B n
    IsLocalization.Away (algebraMap (I.B n) (I.T.G hθ n) (algebraMap I.B0 (I.B n) g))
      (ZariskiTwo.Lc g (I.T.G hθ n)) :=
  letI := alg0G I.T hθ I.B I.B0 n
  Localization.isLocalization

lemma tower_LcG : letI := alg0G I.T hθ I.B I.B0 n; letI := algBG I.T hθ I.B n
    IsScalarTower I.B0 (I.B n) (ZariskiTwo.Lc g (I.T.G hθ n)) :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := algBG I.T hθ I.B n
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma tower_LcE : letI := alg0 I.B I.B0 n (I.E n)
    IsScalarTower I.B0 (I.B n) (ZariskiTwo.Lc g (I.E n)) :=
  letI := alg0 I.B I.B0 n (I.E n)
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma fstL : letI := alg0G I.T hθ I.B I.B0 n
    letI := alg0 I.B I.B0 n (I.E n)
    letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
    IsLocalizedModule (Submonoid.powers I.a0) (ZariskiTwo.fst (ZariskiTwo.ρaL g (ρa := I.ρA hθ n))
      (ZariskiTwo.ρbL g (ρb := I.ρB n))).toLinearMap :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  ZariskiTwo.isLocalizedModule_fstL I.a0 g (ρa := I.ρA hθ n) (ρb := I.ρB n)
    (isUnit_a0 I.T hθ I.B I.a I.B0 (fun _ ↦ rfl) n)
    (isLocalization_ρb0 I.B I.a I.E I.B0 (fun _ ↦ rfl) n)

include hO in
lemma sndL : letI := alg0G I.T hθ I.B I.B0 n
    letI := alg0 I.B I.B0 n (I.E n)
    letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
    IsLocalizedModule (Submonoid.powers I.b0) (ZariskiTwo.snd (ZariskiTwo.ρaL g (ρa := I.ρA hθ n))
      (ZariskiTwo.ρbL g (ρb := I.ρB n))).toLinearMap :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  ZariskiTwo.isLocalizedModule_sndL I.b0 g (ρa := I.ρA hθ n) (ρb := I.ρB n)
    (I.hbE n)
    (isLocalization_ρa0 I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hbb I.hJB I.B0 (fun _ ↦ rfl) n)

include hO hfg in
/-- **An étale algebra over `D(g)` with the special fibre `C1[1/ḡ]` is the localized glueing.** -/
def glueM : M ≃ₐ[I.B0] I.Yg hθ n g := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBC I.T I.B n
  haveI := towerBC I.T I.B n
  letI := algBG I.T hθ I.B n
  haveI := towerBG I.T hθ I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  haveI := isLocalization_C1 I.B I.qB I.C1 I.b I.hbb n
  haveI : IsLocalization.Away (algebraMap (I.B n) (I.E n) (algebraMap I.B0 (I.B n) g))
      (ZariskiTwo.Lc g (I.E n)) := Localization.isLocalization
  haveI : IsLocalization.Away (algebraMap (I.B n) (EtaleOverlap.Bab (I.a n) (I.E n))
      (algebraMap I.B0 (I.B n) g)) (ZariskiTwo.Lc g (EtaleOverlap.Bab (I.a n) (I.E n))) :=
    Localization.isLocalization
  haveI := I.isLocalization_LcG hθ n g
  haveI := I.tower_LcE n g
  haveI := I.tower_LcG hθ n g
  haveI := I.fstL hθ n g
  haveI := I.sndL hθ hO n g
  exact EtaleOverlap.glueEquiv (J θ (R := I.B n)) (I.hJB n) (I.a n) (I.b n) (A := I.R n)
    (P := (I.T.level n).P) (E := I.E n) (C1 := I.C1) (Cc := Cc I.T n) (B0 := I.B0)
    (G := I.T.G hθ n) (Gg := ZariskiTwo.Lc g (I.T.G hθ n)) (Eg := ZariskiTwo.Lc g (I.E n))
    (Babg := ZariskiTwo.Lc g (EtaleOverlap.Bab (I.a n) (I.E n))) (M := M)
    (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n) (I.T.f n) (σPn I.T I.B n)
    (I.σE n) (isLocalization_ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.ha I.hι n) (I.hbE n)
    (I.hdiv n) (algebraMap I.B0 (I.B n) g) (Pg := I.Pg n g) I.a0 I.b0 I.hab rfl rfl
    (fstP I.T hθ n) (isLocalization_fstP I.T hθ hO n) hfg γM hM
    (ZariskiTwo.ρaL g (ρa := I.ρA hθ n)) (ZariskiTwo.ρbL g (ρb := I.ρB n))
    (fun x ↦ ZariskiTwo.pieceL_algebraMap g (I.ρA hθ n) _ _ x)
    (fun x ↦ ZariskiTwo.pieceL_algebraMap g (I.ρB n) _ _ x)

/-- The map `Y n → Y n[1/g]` (`ZariskiTwo.mapL`). -/
def mapYg : I.Y hθ n →ₐ[I.B0] I.Yg hθ n g := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  exact ZariskiTwo.mapL g (ρa := I.ρA hθ n) (ρb := I.ρB n)

include hO in
lemma isLocalization_mapYg : letI := (I.mapYg hθ n g).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap I.B0 (I.Y hθ n) g) (I.Yg hθ n g) :=
  I.isLocalization_Yloc hθ hO n g

/-- **The map `Y n → M`** of the covering over the base chart to the étale algebra over `D(g)`. -/
def ψ : I.Y hθ n →ₐ[I.B0] M :=
  (I.glueM hθ hO n g hfg γM hM).symm.toAlgHom.comp (I.mapYg hθ n g)

/-- **`M = Y n[1/g]`.** -/
theorem isLocalization_ψ : letI := (I.ψ hθ hO n g hfg γM hM).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap I.B0 (I.Y hθ n) g) M :=
  RingHomAway.equiv _ (I.glueM hθ hO n g hfg γM hM).symm.toRingEquiv _
    (I.isLocalization_mapYg hθ hO n g)

end Input

end NodeEtaleGlue

end

end SemistableReduction
