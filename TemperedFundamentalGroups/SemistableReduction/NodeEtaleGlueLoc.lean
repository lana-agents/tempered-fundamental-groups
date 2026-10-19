/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueInput
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoLoc

/-!
# Localizations of the glued coverings over a base chart (Blueprint §12.8, M2.3 (f))

For an input `I : NodeEtaleGlue.Input` (the covering `Y n = G n ×_{E n[1/a]} E n` over the base
`B0`, pieces on `D(a0)`, `D(b0)`) and `c ∈ B0`:

* `NodeEtaleGlue.Input.ρA n`, `ρB n`: the overlap maps of the glueing over `B0`;
* **`NodeEtaleGlue.Input.isLocalization_Yloc`**: `Y n[1/c]` is the glueing of `G n[1/c]` and
  `E n[1/c]` over `E n[1/a][1/c]` (`ZariskiTwo.isLocalization_mapL`).

This is the restriction of the covering over `V₁` to the overlap with the piece over `V₀`
(Tate case: `c = h'(1 + h')`).
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

/-- The overlap map `G n → E n[1/a]` over `B0`. -/
abbrev ρA (n : ℕ) := ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
  I.hdiv I.hJB I.B0 n

/-- The localization map `E n → E n[1/a]` over `B0`. -/
abbrev ρB (n : ℕ) := ρb0 I.B I.a I.E I.B0 n

include hO in
/-- **The covering over the base chart, localized at `c ∈ B0`, is the glueing of the localized
pieces.** -/
theorem isLocalization_Yloc (n : ℕ) (c : I.B0) :
    letI := alg0G I.T hθ I.B I.B0 n
    letI := alg0 I.B I.B0 n (I.E n)
    letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
    letI := (ZariskiTwo.mapL c (ρa := I.ρA hθ n) (ρb := I.ρB n)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap I.B0 (ZariskiTwo.glued (I.ρA hθ n) (I.ρB n)) c)
      (ZariskiTwo.glued (ZariskiTwo.ρaL c (ρa := I.ρA hθ n)) (ZariskiTwo.ρbL c (ρb := I.ρB n))) :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  haveI := locFst I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv
    I.hJB I.B0 (fun _ ↦ rfl) n
  haveI := locSnd I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv
    I.hbb I.hJB I.B0 (fun _ ↦ rfl) n
  ZariskiTwo.isLocalization_mapL I.a0 I.b0 c I.hab
    (isUnit_a0 I.T hθ I.B I.a I.B0 (fun _ ↦ rfl) n)
    (isLocalization_ρb0 I.B I.a I.E I.B0 (fun _ ↦ rfl) n)
    (I.hbE n)
    (isLocalization_ρa0 I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hbb I.hJB I.B0 (fun _ ↦ rfl) n)

end Input

end NodeEtaleGlue

end

end SemistableReduction
