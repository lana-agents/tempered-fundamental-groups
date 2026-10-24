/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0SpecialR0
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Patch

/-!
# The bottom level of a patched piece (Blueprint §12.8, M2.5 (b))

For a tower of patched algebras over `D(c₀) ⊆ V₀` (`NodeEtaleGlue.PatchInput`, coverings with
cusp factors), at a level with `J = 0` on the charts `R n = B' n[1/c₀]`:

* **`NodeEtaleGlue.PatchInput.bottom`**: the bottom identification `(D.piece).Bottom n` of the
  piece: `C0 → cov₀.C ≃ G n` (`LevelTower.Level.cEquiv`: the node/cusp patch is the given
  covering `cov₀` at a level with `J = 0`), a localization away from `c̄₀` (`hι`), compatible with
  `ℓ0` (`FormalPatchLevel.mk_toP`, `PatchInput.e_algebraMap`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace PatchInput

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ} (hJ0 : J θ (R := D.R n) = ⊥)

/-- `C0 → cov₀.C ≃ G n` at a level with `J = 0`. -/
def toG : C0 →+* D.G hθ n :=
  ((D.T.level n).cEquiv hθ hO hJ0).toRingHom.comp D.ι₀

lemma toG_algebraMap (y : B' n) :
    D.toG hθ hO hJ0 (algebraMap Bs' C0 (qB' n y)) = algebraMap (B' n) (D.G hθ n) y := by
  change (D.T.level n).cEquiv hθ hO hJ0 (D.ι₀ (algebraMap Bs' C0 (qB' n y))) = _
  rw [D.ι₀_alg n y]
  exact ((D.T.level n).cEquiv hθ hO hJ0).commutes _

lemma isLocalization_toG : letI := (D.toG hθ hO hJ0).toAlgebra
    IsLocalization.Away (algebraMap Bs' C0 c0s) (D.G hθ n) := by
  letI := (D.toG hθ hO hJ0).toAlgebra
  letI : Algebra C0 cov₀.C := D.ι₀.toAlgebra
  haveI := D.hι
  have e : cov₀.C ≃ₐ[C0] D.G hθ n := AlgEquiv.ofRingEquiv
    (f := ((D.T.level n).cEquiv hθ hO hJ0).toRingEquiv) fun _ ↦ rfl
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap Bs' C0 c0s)) e

variable [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)] [∀ n, IsScalarTower O (B' (n + 1)) (B' n)]

/-- **The bottom identification of a patched piece** (`J = 0` on `R n`). -/
def bottom : (D.piece hθ hO).Bottom n where
  toP := D.toG hθ hO hJ0
  hP := D.toG_algebraMap hθ hO hJ0
  hloc := D.isLocalization_toG hθ hO hJ0
  hℓ := fun c ↦ by
    change _ = D.qe hθ hO n (D.ℓ0' n c)
    have h1 : D.ℓ0' n c = Ideal.Quotient.mk _ (D.φ hθ n (D.toG hθ hO hJ0 c)) := by
      change EtaleNil.red (J θ (R := D.R n)) (IsScalarTower.toAlgHom (D.R n) (D.P n) (D.Mp n))
        ((D.T.level n).σP.symm (algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c))) = _
      rw [← FormalPatchLevel.mk_toP hJ0 (D.T.f n) (D.T.level n).σP (D.ι₀ c),
        AlgEquiv.symm_apply_apply, EtaleNil.red_mk]
      rfl
    rw [h1, qe, Ideal.quotientEquiv_mk]
    refine congrArg _ ?_
    letI := D.algGM hθ n
    change _ = (D.e hθ hO n).symm (D.φ hθ n _)
    rw [← D.e_algebraMap hθ hO n, AlgEquiv.symm_apply_apply]
    rfl

end PatchInput

end NodeEtaleGlue

end

end SemistableReduction
