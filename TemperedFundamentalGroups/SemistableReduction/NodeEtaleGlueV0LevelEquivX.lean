/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelEquiv

/-!
# The level `n` over `V₀` from the levels over `V₁` and the overlap (MR12 T2 S6, G4 over `V₀`)

For an overlap datum `V : NodeEtaleGlue.Overlap I`, an identification `e1 : X1 ≃ Y n` over `V₁`,
an identification `ωn : X0[1/x₀] ≃ X1[1/x₁]` of the overlaps and a patch side `φP : X0 → P0 n`
(a localization away from `c₀`):

* **`NodeEtaleGlue.Overlap.levelEquiv0X`**: `X0 ≃ₐ[B0'] Q n ×_{M n} P0 n` (`levelEquiv0` at
  `φQn e1 ωn` and `φP`, the agreement modulo `J` from `φQn_compat'`);
* **`NodeEtaleGlue.Overlap.hω_of_mk`**: the hypothesis `hω` of `φQn_compat` from witnesses on
  generators `q0 b` of `X0`, for any map `ω'` agreeing with the special-fibre datum `ω`.
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)
  {X1 : Type u} [CommRing X1] [Algebra I.B0 X1] (e1 : X1 ≃ₐ[I.B0] I.Y hθ n)
  {X0 : Type u} [CommRing X0] [Algebra V.B0' X0]
  (ωn : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0) V.x0
    letI := awayAlg (W := V.W0) (C := X1) V.x1
    Localization.Away (algebraMap V.B0' X0 V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1 V.x1))
  (φP : letI := V.alg0'E n; X0 →ₐ[V.B0'] V.P0.P n)
  (ρX1 : X1 →+* I.C1) (ρX0 : X0 →+* V.C0)

/-- **The hypothesis `hω` of `φQn_compat` from generators**: witnesses `(y, k)` for the elements
`q0 b` of a generating family of `X0`, stated with any map `ω'` agreeing with `ω`. -/
theorem hω_of_mk {Z Z1 : Type u} (q0 : Z → X0) (hq0 : Function.Surjective q0) (q1 : Z1 → X1)
    (ω' : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) →
      Localization.Away (algebraMap I.Bs I.C1 V.x1s)) (hω' : ∀ z, V.ω z = ω' z)
    (H : ∀ b : Z, ∃ (y : Z1) (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ (q0 b)) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k =
          algebraMap X1 _ (q1 y)) ∧
      ω' (algebraMap V.C0 _ (ρX0 (q0 b))) *
          algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
            (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 (q1 y))) :
    ∀ x : X0, ∃ (y : X1) (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ x) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k =
          algebraMap X1 _ y) ∧
      V.ω (algebraMap V.C0 _ (ρX0 x)) *
          algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
            (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 y) := by
  intro x
  obtain ⟨b, rfl⟩ := hq0 x
  obtain ⟨y, k, h1, h2⟩ := H b
  exact ⟨q1 y, k, h1, (hω' _).symm ▸ h2⟩

variable (hP : letI := V.alg0'E n; letI := φP.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X0 V.c0) (V.P0.P n))
  {m : ℕ} (hJ : J θ (R := V.B' n) ^ m = ⊥)
  (hψ : ∀ y, (letI := V.algBM n; Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
    (V.ψ hθ hO n (e1 y))) = V.γM n (ρX1 y))
  (hx1 : ρX1 (algebraMap I.B0 X1 V.x1) = algebraMap I.Bs I.C1 V.x1s)
  (hω : ∀ x : X0, ∃ (y : X1) (k : ℕ),
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0) V.x0
      letI := awayAlg (W := V.W0) (C := X1) V.x1
      ωn (algebraMap X0 _ x) *
        algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1)) (algebraMap I.B0 X1 V.x1) ^ k =
        algebraMap X1 _ y) ∧
    V.ω (algebraMap V.C0 _ (ρX0 x)) *
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
          (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 y))
  (hPℓ : ∀ x, Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' n))
      (Loc0 (V.B' n) (V.P0.P n) V.x0))
    (algebraMap (V.P0.P n) (Loc0 (V.B' n) (V.P0.P n) V.x0) (φP x)) = V.P0.ℓ0 n (ρX0 x))

/-- **G4 over `V₀`: the level `n` of the covering over the second chart is `X0`**,
`X0 ≃ₐ[B0'] Q n ×_{M n} P0 n`, with components `φQn e1 ωn` and `φP`. -/
def levelEquiv0X : letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    X0 ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n) :=
  V.levelEquiv0 hθ hO n (V.φQn hθ n e1 ωn) φP (V.isLocalization_φQn hθ n e1 ωn) hP hJ
    (V.φQn_compat' hθ hO n e1 ωn φP ρX1 ρX0 hψ hx1 hω hPℓ)

lemma levelEquiv0X_fst (x : X0) :
    (V.levelEquiv0X hθ hO n e1 ωn φP ρX1 ρX0 hP hJ hψ hx1 hω hPℓ x).1.1 =
      V.φQn hθ n e1 ωn x := rfl

lemma levelEquiv0X_snd (x : X0) :
    (V.levelEquiv0X hθ hO n e1 ωn φP ρX1 ρX0 hP hJ hψ hx1 hω hPℓ x).1.2 = φP x := rfl

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
