/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelEquivX
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower

/-!
# The levels over `V₀` form a tower (MR12 T2 S6, G4 over `V₀`)

For identifications `e1 : X1 ≃ Y n`, `e1' : X1' ≃ Y (n+1)` commuting with maps `μ1 : X1' → X1` and
`Ymap n`, overlap identifications `ωn`, `ωn'` and maps `μ0 : X0' → X0`:

* **`NodeEtaleGlue.Overlap.qmap_φQn`**: `qmap n ∘ φQn' = φQn ∘ μ0` on an element `x` of `X0'` for
  which there is a common witness `(y, k)` of `ωn'(x/1)·x₁ᵏ = y/1` and `ωn(μ0 x/1)·x₁ᵏ = μ1 y/1`;
* **`NodeEtaleGlue.Overlap.f0_levelEquiv0X`**: the identifications `levelEquiv0X` commute with the
  successor maps `f0 n` of the covering over `V₀` (given `qmap_φQn` and the compatibility of the
  patch sides `φP` with the successor maps `sP` of the piece over `D(c₀)`).
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
  {X1' : Type u} [CommRing X1'] [Algebra I.B0 X1'] (e1' : X1' ≃ₐ[I.B0] I.Y hθ (n + 1))
  {X0' : Type u} [CommRing X0'] [Algebra V.B0' X0']
  (ωn' : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0') V.x0
    letI := awayAlg (W := V.W0) (C := X1') V.x1
    Localization.Away (algebraMap V.B0' X0' V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1' V.x1))
  (μ1 : X1' →+* X1) (μ0 : X0' →+* X0)
  (he1 : ∀ y, I.Ymap hθ hO n (e1' y) = e1 (μ1 y))

/-- `φQn` times a power of `x₁` from a witness of `ωn`. -/
lemma φQn_mul_pow (x : X0) (y : X1) (k : ℕ)
    (h : haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0) V.x0
      letI := awayAlg (W := V.W0) (C := X1) V.x1
      ωn (algebraMap X0 _ x) *
        algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1)) (algebraMap I.B0 X1 V.x1) ^ k =
        algebraMap X1 _ y) :
    V.φQn hθ n e1 ωn x * algebraMap I.B0 (V.Q hθ n) V.x1 ^ k =
      algebraMap (I.Y hθ n) (V.Q hθ n) (e1 y) := by
  have h' := congrArg (V.eQn hθ n e1) h
  rw [map_mul, map_pow, eQn_algebraMap, eQn_algebraMap, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply] at h'
  exact h'

include he1 in
/-- **The `Q`-components of the levels over `V₀` form a tower** (on an element with a common
witness of `ωn'` and `ωn`). -/
theorem qmap_φQn (x : X0') (y : X1') (k : ℕ)
    (h' : haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0') V.x0
      letI := awayAlg (W := V.W0) (C := X1') V.x1
      ωn' (algebraMap X0' _ x) *
        algebraMap X1' (Localization.Away (algebraMap I.B0 X1' V.x1))
          (algebraMap I.B0 X1' V.x1) ^ k = algebraMap X1' _ y)
    (h : haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0) V.x0
      letI := awayAlg (W := V.W0) (C := X1) V.x1
      ωn (algebraMap X0 _ (μ0 x)) *
        algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1)) (algebraMap I.B0 X1 V.x1) ^ k =
        algebraMap X1 _ (μ1 y)) :
    V.qmap hθ hO n (V.φQn hθ (n + 1) e1' ωn' x) = V.φQn hθ n e1 ωn (μ0 x) := by
  have a1 := congrArg (V.qmap hθ hO n) (V.φQn_mul_pow hθ (n + 1) e1' ωn' x y k h')
  rw [map_mul, map_pow, AlgHom.commutes, qmap_algebraMap, he1] at a1
  have a0 := V.φQn_mul_pow hθ n e1 ωn (μ0 x) (μ1 y) k h
  exact ((V.isUnit_x1_Q hθ n).pow k).mul_left_injective (a1.trans a0.symm)

variable (φP : letI := V.alg0'E n; X0 →ₐ[V.B0'] V.P0.P n)
  (ρX1 : X1 →+* I.C1) (ρX0 : X0 →+* V.C0)
  (hP : letI := V.alg0'E n; letI := φP.toRingHom.toAlgebra
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
  (φP' : letI := V.alg0'E (n + 1); X0' →ₐ[V.B0'] V.P0.P (n + 1))
  (ρX1' : X1' →+* I.C1) (ρX0' : X0' →+* V.C0)
  (hP' : letI := V.alg0'E (n + 1); letI := φP'.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X0' V.c0) (V.P0.P (n + 1)))
  {m' : ℕ} (hJ' : J θ (R := V.B' (n + 1)) ^ m' = ⊥)
  (hψ' : ∀ y, (letI := V.algBM (n + 1)
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B (n + 1))) (V.M (n + 1)))
      (V.ψ hθ hO (n + 1) (e1' y))) = V.γM (n + 1) (ρX1' y))
  (hx1' : ρX1' (algebraMap I.B0 X1' V.x1) = algebraMap I.Bs I.C1 V.x1s)
  (hω' : ∀ x : X0', ∃ (y : X1') (k : ℕ),
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0') V.x0
      letI := awayAlg (W := V.W0) (C := X1') V.x1
      ωn' (algebraMap X0' _ x) *
        algebraMap X1' (Localization.Away (algebraMap I.B0 X1' V.x1))
          (algebraMap I.B0 X1' V.x1) ^ k = algebraMap X1' _ y) ∧
    V.ω (algebraMap V.C0 _ (ρX0' x)) *
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
          (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1' y))
  (hPℓ' : ∀ x, Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' (n + 1)))
      (Loc0 (V.B' (n + 1)) (V.P0.P (n + 1)) V.x0))
    (algebraMap (V.P0.P (n + 1)) (Loc0 (V.B' (n + 1)) (V.P0.P (n + 1)) V.x0) (φP' x)) =
      V.P0.ℓ0 (n + 1) (ρX0' x))

include he1 in
/-- **The levels over `V₀` form a tower**: `f0 n ∘ levelEquiv0X' = levelEquiv0X ∘ μ0`, from the
compatibility of the `Q`-components (`qmap_φQn`, with a common witness for each element) and of
the patch sides (`hφP`). -/
theorem f0_levelEquiv0X
    (hω2 : ∀ x : X0', ∃ (y : X1') (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0') V.x0
        letI := awayAlg (W := V.W0) (C := X1') V.x1
        ωn' (algebraMap X0' _ x) *
          algebraMap X1' (Localization.Away (algebraMap I.B0 X1' V.x1))
            (algebraMap I.B0 X1' V.x1) ^ k = algebraMap X1' _ y) ∧
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ (μ0 x)) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k = algebraMap X1 _ (μ1 y)))
    (hφP : ∀ x, V.P0.sP n (φP' x) = φP (μ0 x)) (x : X0') :
    V.f0 hθ hO n (V.levelEquiv0X hθ hO (n + 1) e1' ωn' φP' ρX1' ρX0' hP' hJ' hψ' hx1' hω' hPℓ' x) =
      V.levelEquiv0X hθ hO n e1 ωn φP ρX1 ρX0 hP hJ hψ hx1 hω hPℓ (μ0 x) := by
  obtain ⟨y, k, h', h⟩ := hω2 x
  exact Subtype.ext (Prod.ext (V.qmap_φQn hθ hO n e1 ωn e1' ωn' μ1 μ0 he1 x y k h' h) (hφP x))

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
