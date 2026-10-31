/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Levels
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoLoc

/-!
# The level `n` of the covering over the second chart (MR12 T2 S6, G4 over `V₀`)

For an overlap datum `V : NodeEtaleGlue.Overlap I`, the ring `R0 n` of the covering over the
second chart at level `n` is the Zariski glueing `Q n ×_{M n} P0 n` (`Overlap.ρ0a`, `Overlap.ρ0b`)
on `V₀ = D(x₀) ∪ D(c₀)`.

* `NodeEtaleGlue.Overlap.eQn`, **`NodeEtaleGlue.Overlap.φQn`** (`X0 → X0[1/x₀] ≃ X1[1/x₁] ≃ Q n` for
  `e1 : X1 ≃ Y n` and an overlap identification `ωn`), `isLocalization_φQn`;
* **`NodeEtaleGlue.Overlap.levelEquiv0`**: a `B0'`-algebra `X` with maps `φQ : X → Q n`,
  `φP : X → P0 n` which are localizations away from `x₀` and `c₀` and agree modulo `J` in `M n`
  (where `J` is nilpotent on `B' n`) is `≃ₐ[B0'] Q n ×_{M n} P0 n`
  (`Overlap.ρ0a_φQ` + `ZariskiTwo.liftEquiv`), with components `φQ`, `φP` (`rfl`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace NodeEtaleGlue

section Away

variable {S W C : Type u} [CommRing S] [CommRing W] [CommRing C] [Algebra S W] [Algebra S C]
  (s : S) [IsLocalization.Away s W]

/-- `C[1/s]` as an algebra over `W = S[1/s]` (as `AwayAlg.alg`). -/
@[reducible] def awayAlg : Algebra W (Localization.Away (algebraMap S C s)) :=
  (IsLocalization.Away.map W (Localization.Away (algebraMap S C s)) (algebraMap S C) s).toAlgebra

lemma awayAlg_tower : letI := awayAlg (C := C) (W := W) s
    IsScalarTower S W (Localization.Away (algebraMap S C s)) :=
  letI := awayAlg (C := C) (W := W) s
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = IsLocalization.Away.map W _ (algebraMap S C) s (algebraMap S W x)
    rw [IsLocalization.Away.map, IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]

end Away

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)
  {X : Type u} [CommRing X] [Algebra V.B0' X]
  (φQ : letI := V.alg0'Q hθ n; X →ₐ[V.B0'] V.Q hθ n)
  (φP : letI := V.alg0'E n; X →ₐ[V.B0'] V.P0.P n)
  (hQ : letI := V.alg0'Q hθ n; letI := φQ.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X V.x0) (V.Q hθ n))
  (hP : letI := V.alg0'E n; letI := φP.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X V.c0) (V.P0.P n))
  {m : ℕ} (hJ : J θ (R := V.B' n) ^ m = ⊥)
  (h : ∀ x, Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' n)) (V.M n))
      (V.ρ0a hθ hO n (φQ x)) = Ideal.Quotient.mk _ (V.ρ0b n (φP x)))

/-- **The level `n` of the covering over `V₀`**: `X ≃ₐ[B0'] Q n ×_{M n} P0 n` for
localizations `φQ`, `φP` away from `x₀`, `c₀` agreeing modulo `J` in `M n`. -/
def levelEquiv0 : letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    X ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n) :=
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  haveI := V.fstLM hθ hO n
  haveI := V.sndLM hθ hO n
  haveI := ZariskiTwo.isLocalizedModule_of_away V.x0 φQ hQ
  haveI := ZariskiTwo.isLocalizedModule_of_away V.c0 φP hP
  ZariskiTwo.liftEquiv V.x0 V.c0 V.hxc φQ φP (V.ρ0a_φQ hθ hO n φQ φP hP hJ h)

lemma levelEquiv0_fst (x : X) :
    (V.levelEquiv0 hθ hO n φQ φP hQ hP hJ h x).1.1 = φQ x := rfl

lemma levelEquiv0_snd (x : X) :
    (V.levelEquiv0 hθ hO n φQ φP hQ hP hJ h x).1.2 = φP x := rfl

section Q

variable {X1 : Type u} [CommRing X1] [Algebra I.B0 X1] (e1 : X1 ≃ₐ[I.B0] I.Y hθ n)

/-- **`X1[1/x₁] ≃ Q n = Y n[1/x₁]`**, the localization of an identification `e1 : X1 ≃ Y n`. -/
def eQn : Localization.Away (algebraMap I.B0 X1 V.x1) ≃+* V.Q hθ n :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (algebraMap I.B0 X1 V.x1))
    (T := Submonoid.powers (algebraMap I.B0 (I.Y hθ n) V.x1)) _ _ e1.toRingEquiv (by
      rw [Submonoid.map_powers]
      congr 1
      exact e1.commutes V.x1)

lemma eQn_algebraMap (x : X1) :
    V.eQn hθ n e1 (algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1)) x) =
      algebraMap (I.Y hθ n) (V.Q hθ n) (e1 x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ _

lemma eQn_W0 (w : V.W0) :
    (haveI := V.hW0; letI := awayAlg (W := V.W0) (C := X1) V.x1
      V.eQn hθ n e1 (algebraMap V.W0 (Localization.Away (algebraMap I.B0 X1 V.x1)) w)) =
      (letI := V.algW0Q hθ n; algebraMap V.W0 (V.Q hθ n) w) := by
  haveI := V.hW0
  letI := awayAlg (W := V.W0) (C := X1) V.x1
  haveI := awayAlg_tower (W := V.W0) (C := X1) V.x1
  letI := V.algW0Q hθ n
  have h : (V.eQn hθ n e1).toRingHom.comp
      (algebraMap V.W0 (Localization.Away (algebraMap I.B0 X1 V.x1))) =
      algebraMap V.W0 (V.Q hθ n) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers V.x1) (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply I.B0 X1 (Localization.Away (algebraMap I.B0 X1 V.x1)),
      eQn_algebraMap, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
      V.algW0Q_algebraMap hθ n]
  exact RingHom.congr_fun h w

variable {X0 : Type u} [CommRing X0] [Algebra V.B0' X0]
  (ωn : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0) V.x0
    letI := awayAlg (W := V.W0) (C := X1) V.x1
    Localization.Away (algebraMap V.B0' X0 V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1 V.x1))

/-- **`X0 → X0[1/x₀] ≃ X1[1/x₁] ≃ Q n`** (the first component of the level `n` over `V₀`). -/
def φQn : letI := V.alg0'Q hθ n; X0 →ₐ[V.B0'] V.Q hθ n :=
  letI := V.alg0'Q hθ n
  haveI := V.hW0
  haveI := V.hW0'
  letI := awayAlg (W := V.W0) (C := X0) V.x0
  letI := awayAlg (W := V.W0) (C := X1) V.x1
  { (V.eQn hθ n e1).toRingHom.comp (ωn.toRingEquiv.toRingHom.comp
      (algebraMap X0 (Localization.Away (algebraMap V.B0' X0 V.x0)))) with
    commutes' := fun y ↦ by
      haveI := awayAlg_tower (W := V.W0) (C := X0) V.x0
      letI := V.algW0Q hθ n
      change V.eQn hθ n e1 (ωn (algebraMap X0 _ (algebraMap V.B0' X0 y))) =
        algebraMap V.W0 (V.Q hθ n) (algebraMap V.B0' V.W0 y)
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply V.B0' V.W0 (Localization.Away (algebraMap V.B0' X0 V.x0)),
        AlgEquiv.commutes, eQn_W0] }

lemma φQn_apply (x : X0) : V.φQn hθ n e1 ωn x =
    haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0) V.x0
    letI := awayAlg (W := V.W0) (C := X1) V.x1
    V.eQn hθ n e1 (ωn (algebraMap X0 (Localization.Away (algebraMap V.B0' X0 V.x0)) x)) := rfl

/-- `φQn` is a localization away from `x₀`. -/
lemma isLocalization_φQn : letI := V.alg0'Q hθ n; letI := (V.φQn hθ n e1 ωn).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X0 V.x0) (V.Q hθ n) := by
  letI := V.alg0'Q hθ n
  letI := (V.φQn hθ n e1 ωn).toRingHom.toAlgebra
  haveI := V.hW0
  haveI := V.hW0'
  letI := awayAlg (W := V.W0) (C := X0) V.x0
  letI := awayAlg (W := V.W0) (C := X1) V.x1
  have e : Localization.Away (algebraMap V.B0' X0 V.x0) ≃ₐ[X0] V.Q hθ n :=
    AlgEquiv.ofRingEquiv (f := ωn.toRingEquiv.trans (V.eQn hθ n e1)) fun _ ↦ rfl
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap V.B0' X0 V.x0)) e

end Q

section Compat

variable {X1 : Type u} [CommRing X1] [Algebra I.B0 X1] (e1 : X1 ≃ₐ[I.B0] I.Y hθ n)
  {X0 : Type u} [CommRing X0] [Algebra V.B0' X0]
  (ωn : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0) V.x0
    letI := awayAlg (W := V.W0) (C := X1) V.x1
    Localization.Away (algebraMap V.B0' X0 V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1 V.x1))
  (φP : letI := V.alg0'E n; X0 →ₐ[V.B0'] V.P0.P n)
  (ρX1 : X1 →+* I.C1) (ρX0 : X0 →+* V.C0)
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

set_option maxHeartbeats 1000000 in
-- unfolding `ρ0a`, `φQn` and `ℓ1`
include hψ hx1 hω hPℓ in
/-- **The two components of the level `n` over `V₀` agree modulo `J` on the overlap**: the
reduction of `X0 → Q n → M n` is computed through `ωn`, its reduction `ω`, the special fibre
`γM` of `ψ` (hypothesis `hψ`, from `Input.mk_ψ`) and `ℓ1 = ℓx ∘ ω⁻¹`; that of `X0 → P0 n → M n`
is `ℓ0` (hypothesis `hPℓ`, e.g. from `PatchInput.mk_Loc`). -/
theorem φQn_compat (x : X0) : letI := V.algBM n
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
      (V.ρ0a hθ hO n (V.φQn hθ n e1 ωn x)) =
    Ideal.Quotient.mk _ (V.ρ0b n (φP x)) := by
  letI := V.algBM n
  haveI := V.hW0
  haveI := V.hW0'
  letI := awayAlg (W := V.W0) (C := X0) V.x0
  letI := awayAlg (W := V.W0) (C := X1) V.x1
  obtain ⟨y, k, h1, h2⟩ := hω x
  let f : Localization.Away (algebraMap I.B0 X1 V.x1) →+*
      V.M n ⧸ EtaleNil.JB (J θ (R := I.B n)) (V.M n) :=
    (Ideal.Quotient.mk _).comp ((V.ρ0aR hθ hO n).comp (V.eQn hθ n e1).toRingHom)
  have hf : ∀ z : X1, f (algebraMap X1 _ z) = V.γM n (ρX1 z) := fun z ↦ by
    change Ideal.Quotient.mk _ (V.ρ0aR hθ hO n (V.eQn hθ n e1 (algebraMap X1 _ z))) = _
    rw [eQn_algebraMap, ρ0aR_algebraMap]
    exact hψ z
  let G : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      V.M n ⧸ EtaleNil.JB (J θ (R := I.B n)) (V.M n) :=
    (Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
        (V.hWn0 n) (V.P0.P n) (Bn := I.B n))).toRingHom.comp
      (OverlapPiece.ℓ1 (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.P0.P n) V.x1s V.x0s
        V.c0s V.ω (V.P0.ℓ0 n) (V.P0.hℓ0loc n))
  have hG : ∀ c, G (algebraMap I.C1 _ c) = V.γM n c := fun _ ↦ rfl
  have hL : f (ωn (algebraMap X0 _ x)) * f (algebraMap X1 _ (algebraMap I.B0 X1 V.x1)) ^ k =
      f (algebraMap X1 _ y) := by
    rw [← map_pow, ← map_mul, h1]
  have hR : G (V.ω (algebraMap V.C0 _ (ρX0 x))) *
      G (algebraMap I.C1 _ (algebraMap I.Bs I.C1 V.x1s)) ^ k = G (algebraMap I.C1 _ (ρX1 y)) := by
    rw [← map_pow, ← map_mul, h2]
  have hu : IsUnit (f (algebraMap X1 _ (algebraMap I.B0 X1 V.x1))) :=
    (IsLocalization.Away.algebraMap_isUnit _).map f
  rw [hf, hf, hx1] at hL
  rw [hf, hx1] at hu
  rw [hG, hG] at hR
  have key : f (ωn (algebraMap X0 _ x)) = G (V.ω (algebraMap V.C0 _ (ρX0 x))) :=
    (hu.pow k).mul_left_injective (hL.trans hR.symm)
  change f (ωn (algebraMap X0 _ x)) = Ideal.Quotient.mk _ (algebraMap (V.P0.P n) (V.M n) (φP x))
  rw [key]
  have e : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
      (algebraMap (V.P0.P n) (V.M n) (φP x)) =
      Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
          (V.hWn0 n) (V.P0.P n) (Bn := I.B n))
        (Ideal.Quotient.mk _ (algebraMap (V.P0.P n) (V.M n) (φP x))) := rfl
  rw [e, hPℓ x]
  change Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
      (V.hWn0 n) (V.P0.P n) (Bn := I.B n))
    (OverlapPiece.ℓx (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
    (V.P0.P n) V.x0s V.c0s (V.P0.ℓ0 n) (V.P0.hℓ0loc n)
      (V.ω.symm (V.ω (algebraMap V.C0 _ (ρX0 x))))) = _
  rw [AlgEquiv.symm_apply_apply, OverlapPiece.ℓx_algebraMap]

include hψ hx1 hω hPℓ in
/-- `φQn_compat` modulo `J` of the second chart (the form of the hypothesis of `levelEquiv0`). -/
theorem φQn_compat' (x : X0) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' n)) (V.M n))
      (V.ρ0a hθ hO n (V.φQn hθ n e1 ωn x)) = Ideal.Quotient.mk _ (V.ρ0b n (φP x)) := by
  have h := Ideal.Quotient.eq.1 (V.φQn_compat hθ hO n e1 ωn φP ρX1 ρX0 hψ hx1 hω hPℓ x)
  rw [← OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n)
    (V.P0.P n) (Bn := I.B n)] at h
  exact Ideal.Quotient.eq.2 h

end Compat

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
