/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateOmegaNorm

/-!
# Witnesses of the overlap datum `omegaNormC` (MR12 T2 S6, G4 over `V₀`)

* `NormOverlap.awayCongr_algebraMap`, `NormOverlap.awayCongr_symm_algebraMap`: `awayCongr s e`
  maps `c/1` to `e c/1`;
* **`TateGlue0.omegaNormC_mul_pow`**: a witness `ω(b/1)·h̄'ᵏ = y/1` of `omegaNorm` gives the witness
  `ω(b/1)·h̄'ᵏ = e⁻¹(y)/1` of the overlap datum `omegaNormC e` (whose target is `Sp.C1[1/h̄']`).
-/

universe u

namespace SemistableReduction

namespace NormOverlap

/-- `awayCongr s e` maps `c/1` to `e c/1`. -/
lemma awayCongr_algebraMap {S Ws C C' : Type u} [CommRing S] [CommRing Ws] [CommRing C]
    [CommRing C'] [Algebra S Ws] [Algebra S C] [Algebra S C'] (s : S) [IsLocalization.Away s Ws]
    (e : C ≃ₐ[S] C') (c : C) :
    letI := AwayAlg.alg (W := Ws) (C := C) s; letI := AwayAlg.alg (W := Ws) (C := C') s
    awayCongr (Ws := Ws) s e (algebraMap C _ c) = algebraMap C' _ (e c) := by
  letI := AwayAlg.alg (W := Ws) (C := C) s
  letI := AwayAlg.alg (W := Ws) (C := C') s
  change (IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (algebraMap S C s))
    (T := Submonoid.powers (algebraMap S C' s)) (Localization.Away (algebraMap S C s))
    (Localization.Away (algebraMap S C' s)) e.toRingEquiv (by
      rw [Submonoid.map_powers]
      congr 1
      exact e.commutes s)) (algebraMap C _ c) = _
  exact IsLocalization.ringEquivOfRingEquiv_eq _ c

/-- `(awayCongr s e)⁻¹` maps `c/1` to `e⁻¹ c/1`. -/
lemma awayCongr_symm_algebraMap {S Ws C C' : Type u} [CommRing S] [CommRing Ws] [CommRing C]
    [CommRing C'] [Algebra S Ws] [Algebra S C] [Algebra S C'] (s : S) [IsLocalization.Away s Ws]
    (e : C ≃ₐ[S] C') (c : C') :
    letI := AwayAlg.alg (W := Ws) (C := C) s; letI := AwayAlg.alg (W := Ws) (C := C') s
    (awayCongr (Ws := Ws) s e).symm (algebraMap C' _ c) = algebraMap C _ (e.symm c) := by
  letI := AwayAlg.alg (W := Ws) (C := C) s
  letI := AwayAlg.alg (W := Ws) (C := C') s
  rw [AlgEquiv.symm_apply_eq, awayCongr_algebraMap, AlgEquiv.apply_symm_apply]

end NormOverlap

namespace TateGlue0

noncomputable section

open TateTwoChart TateLevel TateTwoChartNode KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀)
  {L : Type*} [Field L] [Algebra (T0 π b₄ t κ) L] [Algebra (T1 π b₄ t κ) L]
  [Algebra (T01 π b₄ t κ) L] [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
  {B₀ B₁ : Type u} [CommRing B₀] [CommRing B₁]
  [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower (T0 π b₄ t κ) B₀ L]
  [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
  [Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower (T1 π b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 π b₄ t κ) L]

attribute [local irreducible] omegaNorm NormOverlap.omegaEquiv

/-- **A witness of `omegaNorm` is a witness of `omegaNormC e`**: if `ω(b/1)·h̄'ᵏ = y/1` for the
datum `omegaNorm` (target `(B₁/J)[1/h̄']`), then `ω(b/1)·h̄'ᵏ = e⁻¹(y)/1` for `omegaNormC e`
(target `Sp.C1[1/h̄']`). -/
theorem omegaNormC_mul_pow
    (e : Sp.C1 ≃ₐ[TateGlue1.T1s θ π b₄ t κ] FormalKummer.Cs θ (T1 π b₄ t κ) B₁)
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (h₀ : algebraMap (T0 π b₄ t κ) L (h0 π b₄ t κ) ≠ 0)
    (h₁ : algebraMap (T1 π b₄ t κ) L (h1 π b₄ t κ) ≠ 0)
    (b : FormalKummer.Cs θ (T0 π b₄ t κ) B₀) (y : FormalKummer.Cs θ (T1 π b₄ t κ) B₁) (k : ℕ)
    (h : omegaNorm θ (B₀ := B₀) (B₁ := B₁) hρ h₀ h₁
        (algebraMap (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) _ b) *
        algebraMap (FormalKummer.Cs θ (T1 π b₄ t κ) B₁)
          (Localization.Away (algebraMap (EtaleTower.Ts θ (T1 π b₄ t κ))
            (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) (Ideal.Quotient.mk _ (h1 π b₄ t κ))))
          (algebraMap (EtaleTower.Ts θ (T1 π b₄ t κ)) (FormalKummer.Cs θ (T1 π b₄ t κ) B₁)
            (Ideal.Quotient.mk _ (h1 π b₄ t κ))) ^ k =
      algebraMap (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) _ y) :
    letI := algC0x (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) (θ := θ) (π := π) (b₄ := b₄) (t := t)
      (κ := κ)
    letI := algC1x Sp.C1 (θ := θ) (π := π) (b₄ := b₄) (t := t) (κ := κ)
    omegaNormC hκ hπ Sp (B₀ := B₀) e hρ h₀ h₁
        (algebraMap (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) _ b) *
        algebraMap Sp.C1 (Localization.Away (algebraMap (TateGlue1.T1s θ π b₄ t κ) Sp.C1
          (Ideal.Quotient.mk _ (h1 π b₄ t κ))))
          (algebraMap (TateGlue1.T1s θ π b₄ t κ) Sp.C1 (Ideal.Quotient.mk _ (h1 π b₄ t κ))) ^ k =
      algebraMap Sp.C1 _ (e.symm y) := by
  letI := alg1s θ π b₄ t κ
  haveI := isLocalization_alg1s θ π b₄ t κ
  letI := algC1x Sp.C1 (θ := θ) (π := π) (b₄ := b₄) (t := t) (κ := κ)
  letI := algC1x (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) (θ := θ) (π := π) (b₄ := b₄) (t := t)
    (κ := κ)
  let F := (NormOverlap.awayCongr (Ws := T01s θ π b₄ t κ)
    (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)) e).symm
  have hA : F (algebraMap (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) _
      (algebraMap (EtaleTower.Ts θ (T1 π b₄ t κ)) (FormalKummer.Cs θ (T1 π b₄ t κ) B₁)
        (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)))) =
      algebraMap Sp.C1 _ (algebraMap (TateGlue1.T1s θ π b₄ t κ) Sp.C1
        (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ))) :=
    (NormOverlap.awayCongr_symm_algebraMap (Ws := T01s θ π b₄ t κ)
      (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)) e _).trans
      (congrArg _ (e.symm.commutes _))
  have hy : F (algebraMap (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) _ y) =
      algebraMap Sp.C1 _ (e.symm y) :=
    NormOverlap.awayCongr_symm_algebraMap (Ws := T01s θ π b₄ t κ)
      (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)) e y
  have e1 := (map_mul F _ _).trans
    (congrArg (F (omegaNorm θ (B₀ := B₀) (B₁ := B₁) hρ h₀ h₁
      (algebraMap (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) _ b)) * ·)
      ((map_pow F _ k).trans (congrArg (· ^ k) hA)))
  exact e1.symm.trans ((congrArg F h).trans hy)

end

end TateGlue0

end SemistableReduction
