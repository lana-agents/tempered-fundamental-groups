/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS5
import TemperedFundamentalGroups.SemistableReduction.TateV1Level
import TemperedFundamentalGroups.SemistableReduction.NormOverlapLevel

/-!
# The overlap identification of the normalisations at the levels (MR12 T2 S6, G4 over `V₀`)

For the tame cover `L` of the Tate curve (data of `TateS5`) with normalisations `B₀`, `B₁` of the
charts `T0`, `T1`:

* **`TateS6.omegaN`**: `(B₀/ϖⁿ⁺¹)[1/h] ≃ₐ[T01] (B₁/ϖⁿ⁺¹)[1/h']` (`NormOverlap.omegaEquivW` at
  `I = ϖⁿ⁺¹`), the identification `ωn` of `NodeEtaleGlue.Overlap.φQn`;
* **`TateS6.omega_witness`**: for `b ∈ B₀` there are `y ∈ B₁`, `k` with `ωn(b̄/1)·h'ᵏ = ȳ/1` and
  `ω(b̄/1)·h̄'ᵏ = ȳ/1` for the special-fibre identification `ω = omegaNorm` (the hypothesis `hω` of
  `Overlap.φQn_compat`; `TateS5.om` is `omegaNorm` up to `NormOverlap.awayCongr_refl_symm_apply`).
-/

universe u
open Module Polynomial
namespace SemistableReduction

namespace TateS6
open TateS5 TateTwoChart TateTwoChartNode TateGlue0 TateLevel
open TensorProduct
open AdmissibleLift (J)
open FormalKummer (Cs)
noncomputable section
section Data

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsAlgClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m]


variable (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
  (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) (hb₆ : IsUnit b₆)
  {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t
      κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) = algebraMap (T1 (ε * ϖ ^ m) b₄ t
      κ) K x)
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ M') {ζe : K} (hζe : IsPrimitiveRoot ζe e)
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (hL : (finrank K L).Coprime q) (hd : finrank K L ∣ e)
  [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (NR b₄
      b₆ ϖ m ε) L] [IsScalarTower (NR b₄ b₆ ϖ m ε) K L]
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (T0 (ε
      * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) L]
  [Algebra (T01 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t
      κ) L]
  (hρ : ∀ x, algebraMap (T01 (ε * ϖ ^ m) b₄ t κ) L (rho0 (ε * ϖ ^ m) b₄ t κ x) = algebraMap (T0 (ε
      * ϖ ^ m) b₄ t κ) L x)
  (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L]
  (Bn : Type u) [CommRing Bn] [Algebra (NR b₄ b₆ ϖ m ε) Bn] [Algebra Bn L] [IsScalarTower (NR b₄ b₆
      ϖ m ε) Bn L]
  [Algebra B₁ Bn] [IsScalarTower B₁ Bn L]
  [IsLocalization.Away (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ (DT (ε * ϖ ^ m) b₄ t κ)) Bn]
  (hBn : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) Bn (toNode b₄ hκ rfl x) = algebraMap B₁ Bn (algebraMap
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁ x))
  (B₀ : Type u) [CommRing B₀] [Algebra (T0 (ε * ϖ ^ m) b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower
      (T0 (ε * ϖ ^ m) b₄ t κ) B₀ L]
  [IsIntegralClosure B₀ (T0 (ε * ϖ ^ m) b₄ t κ) L]
  (Bc : Type u) [CommRing Bc] [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) Bc] [Algebra Bc L] [IsScalarTower
      (RcT (ε * ϖ ^ m) b₄ t κ) Bc L]
  [Algebra B₀ Bc] [IsScalarTower B₀ Bc L]
  [IsLocalization.Away (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)) Bc]
  (hBc : ∀ x, algebraMap (RcT (ε * ϖ ^ m) b₄ t κ) Bc (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε *
      ϖ ^ m) b₄ t κ) x) = algebraMap B₀ Bc (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ x))
  (hunr₁ : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T1 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
    Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁) < P → Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄
      t κ) Q)
  (hunr₀ : ∀ (P : Ideal (T0 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T0 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₀) [Q.IsPrime],
    Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀) < P →
      Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀) ≠
        Ideal.span {h0 (ε * ϖ ^ m) b₄ t κ, z0 (ε * ϖ ^ m) b₄ t κ} →
      Algebra.IsUnramifiedAt (T0 (ε * ϖ ^ m) b₄ t κ) Q)
  (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (h0 (ε * ϖ ^ m) b₄ t
        κ))))




variable {K L B₁ Bn B₀ Bc}

local notation "𝒯" => T1 (ε * ϖ ^ m) b₄ t κ

local notation "𝒩" => NR b₄ b₆ ϖ m ε


local notation "𝓢c" => sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "𝓢p" => sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝒯0" => T0 (ε * ϖ ^ m) b₄ t κ

local notation "𝒲" => T01 (ε * ϖ ^ m) b₄ t κ

/-- **The overlap identification at level `n`**: `(B₀/ϖⁿ⁺¹)[1/h] ≃ₐ[T01] (B₁/ϖⁿ⁺¹)[1/h']`
(`NormOverlap.omegaEquivW` at `I = ϖⁿ⁺¹`). -/
def omegaN (n : ℕ) :
    letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
    haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ
    letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯0 B₀ n) (h0 (ε * ϖ ^ m) b₄ t κ)
    letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)
    Localization.Away (algebraMap 𝒯0 (TateGlue1.Xn ϖ 𝒯0 B₀ n) (h0 (ε * ϖ ^ m) b₄ t κ)) ≃ₐ[𝒲]
      Localization.Away (algebraMap 𝒯 (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)) :=
  letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
  haveI := towerT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
  haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ
  haveI : IsScalarTower 𝒯0 𝒲 L := IsScalarTower.of_algebraMap_eq fun x ↦ (hρ x).symm
  letI := alg0n (ϖ := ϖ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ) n
  letI := alg1n (ϖ := ϖ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ) n
  haveI := isLocalization_rho0n ϖ (ε * ϖ ^ m) b₄ t κ n
  haveI := isLocalization_rho1n ϖ (ε * ϖ ^ m) b₄ t κ n
  NormOverlap.omegaEquivW (B₀ := B₀) (B₁ := B₁) (L := L) (a₀ := h0 (ε * ϖ ^ m) b₄ t κ)
    (a₁ := h1 (ε * ϖ ^ m) b₄ t κ) (ha₀ := TateS5.h0_ne_zero hρ) (ha₁ := TateS5.h1_ne_zero)
    (I := EtaleTower.Iv ϖ n) (hS₀ := fun _ ↦ rfl) (hS₁ := fun _ ↦ rfl)

set_option maxHeartbeats 2000000 in
-- the overlap identifications at the Tate charts
/-- **The witness of the overlap identification, at level `n` and on the special fibre**: for
`b ∈ B₀` there are `y ∈ B₁`, `k` with `ωn(b̄/1)·h'ᵏ = ȳ/1` and `ω(b̄/1)·h̄'ᵏ = ȳ/1`. -/
theorem omega_witness (n : ℕ) (b : B₀) : ∃ (y : B₁) (k : ℕ),
    (letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ);
      haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ;
      letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯0 B₀ n) (h0 (ε * ϖ ^ m) b₄ t κ);
      letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ);
      omegaN (B₀ := B₀) (B₁ := B₁) hρ n (algebraMap (TateGlue1.Xn ϖ 𝒯0 B₀ n) _ (Ideal.Quotient.mk
          _ b)) *
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) (Localization.Away (algebraMap 𝒯
          (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)))
          (algebraMap 𝒯 (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)) ^ k =
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) _ (Ideal.Quotient.mk _ y)) ∧
    (omegaNorm θ (B₀ := B₀) (B₁ := B₁) hρ (TateS5.h0_ne_zero hρ) TateS5.h1_ne_zero
        (algebraMap (Cs θ 𝒯0 B₀) _ (Ideal.Quotient.mk _ b)) *
      algebraMap (Cs θ 𝒯 B₁) (Localization.Away (algebraMap (EtaleTower.Ts θ 𝒯) (Cs θ 𝒯 B₁)
          (Ideal.Quotient.mk _ (h1 (ε * ϖ ^ m) b₄ t κ))))
        (algebraMap (EtaleTower.Ts θ 𝒯) (Cs θ 𝒯 B₁) (Ideal.Quotient.mk _ (h1 (ε * ϖ ^ m) b₄ t κ)))
            ^ k =
      algebraMap (Cs θ 𝒯 B₁) _ (Ideal.Quotient.mk _ y)) := by
  letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
  haveI := towerT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
  haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ
  haveI : IsScalarTower 𝒯0 𝒲 L := IsScalarTower.of_algebraMap_eq fun x ↦ (hρ x).symm
  obtain ⟨y, k, H⟩ := NormOverlap.exists_omegaEquiv_mul_pow (O := O) (B₀ := B₀) (B₁ := B₁) (L := L)
    (W := 𝒲) (h0 (ε * ϖ ^ m) b₄ t κ) (h1 (ε * ϖ ^ m) b₄ t κ) (TateS5.h0_ne_zero hρ)
    TateS5.h1_ne_zero b
  refine ⟨y, k, ?_, ?_⟩
  · letI := alg0n (ϖ := ϖ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ) n
    letI := alg1n (ϖ := ϖ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ) n
    haveI := isLocalization_rho0n ϖ (ε * ϖ ^ m) b₄ t κ n
    haveI := isLocalization_rho1n ϖ (ε * ϖ ^ m) b₄ t κ n
    have e := H (EtaleTower.Iv ϖ n) (fun _ ↦ rfl) (fun _ ↦ rfl)
    exact e
  · letI := alg0s θ (ε * ϖ ^ m) b₄ t κ
    letI := alg1s θ (ε * ϖ ^ m) b₄ t κ
    haveI := isLocalization_alg0s θ (ε * ϖ ^ m) b₄ t κ
    haveI := isLocalization_alg1s θ (ε * ϖ ^ m) b₄ t κ
    have e := H (RingHom.ker θ) (fun _ ↦ rfl) (fun _ ↦ rfl)
    exact e

end Data
end
end TateS6
end SemistableReduction
