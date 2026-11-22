/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Lift
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormCuspTwo
import TemperedFundamentalGroups.SemistableReduction.TateSystemMap

/-!
# I3 surjectivity at Tate: lifting balanced morphisms of special-fibre data (MR12)

**`TateS6.exists_hom_spec`**: for two tame covers `L`, `L'` of the function field of the Tate
model (the data of `TateS5`) and a balanced morphism `F = (f₁, f₀)` of their special-fibre data
(`TateGlue1.Balanced`), there is a morphism `Φ : P_L → P_L'` of chart algebras of the
normalisations which is the identity on `T1` and reduces to `f₁` on `B₁/J` and to `f₀` on
`B₀/J`.

Proof: one application of the generic `NodeEtaleGlue.Overlap.exists_hom_of_cuspLevelsW`, with
the cusp level data of `lift_iso_normalisation` (over `VF`, spelled as in `TateS6Lift`) and the
arguments of `TateGlue0.systemMapT` (over `overlapCusp`); the two spellings of the same overlap
are identified by `HEq.rfl`. No statement at the Tate data mentions the algebraizations (their
reductions `A.α n` hang at concrete inputs, MR12 c50b).
-/

universe u
open Module Polynomial
namespace SemistableReduction

namespace TateS6
open TateS5 TateTwoChart TateTwoChartNode TateGlue0 TateLevel TateGlue1
open TensorProduct
open AdmissibleLift (J)
open FormalKummer (Cs)
noncomputable section
section Data

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsSepClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m] [hsq : Fact (IsSquare (θ b₆))]

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
  (L' : Type u) [Field L'] [Algebra K L'] [FiniteDimensional K L'] [IsGalois K L']
  (hL' : (finrank K L').Coprime q) (hd' : finrank K L' ∣ e)
  [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L'] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L'] [Algebra (NR b₄
      b₆ ϖ m ε) L'] [IsScalarTower (NR b₄ b₆ ϖ m ε) K L']
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) L'] [IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) K L'] [Algebra (T0
      (ε
      * ϖ ^ m) b₄ t κ) L'] [IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) L']
  [Algebra (T01 (ε * ϖ ^ m) b₄ t κ) L'] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t
      κ) L']
  (hρ' : ∀ x, algebraMap (T01 (ε * ϖ ^ m) b₄ t κ) L' (rho0 (ε * ϖ ^ m) b₄ t κ x) = algebraMap (T0 (ε
      * ϖ ^ m) b₄ t κ) L' x)
  (B₁' : Type u) [CommRing B₁'] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁'] [Algebra B₁' L']
      [IsScalarTower
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁' L']
  [IsIntegralClosure B₁' (T1 (ε * ϖ ^ m) b₄ t κ) L']
  (Bn' : Type u) [CommRing Bn'] [Algebra (NR b₄ b₆ ϖ m ε) Bn'] [Algebra Bn' L'] [IsScalarTower (NR
      b₄ b₆
      ϖ m ε) Bn' L']
  [Algebra B₁' Bn'] [IsScalarTower B₁' Bn' L']
  [IsLocalization.Away (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁' (DT (ε * ϖ ^ m) b₄ t κ)) Bn']
  (hBn' : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) Bn' (toNode b₄ hκ rfl x) = algebraMap B₁' Bn' (algebraMap
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁' x))
  (B₀' : Type u) [CommRing B₀'] [Algebra (T0 (ε * ϖ ^ m) b₄ t κ) B₀'] [Algebra B₀' L']
      [IsScalarTower
      (T0 (ε * ϖ ^ m) b₄ t κ) B₀' L']
  [IsIntegralClosure B₀' (T0 (ε * ϖ ^ m) b₄ t κ) L']
  (Bc' : Type u) [CommRing Bc'] [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) Bc'] [Algebra Bc' L']
      [IsScalarTower
      (RcT (ε * ϖ ^ m) b₄ t κ) Bc' L']
  [Algebra B₀' Bc'] [IsScalarTower B₀' Bc' L']
  [IsLocalization.Away (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀' (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ))
      Bc']
  (hBc' : ∀ x, algebraMap (RcT (ε * ϖ ^ m) b₄ t κ) Bc' (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε *
      ϖ ^ m) b₄ t κ) x) = algebraMap B₀' Bc' (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀' x))
  (hunr₁' : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T1 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₁') [Q.IsPrime],
    Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁') < P → Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄
      t κ) Q)
  (hunr₀' : ∀ (P : Ideal (T0 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T0 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₀') [Q.IsPrime],
    Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀') < P →
      Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀') ≠
        Ideal.span {h0 (ε * ϖ ^ m) b₄ t κ, z0 (ε * ϖ ^ m) b₄ t κ} →
      Algebra.IsUnramifiedAt (T0 (ε * ϖ ^ m) b₄ t κ) Q)
  (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (h0 (ε * ϖ ^ m) b₄ t
        κ))))

variable {K L B₁ Bn B₀ Bc L' B₁' Bn' B₀' Bc'}

local notation "𝒯" => T1 (ε * ϖ ^ m) b₄ t κ

local notation "𝒩" => NR b₄ b₆ ϖ m ε

local notation "𝓢c" => sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "𝓢p" => sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝒯0" => T0 (ε * ϖ ^ m) b₄ t κ

local notation "𝒲" => T01 (ε * ϖ ^ m) b₄ t κ

local notation "𝓓" => cuspF hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "ℛ" => RcT (ε * ϖ ^ m) b₄ t κ

local notation "𝓘F" => inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝓥" => VF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "𝓞" => om hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "𝓒" => cuspLevels hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "𝓓V" => cuspV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "𝓘C1" => NodeEtaleGlue.Input.C1 (inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL
  hBn hunr₁ τ)

local notation "𝓘Bs" => NodeEtaleGlue.Input.Bs (inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL
  hBn hunr₁ τ)

local notation "ρXF" => ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝓟" => twoChartL L hρ B₀ B₁

local notation "ωFF" => ωF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "bridge1F" => bridge1 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ
  hBn
    hBc hunr₁ hunr₀ τ φ₀

local notation "q0FF" => q0F (B₀ := B₀) (B₁ := B₁) hρ

local notation "q1FF" => q1F (B₀ := B₀) (B₁ := B₁) hρ

local notation "𝓹" => piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝓹h" => piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝓹'" => piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ

local notation "𝓹h'" => piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ

local notation "𝓢p'" => sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ

local notation "𝓢c'" => sc hϖ hker hκ hε h3 hE hb₆ he hζe hd' hBc' hunr₀' φ₀

local notation "𝓞'" => om hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ' hBn'
    hBc' hunr₁' hunr₀' τ φ₀

set_option maxHeartbeats 4000000 in
-- instantiating `exists_hom_of_cuspLevelsW` at the Tate data of two covers
/-- **I3 surjectivity at Tate, chart algebra form**: a balanced morphism `F = (f₁, f₀)` of the
special-fibre data of two tame covers lifts to a morphism `Φ : P_L → P_L'` of chart algebras of the
normalisations which is the identity on `T1` and reduces to `f₁`, `f₀`
(`NodeEtaleGlue.Overlap.exists_hom_of_cuspLevelsW`). -/
theorem exists_hom_spec [IsAdicComplete (Ideal.span {ϖ}) O] (h2 : (2 : k) ≠ 0)
    (F : OmegaPair.Hom (Ideal.Quotient.mk (J θ (R := 𝒯0)) (h0 (ε * ϖ ^ m) b₄ t κ))
      (Ideal.Quotient.mk (J θ (R := 𝒯)) (h1 (ε * ϖ ^ m) b₄ t κ)) ⇑(𝓞) ⇑(𝓞'))
    (hbal : TateGlue1.Balanced hκ rfl hε (𝓢p) (𝓢p') (TateS5.θ_ϖ hker) (𝓹) (𝓹') F.f₁)
    (hsepP : ∀ b : (twoChartL L hρ B₀ B₁).R1,
      (∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (twoChartL L hρ B₀ B₁).R1)) → b = 0)
    (hsepP' : ∀ b : (twoChartL L' hρ' B₀' B₁').R1,
      (∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (twoChartL L' hρ' B₀' B₁').R1)) →
        b = 0) :
    ∃ Φ : ProjectiveLine.ChartModule.Hom (twoChartL L hρ B₀ B₁).chartModule
        (twoChartL L' hρ' B₀' B₁').chartModule,
      (twoChartL L hρ B₀ B₁).algStr.IsHom (twoChartL L' hρ' B₀' B₁').algStr Φ ∧
      (∀ r, Φ.f1 (algebraMap 𝒯 B₁ r) = algebraMap 𝒯 B₁' (RingHom.id 𝒯 r)) ∧
      (∀ u, ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ 0
          (q1F (B₀ := B₀') (B₁ := B₁') hρ' 0 (Φ.f1 u)) =
        F.f₁.toRingHom (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ 0
          (q1F (B₀ := B₀) (B₁ := B₁) hρ 0 u))) ∧
      (∀ b, ρX0 (B₀ := B₀') hker 0 (q0F (B₀ := B₀') (B₁ := B₁') hρ' 0 (Φ.f0 b)) =
        F.f₀.toRingHom (ρX0 (B₀ := B₀) hker 0 (q0F (B₀ := B₀) (B₁ := B₁) hρ 0 b))) := by
  haveI := finite_B₁ hϖ hker hκ hε h3 hE K L B₁
  haveI := finite_B₀ hϖ hker hκ hε h3 hE hb₆ K L hρ B₁ B₀ Bc hBc
  haveI := finite_x0L L hρ B₀ B₁
  haveI := finite_x1L L hρ B₀ B₁
  haveI := finite_B₁ hϖ hker hκ hε h3 hE K L' B₁'
  haveI := finite_B₀ hϖ hker hκ hε h3 hE hb₆ K L' hρ' B₁' B₀' Bc' hBc'
  haveI := finite_x0L L' hρ' B₀' B₁'
  haveI := finite_x1L L' hρ' B₀' B₁'
  exact
  NodeEtaleGlue.Overlap.exists_hom_of_cuspLevelsW
    (Vs := (VF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ
        φ₀))
    (Dp := (cuspV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁
        hunr₀ τ φ₀))
    (Vc := (cuspLevels hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀))
    (algRI := fun l ↦ inferInstanceAs (Algebra (RcT (ε * ϖ ^ m) b₄ t κ) (EtaleTower.Tn ϖ (RcT (ε *
        ϖ ^ m) b₄ t κ) l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O (RcT (ε * ϖ ^ m) b₄ t κ) (EtaleTower.Tn
        ϖ (RcT (ε * ϖ ^ m) b₄ t κ) l)))
    (towerRII := fun l ↦ inferInstanceAs
      (IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) (EtaleTower.Tn ϖ (RcT (ε * ϖ ^ m) b₄ t κ) (l + 1))
          (EtaleTower.Tn ϖ (RcT (ε * ϖ ^ m) b₄ t κ) l)))
    (hkI := rfl) (hT := HEq.rfl) (hP0 := rfl) (P := twoChartL L hρ B₀ B₁)
    (e1 := eqFam hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
    (X0 := TateGlue1.Xn ϖ (T0 (ε * ϖ ^ m) b₄ t κ) B₀)
    (μ0 := CuspTower.XmapC ϖ B₀) (ωn := ωF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL
        hd hρ hBn hBc hunr₁ hunr₀ τ φ₀) (t := tC (B₀ := B₀) hBc)
    (ht := fun n ↦ CuspTower.toTensorC_algebraMap ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (htloc := fun n ↦ CuspTower.isLocalization_toTensorC ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc
        hBc n)
    (ρX1 := ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (ρX0 := ρX0 (B₀ := B₀)
        hker) (hρ := hρV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
            hunr₁ hunr₀ τ φ₀)
    (hJm := fun n ↦ EtaleTower.hJ hker.le n) (hψ1 := hψ1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k
        he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀) (hx1c := hx1F hϖ hker hκ hε h3 hE hb₆ hqM
            hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀)
    (hω := hω0 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ
        φ₀) (q0 := q0F (B₀ := B₀) (B₁ := B₁) hρ) (hq0O := fun _ _ ↦ rfl)
    (q1 := q1F (B₀ := B₀) (B₁ := B₁) hρ) (hq1O := fun _ _ ↦ rfl) (hx := fun _ ↦ rfl)
    (hy := fun _ ↦ rfl) (hW := hWF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ
        hBn hBc hunr₁ hunr₀ τ φ₀)
    (hμt := fun n x ↦ CuspTower.toTensorC_succ ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n x)
    (hμ0 := fun _ _ ↦ rfl) (hμ1 := fun _ _ ↦ rfl) (hs0 := fun _ ↦ Ideal.Quotient.mk_surjective)
    (hs1 := fun _ ↦ Ideal.Quotient.mk_surjective) (hk0 := hk0F hϖ hker hκ hε h3 hE hb₆ hqM hq hM'
        hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀) (hk1 := hk1F hϖ hker hκ hε h3 hE hb₆
            hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀)
    (hK := hsepP) (hJ0D := (TateGlue0.J_Tn_zero_eq_bot hker.le _))
    (bot := (cuspV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁
        hunr₀ τ φ₀).bottom hθ.out (isUnit_of_θ_ne_zero hϖ hker) (TateGlue0.J_Tn_zero_eq_bot
            hker.le _)) (hbot := HEq.rfl)
    (he1 := (levelsS5 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁
        τ).levelEquivXFam_equiv_zero
      (inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
      (fun l a ↦ QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (TateS5.θ_ϖ hker) l a)
      (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl
      (towerORI := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
      (towerX := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
      (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (fun n ↦ toTensor_algebraMap
          hκ hBn n) (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (hρ_lev hϖ hker
              hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
      (fun n ↦ TateGlue1.isLocalization_toTensor hκ B₁ Bn hBn n) (φE hϖ hker hκ hε h3 hE hqM hq
          hM' hM'k hK hζ hL hBn hunr₁ τ) (hE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn
              hunr₁ τ)
      (hlocE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (Xmap (ϖ := ϖ) (b₄ :=
          b₄) (t := t) (κ := κ) (ε := ε) (m := m) (B₁ := B₁))
      (fun n y ↦ RingHom.congr_fun (tF_succ hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁
          τ n) y) (hμE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
              (TateGlue0.J_Tn_zero_eq_bot hker.le _))
    (ψ1 := algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁) (hψq := fun _ _ ↦ rfl)
    (Vs' := (VF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc' hunr₁'
        hunr₀' τ φ₀))
    (Dp' := (cuspV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc'
        hunr₁' hunr₀' τ φ₀))
    (Vc' := (cuspLevels hϖ hker hκ hε h3 hE hb₆ he hζe hd' hBc' hunr₀' φ₀))
    (algRI' := fun l ↦ inferInstanceAs (Algebra (RcT (ε * ϖ ^ m) b₄ t κ) (EtaleTower.Tn ϖ (RcT (ε
        * ϖ ^ m) b₄ t κ) l)))
    (towerORI' := fun l ↦ inferInstanceAs (IsScalarTower O (RcT (ε * ϖ ^ m) b₄ t κ) (EtaleTower.Tn
        ϖ (RcT (ε * ϖ ^ m) b₄ t κ) l)))
    (towerRII' := fun l ↦ inferInstanceAs
      (IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) (EtaleTower.Tn ϖ (RcT (ε * ϖ ^ m) b₄ t κ) (l + 1))
          (EtaleTower.Tn ϖ (RcT (ε * ϖ ^ m) b₄ t κ) l)))
    (hkI' := rfl) (hT' := HEq.rfl) (hP0' := rfl) (P' := twoChartL L' hρ' B₀' B₁')
    (e1' := eqFam hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ)
    (X0' := TateGlue1.Xn ϖ (T0 (ε * ϖ ^ m) b₄ t κ) B₀')
    (μ0' := CuspTower.XmapC ϖ B₀') (ωn' := ωF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe
        hL' hd' hρ' hBn' hBc' hunr₁' hunr₀' τ φ₀) (t' := tC (B₀ := B₀') hBc')
    (ht' := fun n ↦ CuspTower.toTensorC_algebraMap ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀' Bc'
        hBc' n)
    (htloc' := fun n ↦ CuspTower.isLocalization_toTensorC ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀'
        Bc' hBc' n)
    (ρX1' := ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ) (ρX0' := ρX0 (B₀ :=
        B₀') hker) (hρ' := hρV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ'
            hBn' hBc' hunr₁' hunr₀' τ φ₀)
    (hJm' := fun n ↦ EtaleTower.hJ hker.le n) (hψ1' := hψ1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM'
        hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc' hunr₁' hunr₀' τ φ₀) (hx1c' := hx1F hϖ hker hκ hε
            h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc' hunr₁' hunr₀' τ φ₀)
    (hω' := hω0 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc' hunr₁'
        hunr₀' τ φ₀) (q0' := q0F (B₀ := B₀') (B₁ := B₁') hρ') (hq0O' := fun _ _ ↦ rfl)
    (q1' := q1F (B₀ := B₀') (B₁ := B₁') hρ') (hq1O' := fun _ _ ↦ rfl) (hx' := fun _ ↦ rfl)
    (hy' := fun _ ↦ rfl) (hW' := hWF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd'
        hρ' hBn' hBc' hunr₁' hunr₀' τ φ₀)
    (hμt' := fun n x ↦ CuspTower.toTensorC_succ ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀' Bc' hBc' n
        x)
    (hμ0' := fun _ _ ↦ rfl) (hμ1' := fun _ _ ↦ rfl) (hs0' := fun _ ↦ Ideal.Quotient.mk_surjective)
    (hs1' := fun _ ↦ Ideal.Quotient.mk_surjective) (hk0' := hk0F hϖ hker hκ hε h3 hE hb₆ hqM hq
        hM' hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc' hunr₁' hunr₀' τ φ₀) (hk1' := hk1F hϖ hker hκ
            hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc' hunr₁' hunr₀' τ φ₀)
    (hK' := hsepP') (hJ0D' := (TateGlue0.J_Tn_zero_eq_bot hker.le _))
    (bot' := (cuspV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL' hd' hρ' hBn' hBc'
        hunr₁' hunr₀' τ φ₀).bottom hθ.out (isUnit_of_θ_ne_zero hϖ hker)
            (TateGlue0.J_Tn_zero_eq_bot hker.le _)) (hbot' := HEq.rfl)
    (he1' := (levelsS5 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁'
        τ).levelEquivXFam_equiv_zero
      (inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ)
      (fun l a ↦ QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (TateS5.θ_ϖ hker) l a)
      (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl
      (towerORI := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
      (towerX := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
      (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ) (fun n ↦
          toTensor_algebraMap hκ hBn' n) (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn'
              hunr₁' τ) (hρ_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ)
      (fun n ↦ TateGlue1.isLocalization_toTensor hκ B₁' Bn' hBn' n) (φE hϖ hker hκ hε h3 hE hqM hq
          hM' hM'k hK hζ hL' hBn' hunr₁' τ) (hE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL'
              hBn' hunr₁' τ)
      (hlocE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ) (Xmap (ϖ := ϖ) (b₄
          := b₄) (t := t) (κ := κ) (ε := ε) (m := m) (B₁ := B₁'))
      (fun n y ↦ RingHom.congr_fun (tF_succ hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn'
          hunr₁' τ n) y) (hμE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL' hBn' hunr₁' τ)
              (TateGlue0.J_Tn_zero_eq_bot hker.le _))
    (ψ1' := algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁') (hψq' := fun _ _ ↦ rfl)
    (V := (overlapCusp hκ rfl hε (TateS5.θ_ϖ hker) (𝓹) (𝓹h) hker.le (𝓢p) (NeZero.ne m) (𝓢c)
        (isUnit_of_θ_ne_zero hϖ hker) (𝓞)))
    (V' := (overlapCusp hκ rfl hε (TateS5.θ_ϖ hker) (𝓹') (𝓹h') hker.le (𝓢p') (NeZero.ne m) (𝓢c')
        (isUnit_of_θ_ne_zero hϖ hker) (𝓞')))
    (hR₀ := rfl) (hcR := HEq.rfl) (haR := HEq.rfl) (hf₀ := HEq.rfl) (hφ₀ := HEq.rfl)
    (hφ₀' := HEq.rfl) (hψ₀ := HEq.rfl) (hcov := HEq.rfl) (hcov' := HEq.rfl) (hπ := HEq.rfl)
    (hπ' := HEq.rfl) (hIs := HEq.rfl) (hIs' := HEq.rfl) (hVs := HEq.rfl) (hVs' := HEq.rfl)
    (hϖs := rfl) (hϖs' := rfl) (hJ0s := (TateGlue0.J_Tn_zero_eq_bot hker.le _)) (hJ0s' :=
        (TateGlue0.J_Tn_zero_eq_bot hker.le _))
    (β0s := RingHom.id (T1 (ε * ϖ ^ m) b₄ t κ)) (hβ0s := HEq.rfl)
    (φ1s := F.f₁.toRingHom) (hφ1s := HEq.rfl) (φ0s := F.f₀.toRingHom) (hφ0s := HEq.rfl)
    (bot₂ := ((CuspTower.cuspInput (𝓢c) (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε * ϖ ^ m)
        b₄ t κ)).bottom hθ.out (isUnit_of_θ_ne_zero hϖ hker)
      (J_Tn_zero_eq_bot hker.le _))) (hbot₂ := HEq.rfl)
    (bot₂' := ((CuspTower.cuspInput (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε * ϖ ^
        m) b₄ t κ)).bottom hθ.out (isUnit_of_θ_ne_zero hϖ hker)
      (J_Tn_zero_eq_bot hker.le _))) (hbot₂' := HEq.rfl)
    (hO := (isUnit_of_θ_ne_zero hϖ hker))
    (hR := ((input_R hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹') (𝓹h')).trans
        (input_R hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)).symm))
    (hc := ((input_commRingR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹')
        (𝓹h')).trans
      (input_commRingR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)).symm))
    (ha := ((input_algOR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹') (𝓹h')).trans
      (input_algOR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)).symm))
    (hk := ((input_algkR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹') (𝓹h')).trans
      (input_algkR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)).symm))
    (hs := ((input_algSuccR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹')
        (𝓹h')).trans
      (input_algSuccR hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)).symm))
    (hF := ((input_f hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹') (𝓹h')).trans
        (input_f hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)).symm))
    (hE := ((input_e hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹') (𝓹h')).trans
        (input_e hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)).symm))
    (φ := (covMap hκ rfl hε (𝓢p) (𝓢p') F.f₁))
    (hcd := (nodeCoordI hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓹) (𝓹h)))
    (hcd' := (nodeCoordI hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p') (𝓹') (𝓹h')))
    (hcu := (fun _ ↦ heq_refl_hat _))
    (hcv := (fun _ ↦ heq_refl_hat _))
    (hbal := hbal)
    (e := (fun n ↦ (eMap hκ rfl (𝓢p) (𝓢p') (TateS5.θ_ϖ hker) hker.le F.f₁ n).toRingHom))
    (he := (fun n ↦ (eMap hκ rfl (𝓢p) (𝓢p') (TateS5.θ_ϖ hker) hker.le F.f₁ n).commutes _))
    (β := (βI hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓢p') (𝓹) (𝓹h) (𝓹') (𝓹h')))
    (hβJ := (hβJI hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓢p') (𝓹) (𝓹h) (𝓹') (𝓹h')))
    (hβa := (hβaI hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓢p') (𝓹) (𝓹h) (𝓹') (𝓹h')))
    (heβ := (heβI hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓢p') (𝓹) (𝓹h) (𝓹') (𝓹h')
        F.f₁))
    (hβR := (hβRI hκ rfl hε (TateS5.θ_ϖ hker) hker.le (NeZero.ne m) (𝓢p) (𝓢p') (𝓹) (𝓹h) (𝓹') (𝓹h')))
    (φ1 := F.f₁.toRingHom)
    (hφc := (covMap_ι₀ hκ rfl hε (𝓢p) (𝓢p') F.f₁))
    (ℓb := (EtaleTower.CbMap (C := (𝓢p).C1) (C' := (𝓢p').C1) (T1 (ε * ϖ ^ m) b₄ t κ) (w1 (ε * ϖ ^
        m) b₄ t κ) F.f₁))
    (hℓb := (fun c ↦ EtaleTower.CbMap_algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) (w1 (ε * ϖ ^ m) b₄ t κ)
        F.f₁ c))
    (hσE := (fun n y ↦ EtaleTower.σ_homLift (T1 (ε * ϖ ^ m) b₄ t κ) (TateS5.θ_ϖ hker) (w1 (ε * ϖ ^
        m) b₄ t κ) hker.le F.f₁
      (E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (𝓢p) n) (E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (𝓢p') n) y))
    (heS := (fun n x ↦ sE_eMap hκ rfl (𝓢p) (𝓢p') (TateS5.θ_ϖ hker) hker.le F.f₁ n x))
    (β0 := (RingHom.id (T1 (ε * ϖ ^ m) b₄ t κ)))
    (hβ0 := (fun _ _ ↦ rfl))
    (hx1 := rfl)
    (hg0 := rfl)
    (hβ0O := (fun _ ↦ rfl))
    (p := (fun n ↦ CuspTower.pieceP (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε *
        ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
      (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ n))
    (hp0 := (fun n ↦ CuspTower.pieceP_algebraMapB (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le
        (isSMulRegular_h0 ϖ (ε * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
      (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ n _))
    (hpO := (fun n o ↦ CuspTower.pieceP_algebraMapO (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le
        (isSMulRegular_h0 ϖ (ε * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
      (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ n o))
    (hpS := (fun n x ↦ CuspTower.sP_pieceP (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0
        ϖ (ε * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
      (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ n x))
    (hpB := (fun n b ↦ (overlapCusp hκ rfl hε (TateS5.θ_ϖ hker) (𝓹) (𝓹h) hker.le (𝓢p) (NeZero.ne
        m) (𝓢c) (isUnit_of_θ_ne_zero hϖ hker) (𝓞)).mM_algebraMap0
      (overlapCusp hκ rfl hε (TateS5.θ_ϖ hker) (𝓹') (𝓹h') hker.le (𝓢p') (NeZero.ne m) (𝓢c')
          (isUnit_of_θ_ne_zero hϖ hker) (𝓞'))
      (CuspTower.pieceP (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε * ϖ ^ m) b₄ t
          κ) (isUnit_of_θ_ne_zero hϖ hker)
        (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ n)
      (CuspTower.pieceP_algebraMapB (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε *
          ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
        (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ n _)
      (RingHom.id (EtaleTower.Tn ϖ (T0 (ε * ϖ ^ m) b₄ t κ) n))
      (fun y ↦ CuspTower.pieceP_algebraMapB (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0
          ϖ (ε * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
        (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ n y)
      (RingHom.id _) (fun _ ↦ rfl) (RingHom.id (T1 (ε * ϖ ^ m) b₄ t κ)) (fun _ ↦ rfl) b))
    (hJ0 := (J_Tn_zero_eq_bot hker.le _))
    (hJ0' := (J_Tn_zero_eq_bot hker.le _))
    (hpγ := (fun c z hz ↦ (overlapCusp hκ rfl hε (TateS5.θ_ϖ hker) (𝓹) (𝓹h) hker.le (𝓢p)
        (NeZero.ne m) (𝓢c) (isUnit_of_θ_ne_zero hϖ hker) (𝓞)).mk_mM_γM
      (overlapCusp hκ rfl hε (TateS5.θ_ϖ hker) (𝓹') (𝓹h') hker.le (𝓢p') (NeZero.ne m) (𝓢c')
          (isUnit_of_θ_ne_zero hϖ hker) (𝓞'))
      (CuspTower.pieceP (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε * ϖ ^ m) b₄ t
          κ) (isUnit_of_θ_ne_zero hϖ hker)
        (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ 0)
      (CuspTower.pieceP_algebraMapB (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε *
          ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
        (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ 0 _)
      (fun o ↦ CuspTower.pieceP_algebraMapO (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0
          ϖ (ε * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
        (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ 0 o)
      F.f₀.toRingHom
      (fun c' z' hz' ↦ CuspTower.mk_liftP_ℓ0 (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le
          (isSMulRegular_h0 ϖ (ε * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
        (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ 0
        (CuspTower.pieceP_algebraMapB (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε
            * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
          (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ 0 _) c' z' hz')
      (OmegaPair.awayMap (C := (𝓢c).C0) (C' := (𝓢c').C0)
        (Ideal.Quotient.mk (J θ (R := T0 (ε * ϖ ^ m) b₄ t κ)) (h0 (ε * ϖ ^ m) b₄ t κ)) F.f₀)
      (fun c ↦ OmegaPair.awayMap_algebraMap (C := (𝓢c).C0) (C' := (𝓢c').C0)
        (Ideal.Quotient.mk (J θ (R := T0 (ε * ϖ ^ m) b₄ t κ)) (h0 (ε * ϖ ^ m) b₄ t κ)) F.f₀ c)
      F.f₁.toRingHom
      (OmegaPair.awayMap (C := (𝓢p).C1) (C' := (𝓢p').C1)
        (Ideal.Quotient.mk (J θ (R := T1 (ε * ϖ ^ m) b₄ t κ)) (h1 (ε * ϖ ^ m) b₄ t κ)) F.f₁)
      (fun c ↦ OmegaPair.awayMap_algebraMap (C := (𝓢p).C1) (C' := (𝓢p').C1)
        (Ideal.Quotient.mk (J θ (R := T1 (ε * ϖ ^ m) b₄ t κ)) (h1 (ε * ϖ ^ m) b₄ t κ)) F.f₁ c)
      (fun w ↦ OmegaPair.Hom.comm_algEquiv (𝓞) (𝓞') F w) c z hz))
    (ϖ := ϖ)
    (h := rfl)
    (h' := rfl)
    (φ0 := F.f₀.toRingHom)
    (hpb := (fun c ↦ CuspTower.pieceMap_bottom (𝓢c) (𝓢c') (TateS5.θ_ϖ hker) hker.le
        (isSMulRegular_h0 ϖ (ε * ϖ ^ m) b₄ t κ) (isUnit_of_θ_ne_zero hϖ hker)
      (cuspNFc (TateS5.θ_ϖ hker) hker.le h2 hκ hb₆ (𝓢c')) F.f₀ (J_Tn_zero_eq_bot hker.le _) c))
    (Lx0 := (OmegaPair.awayMap (C := (𝓢c).C0) (C' := (𝓢c').C0)
      (Ideal.Quotient.mk (J θ (R := T0 (ε * ϖ ^ m) b₄ t κ)) (h0 (ε * ϖ ^ m) b₄ t κ)) F.f₀))
    (hLx0 := (fun c ↦ OmegaPair.awayMap_algebraMap (C := (𝓢c).C0) (C' := (𝓢c').C0)
      (Ideal.Quotient.mk (J θ (R := T0 (ε * ϖ ^ m) b₄ t κ)) (h0 (ε * ϖ ^ m) b₄ t κ)) F.f₀ c))
    (Lx1 := (OmegaPair.awayMap (C := (𝓢p).C1) (C' := (𝓢p').C1)
      (Ideal.Quotient.mk (J θ (R := T1 (ε * ϖ ^ m) b₄ t κ)) (h1 (ε * ϖ ^ m) b₄ t κ)) F.f₁))
    (hLx1 := (fun c ↦ OmegaPair.awayMap_algebraMap (C := (𝓢p).C1) (C' := (𝓢p').C1)
      (Ideal.Quotient.mk (J θ (R := T1 (ε * ϖ ^ m) b₄ t κ)) (h1 (ε * ϖ ^ m) b₄ t κ)) F.f₁ c))
    (hωL := (fun w ↦ OmegaPair.Hom.comm_algEquiv (𝓞) (𝓞') F w))

end Data
end
end TateS6
end SemistableReduction
