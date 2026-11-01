/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateV0Equiv
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormCusp
import TemperedFundamentalGroups.SemistableReduction.CuspTensorLevelSucc
import TemperedFundamentalGroups.SemistableReduction.TateNormalisationChart
import TemperedFundamentalGroups.SemistableReduction.NormOverlapWitness

/-!
# The M2 lift of a tame cover of the Tate curve is the normalisation (MR12 S6, G5)

**`TateS6.lift_iso_normalisation`**: for a tame Galois cover `L` of the function field of the Tate
model (the data of `TateS5`), every algebraization `(N, BN, α)` of the adic system
`systemCusp … (sp) (sc) (om)` (e.g. the one of `TateS5.liftCusp_tame`) is isomorphic as a chart
algebra to `P_L = (B₀, B₁)`, the normalisations of the charts `T0`, `T1` in `L`
(`TateS6.twoChartL`).

This is `NodeEtaleGlue.Overlap.exists_iso_of_cuspLevelsW` at the covering `VF` with
* over `V₁`: the levels `B₁/ϖⁿ⁺¹` with the identifications `eqFam`;
* over `V₀`: the levels `B₀/ϖⁿ⁺¹` with `equiv0`'s data (`ωF`, `tC`, `ρX0`, `hρV`, `hψ1F`, `hx1F`,
  `hω0`), the reductions `XmapC` and `tC_succ` (`CuspTower.toTensorC_succ`);
* the reductions `q0F`, `q1F` of `P_L` (kernels `ker_mk_map`), the witnesses `hWF` of the overlap
  identifications on the overlap of `P_L` (`omegaN_mul_pow_of_L`, from the equation in `L`),
  `hSF : VF.system = systemCusp …` (by `rfl`) and the finiteness of `B₀`, `B₁`.
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

set_option maxHeartbeats 2000000 in
-- unfolding `VF` and `overlapCusp`
/-- **The adic system of `VF` is `systemCusp`** (definitionally; `VF` is `overlapCusp` over
`inpF`). -/
theorem hSF : (𝓥).system hθ.out (isUnit_of_θ_ne_zero hϖ hker) =
    systemCusp hκ rfl hε (TateS5.θ_ϖ hker) (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn
        hunr₁ τ) (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (𝓢p)
        (NeZero.ne m)
      (𝓢c) (isUnit_of_θ_ne_zero hϖ hker) (𝓞) := rfl

/-- **The reductions of the first chart of `P_L`**: `B₀ → B₀/ϖⁿ⁺¹`. -/
abbrev q0F (n : ℕ) : (𝓟).R0 →+* TateGlue1.Xn ϖ 𝒯0 B₀ n := Ideal.Quotient.mk _

/-- **The reductions of the second chart of `P_L`**: `B₁ → B₁/ϖⁿ⁺¹`. -/
abbrev q1F (n : ℕ) : (𝓟).R1 →+* TateGlue1.Xn ϖ 𝒯 B₁ n := Ideal.Quotient.mk _

local notation "q0FF" => q0F (B₀ := B₀) (B₁ := B₁) hρ

local notation "q1FF" => q1F (B₀ := B₀) (B₁ := B₁) hρ

/-- The kernels of the reductions `q0F` (`ker_mk_map`). -/
theorem hk0F (n : ℕ) :
    RingHom.ker (q0FF n) = (Ideal.span {(𝓥).ϖ} ^ (n + 1)).map (algebraMap O (𝓟).R0) :=
  ker_mk_map (A := 𝒯0) (B := B₀) _

/-- The kernels of the reductions `q1F` (`ker_mk_map`). -/
theorem hk1F (n : ℕ) :
    RingHom.ker (q1FF n) = (Ideal.span {(𝓥).ϖ} ^ (n + 1)).map (algebraMap O (𝓟).R1) :=
  ker_mk_map (A := 𝒯) (B := B₁) _

/-- An equation on the overlap of `P_L` is an equation in `L`. -/
theorem L_eq_of_P (a : B₀) (y : B₁) (k : ℕ)
    (h : (𝓟).ρ0 a * (𝓟).ρ1 (𝓟).y ^ k = (𝓟).ρ1 y) :
    algebraMap B₀ L a * algebraMap 𝒯 L (h1 (ε * ϖ ^ m) b₄ t κ) ^ k = algebraMap B₁ L y := by
  have e := congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply 𝒯 B₁ L]
  exact e

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- the overlap identifications at the Tate charts
/-- **The level-`n` overlap identification on a witness from `L`**: if `b · h'ᵏ = y` in `L`,
then `omegaN n (b̄/1) · h'ᵏ = ȳ/1` (`NormOverlap.omegaEquiv_mul_pow_of_L`). -/
def omegaN_mul_pow_of_L (n : ℕ) (b : B₀) (y : B₁) (k : ℕ)
    (h : algebraMap B₀ L b * algebraMap 𝒯 L (h1 (ε * ϖ ^ m) b₄ t κ) ^ k = algebraMap B₁ L y) :
    letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
    haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ
    letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯0 B₀ n) (h0 (ε * ϖ ^ m) b₄ t κ)
    letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)
    omegaN (B₀ := B₀) (B₁ := B₁) hρ n
        (algebraMap (TateGlue1.Xn ϖ 𝒯0 B₀ n) _ (Ideal.Quotient.mk _ b)) *
      algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) (Localization.Away (algebraMap 𝒯
        (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)))
        (algebraMap 𝒯 (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)) ^ k =
      algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) _ (Ideal.Quotient.mk _ y) := by
  letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
  haveI := towerT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
  haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ
  haveI : IsScalarTower 𝒯0 𝒲 L := IsScalarTower.of_algebraMap_eq fun x ↦ (hρ x).symm
  letI := alg0n (ϖ := ϖ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ) n
  letI := alg1n (ϖ := ϖ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ) n
  haveI := isLocalization_rho0n ϖ (ε * ϖ ^ m) b₄ t κ n
  haveI := isLocalization_rho1n ϖ (ε * ϖ ^ m) b₄ t κ n
  exact NormOverlap.omegaEquiv_mul_pow_of_L (O := O) (B₀ := B₀) (B₁ := B₁) (L := L) (W := 𝒲)
    (h0 (ε * ϖ ^ m) b₄ t κ) (h1 (ε * ϖ ^ m) b₄ t κ) (TateS5.h0_ne_zero hρ) TateS5.h1_ne_zero
    (EtaleTower.Iv ϖ n) (fun _ ↦ rfl) (fun _ ↦ rfl) b y k h

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- comparing the S5 form and the form over `VF`
/-- **The witnesses `hW` on the overlap of `P_L`**: an equation `ρ0 a · ρ1 yᵏ = ρ1 m'` gives
`ωF n (ā/1) · x₁ᵏ = m̄'/1`. -/
def hWF (n : ℕ) (a : B₀) (m' : B₁) (k : ℕ)
    (h : (𝓟).ρ0 a * (𝓟).ρ1 (𝓟).y ^ k = (𝓟).ρ1 m') :
    haveI := (𝓥).hW0; haveI := (𝓥).hW0'
    letI := NodeEtaleGlue.awayAlg (W := (𝓥).W0) (C := TateGlue1.Xn ϖ 𝒯0 B₀ n) (𝓥).x0
    letI := NodeEtaleGlue.awayAlg (W := (𝓥).W0) (C := TateGlue1.Xn ϖ 𝒯 B₁ n) (𝓥).x1
    ωFF n (algebraMap (TateGlue1.Xn ϖ 𝒯0 B₀ n) _ (Ideal.Quotient.mk _ a)) *
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n)
          (Localization.Away (algebraMap (𝓘F).B0 (TateGlue1.Xn ϖ 𝒯 B₁ n) (𝓥).x1))
          (algebraMap (𝓘F).B0 (TateGlue1.Xn ϖ 𝒯 B₁ n) (𝓥).x1) ^ k =
      algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) _ (Ideal.Quotient.mk _ m') :=
  bridge1F n a m' k (omegaN_mul_pow_of_L hρ n a m' k (L_eq_of_P hρ a m' k h))

local notation "𝓢𝓒" => (systemCusp hκ rfl hε (TateS5.θ_ϖ hker) (piP hϖ hker hκ hε h3 hE hqM hq hM'
  hM'k hK hζ hL hBn hunr₁ τ)
      (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (𝓢p) (NeZero.ne m)
          (𝓢c)
      (isUnit_of_θ_ne_zero hϖ hker) (𝓞))

set_option maxHeartbeats 4000000 in
-- instantiating the generic G5 at the Tate data
/-- **MR12 S6: the M2 lift of a tame cover of the Tate curve is the normalisation.** For the data
of `TateS5` (a tame Galois cover `L` of the function field of the Tate model), every
algebraization `(N, BN, α)` of the adic system `systemCusp … (sp) (sc) (om)` (e.g. the one of
`TateS5.liftCusp_tame`) is isomorphic as a chart algebra to `P_L = (B₀, B₁)`, the normalisations
of the charts `T0`, `T1` in `L` (`twoChartL`). -/
theorem lift_iso_normalisation [IsAdicComplete (Ideal.span {ϖ}) O]
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((𝓢𝓒).M n)}
    {BN : ProjectiveLine.ChartModule.AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hαc : ∀ a b (h : a ≤ b), ((𝓢𝓒).tr h).comp (α b) = α a)
    (hBN : ∀ n, BN.IsHom ((𝓢𝓒).alg n) (α n)) :
    ∃ (γ : ProjectiveLine.ChartModule.Hom (𝓟).chartModule N)
      (δ : ProjectiveLine.ChartModule.Hom N (𝓟).chartModule),
      γ.comp δ = ProjectiveLine.ChartModule.Hom.id N ∧
      δ.comp γ = ProjectiveLine.ChartModule.Hom.id (𝓟).chartModule ∧
      (𝓟).algStr.IsHom BN γ ∧ BN.IsHom (𝓟).algStr δ := by
  haveI : IsAdicComplete (Ideal.span {(𝓥).ϖ}) O :=
    inferInstanceAs (IsAdicComplete (Ideal.span {ϖ}) O)
  haveI := finite_B₁ hϖ hker hκ hε h3 hE K L B₁
  haveI := finite_B₀ hϖ hker hκ hε h3 hE hb₆ K L hρ B₁ B₀ Bc hBc
  haveI := finite_x0L L hρ B₀ B₁
  haveI := finite_x1L L hρ B₀ B₁
  exact (𝓥).exists_iso_of_cuspLevelsW (isUnit_of_θ_ne_zero hϖ hker) (𝓓V) (𝓒)
    (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerRII := fun l ↦ inferInstanceAs
      (IsScalarTower ℛ (EtaleTower.Tn ϖ ℛ (l + 1)) (EtaleTower.Tn ϖ ℛ l)))
    rfl HEq.rfl rfl (𝓟) (eqFam hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (X0 :=
        TateGlue1.Xn ϖ 𝒯0 B₀)
    (CuspTower.XmapC ϖ B₀) (ωFF) (tC (B₀ := B₀) hBc)
    (fun n ↦ CuspTower.toTensorC_algebraMap ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (fun n ↦ CuspTower.isLocalization_toTensorC ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (ρXF) (ρX0 (B₀ := B₀) hker) (hρV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ
        hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (fun n ↦ EtaleTower.hJ hker.le n) (hψ1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL
        hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) (hx1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (hω0 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) (q0FF) (fun _ _ ↦ rfl) (q1FF) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦
          rfl)
    (hWF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (fun n x ↦ CuspTower.toTensorC_succ ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n x)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ Ideal.Quotient.mk_surjective)
    (fun _ ↦ Ideal.Quotient.mk_surjective) (hk0F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ
        hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) (hk1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (hSF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) hα hαc hBN

/-- **The base map of `VF`**: the Tate model maps to the charts of `VF` by the identities
(`TateGlue0.baseMapP`). -/
def bmF : NodeEtaleGlue.Overlap.BaseMap (𝓥) (TateTwoChart.twoChart (ε * ϖ ^ m) b₄ t κ) :=
  baseMapP hκ rfl hε (TateS5.θ_ϖ hker) (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn
      hunr₁ τ) (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (𝓢p)
    (NeZero.ne m) (𝓢c).C0 (𝓞) ((𝓓).piece hθ.out (isUnit_of_θ_ne_zero hϖ hker))

set_option maxHeartbeats 4000000 in
-- instantiating the generic G5 at the Tate data
/-- **MR12 S6 with the structure maps: the M2 lift of a tame cover of the Tate curve is the
normalisation over the Tate model.** As `lift_iso_normalisation`, and the isomorphism
`γ : P_L ≅ N` sends the structure map `toNormL` of `P_L` to any structure map `ψ` of the lift
reducing to the structure maps `structureMapsCusp` of the levels (e.g. the one of
`TateS5.liftCusp_tame`). For the data
of `TateS5` (a tame Galois cover `L` of the function field of the Tate model), every
algebraization `(N, BN, α)` of the adic system `systemCusp … (sp) (sc) (om)` (e.g. the one of
`TateS5.liftCusp_tame`) is isomorphic as a chart algebra to `P_L = (B₀, B₁)`, the normalisations
of the charts `T0`, `T1` in `L` (`twoChartL`). -/
theorem lift_iso_normalisation_base [IsAdicComplete (Ideal.span {ϖ}) O]
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((𝓢𝓒).M n)}
    {BN : ProjectiveLine.ChartModule.AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hαc : ∀ a b (h : a ≤ b), ((𝓢𝓒).tr h).comp (α b) = α a)
    (hBN : ∀ n, BN.IsHom ((𝓢𝓒).alg n) (α n))
    {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart (ε * ϖ ^ m) b₄ t κ).chartModule N}
    (hψα : ∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ rfl hε (TateS5.θ_ϖ hker)
      (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
      (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (𝓢p)
      (NeZero.ne m) (isUnit_of_θ_ne_zero hϖ hker) (𝓢c) (𝓞) n) :
    ∃ (γ : ProjectiveLine.ChartModule.Hom (𝓟).chartModule N)
      (δ : ProjectiveLine.ChartModule.Hom N (𝓟).chartModule),
      γ.comp δ = ProjectiveLine.ChartModule.Hom.id N ∧
      δ.comp γ = ProjectiveLine.ChartModule.Hom.id (𝓟).chartModule ∧
      (𝓟).algStr.IsHom BN γ ∧ BN.IsHom (𝓟).algStr δ ∧
      γ.comp (toNormL L hρ B₀ B₁).toHom = ψ := by
  haveI : IsAdicComplete (Ideal.span {(𝓥).ϖ}) O :=
    inferInstanceAs (IsAdicComplete (Ideal.span {ϖ}) O)
  haveI := finite_B₁ hϖ hker hκ hε h3 hE K L B₁
  haveI := finite_B₀ hϖ hker hκ hε h3 hE hb₆ K L hρ B₁ B₀ Bc hBc
  haveI := finite_x0L L hρ B₀ B₁
  haveI := finite_x1L L hρ B₀ B₁
  haveI := TateTwoChart.finite_x0 (ε * ϖ ^ m) b₄ t κ
  haveI := TateTwoChart.finite_x1 (ε * ϖ ^ m) b₄ t κ
  exact (𝓥).exists_iso_of_cuspLevelsW_base (isUnit_of_θ_ne_zero hϖ hker) (𝓓V) (𝓒)
    (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerRII := fun l ↦ inferInstanceAs
      (IsScalarTower ℛ (EtaleTower.Tn ϖ ℛ (l + 1)) (EtaleTower.Tn ϖ ℛ l)))
    rfl HEq.rfl rfl (𝓟) (eqFam hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (X0 :=
        TateGlue1.Xn ϖ 𝒯0 B₀)
    (CuspTower.XmapC ϖ B₀) (ωFF) (tC (B₀ := B₀) hBc)
    (fun n ↦ CuspTower.toTensorC_algebraMap ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (fun n ↦ CuspTower.isLocalization_toTensorC ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (ρXF) (ρX0 (B₀ := B₀) hker) (hρV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ
        hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (fun n ↦ EtaleTower.hJ hker.le n) (hψ1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL
        hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) (hx1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (hω0 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) (q0FF) (fun _ _ ↦ rfl) (q1FF) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦
          rfl)
    (hWF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (bmF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀)
    (toNormL L hρ B₀ B₁) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun n x ↦ CuspTower.toTensorC_succ ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n x)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ Ideal.Quotient.mk_surjective)
    (fun _ ↦ Ideal.Quotient.mk_surjective) (hk0F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ
        hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) (hk1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀)
    (hSF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
      hBc hunr₁ hunr₀ τ φ₀) hα hαc hBN hψα

end Data
end
end TateS6
end SemistableReduction
