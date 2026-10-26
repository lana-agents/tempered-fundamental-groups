/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TwoChartNormalisation
import TemperedFundamentalGroups.SemistableReduction.TateChartFinite
import TemperedFundamentalGroups.SemistableReduction.TateS5

/-!
# The normalisation of the Tate model in a tame cover as two-chart rings (MR12 S6)

Let `T0`, `T1` be the charts of the Tate model with overlap `T01 = T1[1/h']`
(`TateTwoChart.twoChart`), `L` a field receiving them compatibly (`hρ`), and `B₀`, `B₁` the
normalisations of `T0`, `T1` in `L`. Then (instances of `TwoChartNorm`):

* **`TateS6.twoChartL`**: `P_L = (B₀, B₁)` as two-chart rings over `O` (overlap: the
  normalisation of `T01` in `L`), and **`TateS6.toNormL`**: the structure map from the Tate model;
* **`TateS6.finite_x0L`**, **`TateS6.finite_x1L`**: the charts of `P_L` are finite over `O[X]`
  if `B₀`, `B₁` are finite over `T0`, `T1`;
* **`TateS6.finite_B₁`**: `B₁` is finite over `T1` (`T1` is an integrally closed Noetherian
  domain with fraction field `K`, `L / K` finite Galois);
* **`TateS6.finite_B₀`**: `B₀` is finite over `T0`, by the two localizations `T0[1/h] = T01`
  (where `B₀[1/h] = B₁[1/h']`) and `T0[1/(1 + h)] = Rc` (where `B₀[1/(1 + h)] = Bc` is the
  normalisation of the integrally closed cusp chart `Rc`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateS6

open TateTwoChart

noncomputable section

/-- The restriction `T1 → T01` is compatible with the maps to `L`. -/
lemma h1T {O : Type u} [CommRing O] {π b₄ t κ : O} (L : Type u) [Field L]
    [Algebra (T1 π b₄ t κ) L] [Algebra (T01 π b₄ t κ) L]
    [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L] (a : T1 π b₄ t κ) :
    algebraMap (T01 π b₄ t κ) L (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) a) =
      algebraMap (T1 π b₄ t κ) L a :=
  (IsScalarTower.algebraMap_apply _ _ _ a).symm

/-- **The normalisation `P_L = (B₀, B₁)` of the Tate model in `L`** as two-chart rings over
`O`. -/
def twoChartL {O : Type u} [CommRing O] {π b₄ t κ : O} (L : Type u) [Field L]
    [iT0 : Algebra (T0 π b₄ t κ) L] [iT1 : Algebra (T1 π b₄ t κ) L]
    [iT01 : Algebra (T01 π b₄ t κ) L]
    [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁]
    [iB₀ : Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [sB₀ : IsScalarTower (T0 π b₄ t κ) B₀ L]
    [cB₀ : IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [iB₁ : Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [sB₁ : IsScalarTower (T1 π b₄ t κ) B₁ L]
    [cB₁ : IsIntegralClosure B₁ (T1 π b₄ t κ) L] :
    ProjectiveLine.TwoChartRings O :=
  letI : Algebra (twoChart π b₄ t κ).R0 L := iT0
  letI : Algebra (twoChart π b₄ t κ).R1 L := iT1
  letI : Algebra (twoChart π b₄ t κ).R01 L := iT01
  letI : Algebra (twoChart π b₄ t κ).R0 B₀ := iB₀
  letI : Algebra (twoChart π b₄ t κ).R1 B₁ := iB₁
  haveI : IsScalarTower (twoChart π b₄ t κ).R0 B₀ L := sB₀
  haveI : IsScalarTower (twoChart π b₄ t κ).R1 B₁ L := sB₁
  haveI : IsIntegralClosure B₀ (twoChart π b₄ t κ).R0 L := cB₀
  haveI : IsIntegralClosure B₁ (twoChart π b₄ t κ).R1 L := cB₁
  TwoChartNorm.twoChart (D := twoChart π b₄ t κ) B₀ B₁ hρ (h1T L)

/-- **The structure map** from the Tate model to its normalisation `P_L`. -/
def toNormL {O : Type u} [CommRing O] {π b₄ t κ : O} (L : Type u) [Field L]
    [iT0 : Algebra (T0 π b₄ t κ) L] [iT1 : Algebra (T1 π b₄ t κ) L]
    [iT01 : Algebra (T01 π b₄ t κ) L]
    [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁]
    [iB₀ : Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [sB₀ : IsScalarTower (T0 π b₄ t κ) B₀ L]
    [cB₀ : IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [iB₁ : Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [sB₁ : IsScalarTower (T1 π b₄ t κ) B₁ L]
    [cB₁ : IsIntegralClosure B₁ (T1 π b₄ t κ) L] :
    TwoChartMap (twoChart π b₄ t κ) (twoChartL L hρ B₀ B₁) :=
  letI : Algebra (twoChart π b₄ t κ).R0 L := iT0
  letI : Algebra (twoChart π b₄ t κ).R1 L := iT1
  letI : Algebra (twoChart π b₄ t κ).R01 L := iT01
  letI : Algebra (twoChart π b₄ t κ).R0 B₀ := iB₀
  letI : Algebra (twoChart π b₄ t κ).R1 B₁ := iB₁
  haveI : IsScalarTower (twoChart π b₄ t κ).R0 B₀ L := sB₀
  haveI : IsScalarTower (twoChart π b₄ t κ).R1 B₁ L := sB₁
  haveI : IsIntegralClosure B₀ (twoChart π b₄ t κ).R0 L := cB₀
  haveI : IsIntegralClosure B₁ (twoChart π b₄ t κ).R1 L := cB₁
  TwoChartNorm.toNorm (D := twoChart π b₄ t κ) B₀ B₁ hρ (h1T L)

lemma toNormL_f0 {O : Type u} [CommRing O] {π b₄ t κ : O} (L : Type u) [Field L]
    [Algebra (T0 π b₄ t κ) L] [Algebra (T1 π b₄ t κ) L] [Algebra (T01 π b₄ t κ) L]
    [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁]
    [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower (T0 π b₄ t κ) B₀ L]
    [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower (T1 π b₄ t κ) B₁ L]
    [IsIntegralClosure B₁ (T1 π b₄ t κ) L] (a : T0 π b₄ t κ) :
    @Eq B₀ ((toNormL L hρ B₀ B₁).f0 a) (algebraMap (T0 π b₄ t κ) B₀ a) :=
  rfl

lemma toNormL_f1 {O : Type u} [CommRing O] {π b₄ t κ : O} (L : Type u) [Field L]
    [Algebra (T0 π b₄ t κ) L] [Algebra (T1 π b₄ t κ) L] [Algebra (T01 π b₄ t κ) L]
    [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁]
    [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower (T0 π b₄ t κ) B₀ L]
    [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower (T1 π b₄ t κ) B₁ L]
    [IsIntegralClosure B₁ (T1 π b₄ t κ) L] (a : T1 π b₄ t κ) :
    @Eq B₁ ((toNormL L hρ B₀ B₁).f1 a) (algebraMap (T1 π b₄ t κ) B₁ a) :=
  rfl

/-- **The first chart of `P_L` is finite over `O[X]`** if `B₀` is finite over `T0`. -/
theorem finite_x0L {O : Type u} [CommRing O] {π b₄ t κ : O} (L : Type u) [Field L]
    [iT0 : Algebra (T0 π b₄ t κ) L] [iT1 : Algebra (T1 π b₄ t κ) L]
    [iT01 : Algebra (T01 π b₄ t κ) L]
    [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁]
    [iB₀ : Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [sB₀ : IsScalarTower (T0 π b₄ t κ) B₀ L]
    [cB₀ : IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [iB₁ : Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [sB₁ : IsScalarTower (T1 π b₄ t κ) B₁ L]
    [cB₁ : IsIntegralClosure B₁ (T1 π b₄ t κ) L] [fB₀ : Module.Finite (T0 π b₄ t κ) B₀] :
    Module.Finite O[X] (Module.AEval' (twoChartL L hρ B₀ B₁).chartModule.x0) :=
  letI : Algebra (twoChart π b₄ t κ).R0 L := iT0
  letI : Algebra (twoChart π b₄ t κ).R1 L := iT1
  letI : Algebra (twoChart π b₄ t κ).R01 L := iT01
  letI : Algebra (twoChart π b₄ t κ).R0 B₀ := iB₀
  letI : Algebra (twoChart π b₄ t κ).R1 B₁ := iB₁
  haveI : IsScalarTower (twoChart π b₄ t κ).R0 B₀ L := sB₀
  haveI : IsScalarTower (twoChart π b₄ t κ).R1 B₁ L := sB₁
  haveI : IsIntegralClosure B₀ (twoChart π b₄ t κ).R0 L := cB₀
  haveI : IsIntegralClosure B₁ (twoChart π b₄ t κ).R1 L := cB₁
  haveI : Module.Finite (twoChart π b₄ t κ).R0 B₀ := fB₀
  TwoChartNorm.finite_x0 (D := twoChart π b₄ t κ) B₀ B₁ hρ (h1T L)
    (TateGlue0.finite_aeval_h0 (π := π) (b₄ := b₄) (t := t) (κ := κ))

/-- **The second chart of `P_L` is finite over `O[X]`** if `B₁` is finite over `T1`. -/
theorem finite_x1L {O : Type u} [CommRing O] {π b₄ t κ : O} (L : Type u) [Field L]
    [iT0 : Algebra (T0 π b₄ t κ) L] [iT1 : Algebra (T1 π b₄ t κ) L]
    [iT01 : Algebra (T01 π b₄ t κ) L]
    [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁]
    [iB₀ : Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [sB₀ : IsScalarTower (T0 π b₄ t κ) B₀ L]
    [cB₀ : IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [iB₁ : Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [sB₁ : IsScalarTower (T1 π b₄ t κ) B₁ L]
    [cB₁ : IsIntegralClosure B₁ (T1 π b₄ t κ) L] [fB₁ : Module.Finite (T1 π b₄ t κ) B₁] :
    Module.Finite O[X] (Module.AEval' (twoChartL L hρ B₀ B₁).chartModule.x1) :=
  letI : Algebra (twoChart π b₄ t κ).R0 L := iT0
  letI : Algebra (twoChart π b₄ t κ).R1 L := iT1
  letI : Algebra (twoChart π b₄ t κ).R01 L := iT01
  letI : Algebra (twoChart π b₄ t κ).R0 B₀ := iB₀
  letI : Algebra (twoChart π b₄ t κ).R1 B₁ := iB₁
  haveI : IsScalarTower (twoChart π b₄ t κ).R0 B₀ L := sB₀
  haveI : IsScalarTower (twoChart π b₄ t κ).R1 B₁ L := sB₁
  haveI : IsIntegralClosure B₀ (twoChart π b₄ t κ).R0 L := cB₀
  haveI : IsIntegralClosure B₁ (twoChart π b₄ t κ).R1 L := cB₁
  haveI : Module.Finite (twoChart π b₄ t κ).R1 B₁ := fB₁
  TwoChartNorm.finite_x1 (D := twoChart π b₄ t κ) B₀ B₁ hρ (h1T L)
    (TateGlue0.finite_aeval_h1 (π := π) (b₄ := b₄) (t := t) (κ := κ))

/-- **`B₁` is finite over `T1`**: `T1` is an integrally closed Noetherian domain with fraction
field `K` and `L / K` is finite separable. -/
theorem finite_B₁ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {k : Type u} [Field k] {θ : O →+* k} [Fact (Function.Surjective θ)]
    {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m] (hϖ : Irreducible ϖ)
    (hker : RingHom.ker θ = Ideal.span {ϖ}) (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1)
    (h3 : (3 : O) ≠ 0) (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
    [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L]
    (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L]
    [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L] [IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L] :
    Module.Finite (T1 (ε * ϖ ^ m) b₄ t κ) B₁ := by
  haveI := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  haveI := TateGlue1.isIntegrallyClosed_T1' hϖ hker hκ hε h3 hE
  exact IsIntegralClosure.finite (T1 (ε * ϖ ^ m) b₄ t κ) K L B₁

/-- `(h, 1 + h) = (1)` in `T0`. -/
lemma span_h0_c0 {O : Type u} [CommRing O] (π b₄ t κ : O) :
    Ideal.span {h0 π b₄ t κ, TateGlue0.c0 π b₄ t κ} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : T0 π b₄ t κ) = TateGlue0.c0 π b₄ t κ - h0 π b₄ t κ := by
    simp [TateGlue0.c0]
  rw [h]
  exact sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))

/-- **`B₀` is finite over `T0`**: over `T0[1/h] = T01` it is `B₁[1/h']` (finite as `B₁` is
finite over `T1`), over `T0[1/(1 + h)] = Rc` it is `Bc`, the normalisation of the integrally
closed Noetherian domain `Rc` (fraction field `K`, `L / K` finite Galois). -/
theorem finite_B₀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {k : Type u} [Field k] {θ : O →+* k} [Fact (Function.Surjective θ)]
    {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m] (hϖ : Irreducible ϖ)
    (hker : RingHom.ker θ = Ideal.span {ϖ}) (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1)
    (h3 : (3 : O) ≠ 0) (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    (hb₆ : IsUnit b₆)
    (K : Type u) [Field K] [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K]
    [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) K L]
    [iT0 : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) L]
    [IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) L]
    [iT1 : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L] [iT01 : Algebra (T01 (ε * ϖ ^ m) b₄ t κ) L]
    [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t κ) L]
    (hρ : ∀ x, algebraMap (T01 (ε * ϖ ^ m) b₄ t κ) L (rho0 (ε * ϖ ^ m) b₄ t κ x) =
      algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) L x)
    (B₁ : Type u) [CommRing B₁] [iB₁ : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L]
    [sB₁ : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L]
    [cB₁ : IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L]
    [fB₁ : Module.Finite (T1 (ε * ϖ ^ m) b₄ t κ) B₁]
    (B₀ : Type u) [CommRing B₀] [iB₀ : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) B₀] [Algebra B₀ L]
    [sB₀ : IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) B₀ L]
    [cB₀ : IsIntegralClosure B₀ (T0 (ε * ϖ ^ m) b₄ t κ) L]
    (Bc : Type u) [CommRing Bc] [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) Bc] [Algebra Bc L]
    [IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) Bc L] [Algebra B₀ Bc] [IsScalarTower B₀ Bc L]
    [lBc : IsLocalization.Away
      (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ))
      Bc]
    (hBc : ∀ x, algebraMap (RcT (ε * ϖ ^ m) b₄ t κ) Bc
      (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) x) =
        algebraMap B₀ Bc (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ x)) :
    Module.Finite (T0 (ε * ϖ ^ m) b₄ t κ) B₀ := by
  have hεu : IsUnit ε := .of_mul_eq_one_right εi hε
  haveI := TateCuspCov.isDomain_Rc' hϖ rfl hεu h3 hE hκ
  haveI := TateCuspCov.isIntegrallyClosed_Rc' hϖ hker rfl (Nat.pos_of_neZero m) hεu h3 hE hκ hb₆
  haveI := TateCuspCov.isIntegralClosure_B (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ) L Bc B₀
  haveI : Module.Finite (RcT (ε * ϖ ^ m) b₄ t κ) Bc :=
    IsIntegralClosure.finite (RcT (ε * ϖ ^ m) b₄ t κ) K L Bc
  have hloc : IsLocalization.Away (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) :=
    inferInstance
  letI : Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R0 L := iT0
  letI : Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R1 L := iT1
  letI : Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R01 L := iT01
  letI : Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R0 B₀ := iB₀
  letI : Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R1 B₁ := iB₁
  haveI : IsScalarTower (twoChart (ε * ϖ ^ m) b₄ t κ).R0 B₀ L := sB₀
  haveI : IsScalarTower (twoChart (ε * ϖ ^ m) b₄ t κ).R1 B₁ L := sB₁
  haveI : IsIntegralClosure B₀ (twoChart (ε * ϖ ^ m) b₄ t κ).R0 L := cB₀
  haveI : IsIntegralClosure B₁ (twoChart (ε * ϖ ^ m) b₄ t κ).R1 L := cB₁
  haveI : Module.Finite (twoChart (ε * ϖ ^ m) b₄ t κ).R1 B₁ := fB₁
  letI : Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R0 (RcT (ε * ϖ ^ m) b₄ t κ) :=
    inferInstanceAs (Algebra (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ))
  exact TwoChartNorm.finite_B₀ (D := twoChart (ε * ϖ ^ m) b₄ t κ) B₀ B₁ hρ (h1T L)
    (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (span_h0_c0 _ _ _ _) (Rc := RcT (ε * ϖ ^ m) b₄ t κ)
    hloc (Bc := Bc) lBc (fun r ↦ (hBc r).symm)

end

end TateS6

end SemistableReduction
