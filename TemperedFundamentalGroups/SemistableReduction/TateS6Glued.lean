/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Lift
import TemperedFundamentalGroups.SemistableReduction.AlgStrRingHom01
import TemperedFundamentalGroups.SemistableReduction.TateAffineGlueNorm

/-!
# The glued generic fibre of the lift is the `E ∖ {0}`-algebra of `L` (MR12 S6, G6)

For the data of `TateS5` (a tame Galois cover `L` of the function field of the Tate model) and an
algebraization `(N, BN, α)` of `systemCusp … (sp) (sc) (om)` with a structure map `ψ` from the
Tate model reducing to the structure maps of the levels (e.g. the lift of `TateS5.liftCusp_tame`):

* `TateS6.varpi_ne_zero_L`, `w1_ne_zero_L`, `varpi_z0_ne_zero_L`: `ϖ`, `w`, `ϖ z` are nonzero in
  `L`; **`TateS6.algKL`**: the coordinate ring `A[1/ϖ]` of `E ∖ {0}` maps to `L` (through
  `T0[1/(ϖ z)]`);
* **`TateS6.gluedK_isNorm`** (G6): the glued generic fibre `TateAffine.gluedK` of the lift over
  `E ∖ {0}` is isomorphic as an `A[1/ϖ]`-algebra to the integral closure of `A[1/ϖ]` in `L`, the
  `E ∖ {0}`-algebra of `L` (`TateS6.GluedKIsNorm`). Proof: `lift_iso_normalisation_base` gives
  `δ : N ≅ P_L` with `δ ∘ ψ = toNormL`, so the charts of the lift embed into `L` as the
  normalisations `B₀`, `B₁`; then `TateAffine.gluedKNorm`.
-/

universe u
open Module Polynomial
namespace SemistableReduction

namespace TateS6
open TateS5 TateTwoChart TateTwoChartNode TateGlue0 TateLevel TateAffine
open TensorProduct
open AdmissibleLift (J)
open FormalKummer (Cs)

noncomputable section

section Field

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] {π b₄ b₆ t κ ϖ ε εi : O} {m : ℕ}
  (L : Type u) [Field L] [Algebra (T0 π b₄ t κ) L] [Algebra (T1 π b₄ t κ) L]
  [Algebra (T01 π b₄ t κ) L] [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
  (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
  (hinj : Function.Injective (algebraMap (T1 π b₄ t κ) L))

include hinj in
/-- `ϖ ≠ 0` in `L`. -/
lemma varpi_ne_zero_L (hϖ : ϖ ≠ 0) :
    algebraMap (T1 π b₄ t κ) L (algebraMap O (T1 π b₄ t κ) ϖ) ≠ 0 := fun h ↦
  algebraMap_ϖ_T1_ne_zero hϖ (hinj (h.trans (map_zero _).symm))

include hinj in
/-- `w ≠ 0` in `L` (`w (w² + …) = κ π` with `κ`, `ε` units and `π = ε ϖᵐ`). -/
lemma w1_ne_zero_L (hϖ : ϖ ≠ 0) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
    (hε : εi * ε = 1) : algebraMap (T1 π b₄ t κ) L (w1 π b₄ t κ) ≠ 0 := by
  set g : O →+* L := (algebraMap (T1 π b₄ t κ) L).comp (algebraMap O (T1 π b₄ t κ))
  have e : algebraMap O (T1 π b₄ t κ) (κ * π) = w1 π b₄ t κ * (w1 π b₄ t κ ^ 2 +
      algebraMap O _ κ * (algebraMap O _ (2 * t) * h1 π b₄ t κ +
        algebraMap O _ (t - π * b₄)) * w1 π b₄ t κ +
      algebraMap O _ κ * (h1 π b₄ t κ ^ 2 + h1 π b₄ t κ)) := by
    linear_combination (-1 : T1 π b₄ t κ) * eq1 π b₄ t κ
  have hκ0 : g κ ≠ 0 := left_ne_zero_of_mul_eq_one (by rw [← map_mul, hκ, map_one])
  have hε0 : g ε ≠ 0 := right_ne_zero_of_mul_eq_one (by rw [← map_mul, hε, map_one])
  have hϖ0 : g ϖ ≠ 0 := varpi_ne_zero_L L hinj hϖ
  have hg : g (κ * π) ≠ 0 := by
    rw [hπ, map_mul, map_mul, map_pow]
    exact mul_ne_zero hκ0 (mul_ne_zero hε0 (pow_ne_zero _ hϖ0))
  intro h
  apply hg
  change algebraMap (T1 π b₄ t κ) L (algebraMap O (T1 π b₄ t κ) (κ * π)) = 0
  rw [e, map_mul, h, zero_mul]

include hρ hinj in
/-- `ϖ z ≠ 0` in `L` (`ρ₀ z = w h'⁻¹` on the overlap). -/
lemma varpi_z0_ne_zero_L (hϖ : ϖ ≠ 0) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
    (hε : εi * ε = 1) :
    algebraMap (T0 π b₄ t κ) L (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ) ≠ 0 := by
  have e1 : algebraMap (T01 π b₄ t κ) L (algebraMap O (T01 π b₄ t κ) ϖ) =
      algebraMap (T1 π b₄ t κ) L (algebraMap O (T1 π b₄ t κ) ϖ) := by
    rw [IsScalarTower.algebraMap_apply O (T1 π b₄ t κ) (T01 π b₄ t κ),
      ← IsScalarTower.algebraMap_apply (T1 π b₄ t κ) (T01 π b₄ t κ) L]
  have e2 : algebraMap (T01 π b₄ t κ) L (wo π b₄ t κ) = algebraMap (T1 π b₄ t κ) L (w1 π b₄ t κ) :=
    (IsScalarTower.algebraMap_apply (T1 π b₄ t κ) (T01 π b₄ t κ) L _).symm
  rw [← hρ, map_mul, map_mul, AlgHom.commutes, rho0_z0, map_mul, e1, e2]
  have hu : algebraMap (T01 π b₄ t κ) L (hinv π b₄ t κ) ≠ 0 :=
    right_ne_zero_of_mul_eq_one (by rw [← map_mul, h1_mul_hinv, map_one])
  exact mul_ne_zero (varpi_ne_zero_L L hinj hϖ)
    (mul_ne_zero (w1_ne_zero_L L hinj hϖ hκ hπ hε) hu)

end Field

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

local notation "𝒯0" => T0 (ε * ϖ ^ m) b₄ t κ

local notation "𝓢c" => sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "𝓢p" => sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝓞" => om hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "𝓟" => twoChartL L hρ B₀ B₁

local notation "𝓢𝓒" => (systemCusp hκ rfl hε (TateS5.θ_ϖ hker) (piP hϖ hker hκ hε h3 hE hqM hq hM'
  hM'k hK hζ hL hBn hunr₁ τ)
      (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (𝓢p) (NeZero.ne m)
          (𝓢c)
      (isUnit_of_θ_ne_zero hϖ hker) (𝓞))

variable (K L) in
include K in
/-- `T1 → L` is injective (`T1 → K` is the fraction field). -/
lemma injective_T1L : Function.Injective (algebraMap 𝒯 L) := by
  rw [IsScalarTower.algebraMap_eq 𝒯 K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective 𝒯 K)

variable (K L) in
include hϖ hκ hε hρ K in
/-- `ϖ z ≠ 0` in `L`. -/
lemma varpi_z0_ne_zero_L' :
    algebraMap 𝒯0 L (algebraMap O 𝒯0 ϖ * z0 (ε * ϖ ^ m) b₄ t κ) ≠ 0 :=
  varpi_z0_ne_zero_L L hρ (injective_T1L K L) hϖ.ne_zero hκ rfl hε

variable (K L) in
/-- `T0[1/(ϖ z)] → L`. -/
abbrev liftT0K : T0K (ε * ϖ ^ m) b₄ t κ ϖ →+* L :=
  IsLocalization.Away.lift (algebraMap O 𝒯0 ϖ * z0 (ε * ϖ ^ m) b₄ t κ)
    (varpi_z0_ne_zero_L' hϖ hκ hε K L hρ).isUnit

variable (K L) in
/-- **The `E ∖ {0}`-algebra structure of `L`**: `A[1/ϖ] → T0[1/(ϖ z)] → L`. -/
abbrev algKL : Algebra (AK (ε * ϖ ^ m) b₄ b₆ ϖ) L :=
  ((liftT0K hϖ hκ hε K L hρ).comp
    (f0K (ε * ϖ ^ m) b₄ ϖ hκ : AK (ε * ϖ ^ m) b₄ b₆ ϖ →+* T0K (ε * ϖ ^ m) b₄ t κ ϖ)).toAlgebra

variable (K L) in
set_option linter.defProp false in
/-- **G6 as a proposition**: the glued generic fibre of a chart algebra `BN` with structure map
`ψ` over `E ∖ {0}` is isomorphic to the integral closure of `A[1/ϖ]` in `L` (`algKL`). -/
def GluedKIsNorm {N : ProjectiveLine.ChartModule O} {BN : ProjectiveLine.ChartModule.AlgStr N}
    {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart (ε * ϖ ^ m) b₄ t κ).chartModule N}
    (hψ : (TateTwoChart.twoChart (ε * ϖ ^ m) b₄ t κ).algStr.IsHom BN ψ) : Prop :=
  letI := algKL hϖ hκ hε K L hρ
  GluedKNorm b₄ hκ (pi_dvd rfl hε) (hc0_chart hψ) (hc1_chart hψ) L

set_option maxHeartbeats 1000000 in
-- the chart maps of the lift into `L`
/-- **MR12 S6, G6: the glued generic fibre of the lift is the `E ∖ {0}`-algebra of `L`.** For
the data of `TateS5` and an algebraization `(N, BN, α)` of `systemCusp … (sp) (sc) (om)` with a
structure map `ψ` from the Tate model reducing to the structure maps `structureMapsCusp` of the
levels (e.g. the lift of `TateS5.liftCusp_tame`), the glued generic fibre `TateAffine.gluedK` of
`(BN, ψ)` over `E ∖ {0}` is isomorphic as an `A[1/ϖ]`-algebra to the integral closure of
`A[1/ϖ]` in `L`. -/
theorem gluedK_isNorm [IsAdicComplete (Ideal.span {ϖ}) O]
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
    (hψ : (TateTwoChart.twoChart (ε * ϖ ^ m) b₄ t κ).algStr.IsHom BN ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ rfl hε (TateS5.θ_ϖ hker)
      (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
      (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (𝓢p)
      (NeZero.ne m) (isUnit_of_θ_ne_zero hϖ hker) (𝓢c) (𝓞) n) :
    GluedKIsNorm hϖ hκ hε K L hρ hψ := by
  obtain ⟨γ, δ, hγδ, hδγ, -, hδB, hγψ⟩ := lift_iso_normalisation_base hϖ hker hκ hε h3 hE hb₆
    hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀ hα hαc hBN hψα
  have hδψ : δ.comp ψ = (toNormL L hρ B₀ B₁).toHom := by
    rw [← hγψ, ← ProjectiveLine.ChartModule.Hom.comp_assoc, hδγ,
      ProjectiveLine.ChartModule.Hom.id_comp]
  letI := algKL hϖ hκ hε K L hρ
  let j0 : BN.Ring0 →+* L := (algebraMap B₀ L).comp
    ((ProjectiveLine.TwoChartRings.ring0Equiv (𝓟)).toRingHom.comp hδB.ringHom0)
  let j1 : BN.Ring1 →+* L := (algebraMap B₁ L).comp
    ((ProjectiveLine.TwoChartRings.ring1Equiv (𝓟)).toRingHom.comp hδB.ringHom1)
  let j01 : BN.Ring01 →+* L := (integralClosure (T01 (ε * ϖ ^ m) b₄ t κ) L).val.toRingHom.comp
    ((ProjectiveLine.TwoChartRings.ring01Equiv (𝓟)).toRingHom.comp hδB.ringHom01')
  have hj0ι : ∀ a, j0 (iota0 hψ a) = algebraMap 𝒯0 L a := fun a ↦
    show algebraMap B₀ L (δ.f0 (ψ.f0 a)) = _ from
      (congrArg (algebraMap B₀ L) (ProjectiveLine.ChartModule.Hom.f0_eq_of_eq hδψ a)).trans
        (IsScalarTower.algebraMap_apply 𝒯0 B₀ L a).symm
  have hj1ι : ∀ a, j1 (iota1 hψ a) = algebraMap 𝒯 L a := fun a ↦
    show algebraMap B₁ L (δ.f1 (ψ.f1 a)) = _ from
      (congrArg (algebraMap B₁ L) (ProjectiveLine.ChartModule.Hom.f1_eq_of_eq hδψ a)).trans
        (IsScalarTower.algebraMap_apply 𝒯 B₁ L a).symm
  have hj0 : ∀ a, j01 (BN.r0Hom a) = j0 a := fun a ↦
    congrArg (fun z ↦ (integralClosure (T01 (ε * ϖ ^ m) b₄ t κ) L).val.toRingHom
      (ProjectiveLine.TwoChartRings.ring01Equiv (𝓟) z)) (hδB.ringHom01'_r0Hom a)
  have hj1 : ∀ a, j01 (BN.r1Hom a) = j1 a := fun a ↦
    congrArg (fun z ↦ (integralClosure (T01 (ε * ϖ ^ m) b₄ t κ) L).val.toRingHom
      (ProjectiveLine.TwoChartRings.ring01Equiv (𝓟) z)) (hδB.ringHom01'_r1Hom a)
  have hi0 : Function.Injective j0 :=
    (IsIntegralClosure.algebraMap_injective B₀ 𝒯0 L).comp
      ((ProjectiveLine.TwoChartRings.ring0Equiv (𝓟)).injective.comp
        (Function.LeftInverse.injective (g := γ.f0)
          (ProjectiveLine.ChartModule.Hom.f0_eq_of_eq hγδ)))
  have hi1 : Function.Injective j1 :=
    (IsIntegralClosure.algebraMap_injective B₁ 𝒯 L).comp
      ((ProjectiveLine.TwoChartRings.ring1Equiv (𝓟)).injective.comp
        (Function.LeftInverse.injective (g := γ.f1)
          (ProjectiveLine.ChartModule.Hom.f1_eq_of_eq hγδ)))
  have hi01 : Function.Injective j01 :=
    Subtype.val_injective.comp
      ((ProjectiveLine.TwoChartRings.ring01Equiv (𝓟)).injective.comp
        (Function.LeftInverse.injective (g := γ.f01)
          (ProjectiveLine.ChartModule.Hom.f01_eq_of_eq hγδ)))
  have hϖ0 : j0 (iota0 hψ (algebraMap O 𝒯0 ϖ * z0 (ε * ϖ ^ m) b₄ t κ)) ≠ 0 := by
    rw [hj0ι]
    exact varpi_z0_ne_zero_L' hϖ hκ hε K L hρ
  have hϖ1 : j1 (iota1 hψ (algebraMap O 𝒯 ϖ)) ≠ 0 := by
    rw [hj1ι]
    exact varpi_ne_zero_L L (injective_T1L K L) hϖ.ne_zero
  have hAK : ∀ a : AK (ε * ϖ ^ m) b₄ b₆ ϖ, algebraMap (AK (ε * ϖ ^ m) b₄ b₆ ϖ) L a =
      jA b₄ j0 hϖ0 (iotaA b₄ ϖ (iota0 hψ) (f0K (ε * ϖ ^ m) b₄ ϖ hκ a)) := fun a ↦
    RingHom.congr_fun (IsLocalization.ringHom_ext (S := T0K (ε * ϖ ^ m) b₄ t κ ϖ)
      (Submonoid.powers (algebraMap O 𝒯0 ϖ * z0 (ε * ϖ ^ m) b₄ t κ))
      (j := liftT0K hϖ hκ hε K L hρ)
      (k := (jA b₄ j0 hϖ0).comp (iotaA b₄ ϖ (iota0 hψ))) (RingHom.ext fun x ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
          IsLocalization.Away.lift_eq, iotaA_algebraMap, jA_algebraMap, hj0ι]))
      (f0K (ε * ϖ ^ m) b₄ ϖ hκ a)
  have hcl0 : ∀ x : L, (j0.comp (iota0 hψ)).IsIntegralElem x → x ∈ j0.range := by
    intro x hx
    rw [show j0.comp (iota0 hψ) = algebraMap 𝒯0 L from RingHom.ext hj0ι] at hx
    obtain ⟨b, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := B₀)).1 hx
    exact ⟨γ.f0 b, congrArg (algebraMap B₀ L) (ProjectiveLine.ChartModule.Hom.f0_eq_of_eq hδγ b)⟩
  have hcl1 : ∀ x : L, (j1.comp (iota1 hψ)).IsIntegralElem x → x ∈ j1.range := by
    intro x hx
    rw [show j1.comp (iota1 hψ) = algebraMap 𝒯 L from RingHom.ext hj1ι] at hx
    obtain ⟨b, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := B₁)).1 hx
    exact ⟨γ.f1 b, congrArg (algebraMap B₁ L) (ProjectiveLine.ChartModule.Hom.f1_eq_of_eq hδγ b)⟩
  exact gluedKNorm b₄ hκ (pi_dvd rfl hε) (hc0_chart hψ) (hc1_chart hψ) (hloc0_chart hψ)
    (hloc1_chart hψ) j0 j1 j01 hj0 hj1 hi0 hi1 hi01 hϖ0 hϖ1 hAK hcl0 hcl1 (finite_iota0 hψ)
    (finite_iota1 hψ)

end Data

end

end TateS6

end SemistableReduction
