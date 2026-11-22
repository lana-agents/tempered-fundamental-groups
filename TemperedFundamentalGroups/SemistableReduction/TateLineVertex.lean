/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Decomposition
import TemperedFundamentalGroups.SemistableReduction.TateLineRegular
import TemperedFundamentalGroups.SemistableReduction.TateSpecial1

/-!
# The vertex chart of a Galois Tate cover over the line `ℓ` (MR13 step 7, D1, `V₁` part)

For a tame cover `C : TateS6.Cov …` with Galois group `Gal(C.L/K)` and a component `𝔓` of the
special fibre of the normalisation `C.B₁` over the line `ℓ = {w = 0}` of the Tate chart `T1`
(a prime of `C.B₁` over the generic point `P_ℓ = lineIdeal` of `ℓ`), the **vertex chart**

  `C1 = (C.B₁/𝔓)[1/(h'(h' + 1))]`  over  `R = (T1/P_ℓ)[1/(h'(h' + 1))] ≅ k[h', 1/(h'(h' + 1))]`

(`ComponentChart.C1`, with `P_ℓ` and `h'(h' + 1)` taken in the chart ring `(twoChart …).R1` as
`TateS6.lineP`, `TateS6.glD`, so that the instances of `C` apply) satisfies:

* **`TateS6.etale_line`**: `C.B₁/P_ℓ C.B₁` is étale over `T1/P_ℓ` away from the nodes
  `h'(h' + 1) = 0` (purity, `CovData.etale_quot`, with the regular pairs of
  `TateTwoChart.exists_regular_pair_T1_line`);
* **`TateS6.vertexChart_etale`**, **`vertexChart_finite`**: `C1` is finite étale over `R`;
* **`TateS6.vertexChart_finrank`**: `rank_R C1 = |Stab(𝔓)|` (the decomposition group `Γ_v`);
* **`TateS6.vertexChart_stabilizerHom_bijective`**: `Γ_v ≃ Aut_{T1/P_ℓ}(C.B₁/𝔓)` (trivial inertia).
-/

universe u

open Polynomial
open scoped Pointwise

namespace SemistableReduction

open TateTwoChart TateTwoChartNode TateGlue0

namespace TateS6

noncomputable section

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m]
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
  {hκ : κ * (t ^ 2 - b₆) = 1} (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
  {q e : ℕ} {K : Type u} [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
  [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K]

local notation "𝒯" => T1 (ε * ϖ ^ m) b₄ t κ

set_option quotPrecheck false in
local notation "𝒟" => (TateTwoChart.twoChart (ε * ϖ ^ m) b₄ t κ).R1

omit [IsDomain O] [IsDiscreteValuationRing O] hθ in
include hker in
lemma θϖ : θ ϖ = 0 := by
  rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ

omit [IsDomain O] [IsDiscreteValuationRing O] hθ in
include hker in
lemma θπ : θ (ε * ϖ ^ m) = 0 := by
  rw [map_mul, map_pow, θϖ hker, zero_pow (NeZero.ne m), mul_zero]

/-- The generic point `P_ℓ = lineIdeal` of the line `ℓ`, as an ideal of the chart ring
`(twoChart …).R1 = T1`. -/
def lineP (π b₄ t κ : O) (hπ : θ π = 0) : Ideal (TateTwoChart.twoChart π b₄ t κ).R1 :=
  lineIdeal hπ b₄ t κ

instance lineP_isPrime (π b₄ t κ : O) (hπ : θ π = 0) : (lineP π b₄ t κ hπ).IsPrime :=
  lineIdeal_isPrime _

/-- The closed point `h' = 1` of `ℓ`, as an ideal of the chart ring. -/
def pointP (π b₄ t κ : O) (hπ : θ π = 0) : Ideal (TateTwoChart.twoChart π b₄ t κ).R1 :=
  pointIdeal hπ b₄ t κ

/-- The nodes `h'(h' + 1)` of `ℓ`, as an element of the chart ring. -/
def glD (π b₄ t κ : O) : (TateTwoChart.twoChart π b₄ t κ).R1 :=
  (h1 π b₄ t κ * (h1 π b₄ t κ + 1) : T1 π b₄ t κ)

set_option quotPrecheck false in
/-- `P_ℓ` for the Tate data of the section. -/
local notation "𝓅" => lineP (ε * ϖ ^ m) b₄ t κ (θπ (ε := ε) (m := m) hker)

set_option quotPrecheck false in
/-- The nodes of `ℓ` for the Tate data of the section. -/
local notation "𝓰" => glD (ε * ϖ ^ m) b₄ t κ

omit [IsDomain O] [IsDiscreteValuationRing O] hθ in
lemma mem_lineP_iff (x : 𝒟) : x ∈ 𝓅 ↔ lineHom θ (ε * ϖ ^ m) b₄ t κ (θπ hker) x = 0 :=
  RingHom.mem_ker

omit [IsDomain O] [IsDiscreteValuationRing O] hθ in
lemma algebraMap_mem_lineP : algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) ϖ ∈ 𝓅 :=
  algebraMap_mem_lineIdeal _ (θϖ hker)

omit [IsDomain O] [IsDiscreteValuationRing O] hθ in
lemma w1_mem_lineP : w1 (ε * ϖ ^ m) b₄ t κ ∈ 𝓅 :=
  (mem_lineP_iff hker _).2 (lineHom_root _)

omit [IsDomain O] [IsDiscreteValuationRing O] hθ in
lemma glD_notMem_lineP : 𝓰 ∉ 𝓅 := by
  rw [mem_lineP_iff hker]
  simp only [glD, h1, map_mul, map_add, map_one, lineHom_of, Polynomial.map_X]
  intro h
  have h1 := congrArg (fun p ↦ p.coeff 1) h
  simp [coeff_X, coeff_one] at h1

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- `T1/P_ℓ` is a Jacobson ring (`≅ k[X]`). -/
lemma isJacobsonRing_line : IsJacobsonRing (𝒟 ⧸ 𝓅) :=
  isJacobsonRing_of_surjective ⟨(quotientLineEquiv _ hθ.out).symm.toRingHom,
    (quotientLineEquiv _ hθ.out).symm.surjective⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- `T1/P_ℓ` is a Dedekind domain (`≅ k[X]`). -/
lemma isDedekindDomain_line : IsDedekindDomain (𝒟 ⧸ 𝓅) :=
  haveI : IsPrincipalIdealRing (𝒟 ⧸ 𝓅) :=
    IsPrincipalIdealRing.of_surjective (quotientLineEquiv _ hθ.out).symm.toRingHom
      (quotientLineEquiv _ hθ.out).symm.surjective
  inferInstance

include hϖ in
lemma span_ϖ_isMaximal : (Ideal.span {ϖ}).IsMaximal := by
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  exact IsLocalRing.maximalIdeal.isMaximal O

omit [IsDomain O] [IsDiscreteValuationRing O] in
lemma pointP_isMaximal : (pointP (ε * ϖ ^ m) b₄ t κ (θπ hker)).IsMaximal :=
  pointIdeal_isMaximal _ hθ.out

variable (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K)

include hϖ hε h3 hE in
/-- **Purity along `ℓ`**: `C.B₁/P_ℓ C.B₁` is étale over `T1/P_ℓ` away from the nodes. -/
theorem etale_line :
    (Localization.awayMap (algebraMap (𝒟 ⧸ 𝓅) (C.B₁ ⧸ Ideal.map (algebraMap 𝒟 C.B₁) 𝓅))
      (Ideal.Quotient.mk 𝓅 𝓰)).Etale := by
  haveI : IsDomain 𝒟 := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  haveI : IsIntegrallyClosed 𝒟 :=
    TateGlue1.isIntegrallyClosed_T1' (k := k) (θ := θ) hϖ hker hκ hε h3 hE
  haveI : IsNoetherianRing 𝒟 := inferInstanceAs (IsNoetherianRing 𝒯)
  haveI : IsFractionRing 𝒟 K := inferInstanceAs (IsFractionRing 𝒯 K)
  haveI := isJacobsonRing_line (ε := ε) (m := m) (b₄ := b₄) (t := t) (κ := κ) hker
  haveI : IsDomain 𝒯 := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  refine CovData.etale_quot (C := C) 𝓅 𝓰 (algebraMap_mem_lineP hker) fun P hPm hP hgP ↦ ?_
  haveI : Ideal.IsMaximal (P : Ideal 𝒯) := hPm
  obtain ⟨y, h1, h2, h3⟩ := exists_regular_pair_T1_line hϖ hθ.out hker rfl
    (Nat.pos_of_neZero m) hκ (P : Ideal 𝒯) (hP := hPm) (hP (algebraMap_mem_lineP hker))
    (hP (w1_mem_lineP hker)) hgP
  exact ⟨_, y, h1, h2, h3⟩

include hϖ hε h3 hE in
/-- **The vertex chart is étale** over `(T1/P_ℓ)[1/(h'(h' + 1))]`. -/
theorem vertexChart_etale (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅] :
    Algebra.Etale (ComponentChart.R 𝓅 𝓰) (ComponentChart.C1 𝓅 𝓰 𝔓) := by
  haveI := isDedekindDomain_line (ε := ε) (m := m) (b₄ := b₄) (t := t) (κ := κ) hker
  exact ComponentChart.etale_C1 (glD_notMem_lineP hker) (etale_line hϖ hker hε h3 hE C)

include hϖ hε h3 hE in
/-- **The vertex chart is finite.** -/
theorem vertexChart_finite (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅] :
    Module.Finite (ComponentChart.R 𝓅 𝓰) (ComponentChart.C1 𝓅 𝓰 𝔓) := by
  haveI : IsDomain 𝒟 := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  haveI : IsIntegrallyClosed 𝒟 :=
    TateGlue1.isIntegrallyClosed_T1' (k := k) (θ := θ) hϖ hker hκ hε h3 hE
  haveI : IsNoetherianRing 𝒟 := inferInstanceAs (IsNoetherianRing 𝒯)
  haveI : IsFractionRing 𝒟 K := inferInstanceAs (IsFractionRing 𝒯 K)
  haveI := CovData.finite_B₁ C
  exact ComponentChart.finite_C1 _ _ _

include hϖ hε h3 hE in
/-- **The degree of the vertex chart is the order of the decomposition group `Γ_v`.** -/
theorem vertexChart_finrank (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅] :
    Module.finrank (ComponentChart.R 𝓅 𝓰) (ComponentChart.C1 𝓅 𝓰 𝔓) =
      Nat.card (MulAction.stabilizer (C.L ≃ₐ[K] C.L) 𝔓) := by
  haveI : IsDomain 𝒟 := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  haveI : IsIntegrallyClosed 𝒟 :=
    TateGlue1.isIntegrallyClosed_T1' (k := k) (θ := θ) hϖ hker hκ hε h3 hE
  haveI : IsNoetherianRing 𝒟 := inferInstanceAs (IsNoetherianRing 𝒯)
  haveI : IsFractionRing 𝒟 K := inferInstanceAs (IsFractionRing 𝒯 K)
  haveI := span_ϖ_isMaximal hϖ
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝓅) :=
    isDiscreteValuationRing_lineIdeal (b₄ := b₄) (θπ (ε := ε) (m := m) hker) hκ
    (dvd_mul_of_dvd_right (dvd_pow_self ϖ (NeZero.ne m)) ε) hϖ.ne_zero (θϖ hker) hker.le
  haveI := pointP_isMaximal (ε := ε) (m := m) (b₄ := b₄) (t := t) (κ := κ) hker
  exact CovData.finrank_C1_eq_card (C := C) 𝓅 (P := pointP (ε * ϖ ^ m) b₄ t κ (θπ hker))
    (algebraMap_mem_pointIdeal _ (θϖ hker)) (lineIdeal_lt_pointIdeal _) 𝔓
    (glD_notMem_lineP hker)

include hϖ hε h3 hE in
/-- **`Γ_v ≃ Aut_{T1/P_ℓ}(C.B₁/𝔓)`**: the decomposition group acts faithfully on the component. -/
theorem vertexChart_stabilizerHom_bijective (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅] :
    Function.Bijective (Ideal.Quotient.stabilizerHom 𝔓 𝓅 (C.L ≃ₐ[K] C.L)) := by
  haveI : IsDomain 𝒟 := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  haveI : IsIntegrallyClosed 𝒟 :=
    TateGlue1.isIntegrallyClosed_T1' (k := k) (θ := θ) hϖ hker hκ hε h3 hE
  haveI : IsNoetherianRing 𝒟 := inferInstanceAs (IsNoetherianRing 𝒯)
  haveI : IsFractionRing 𝒟 K := inferInstanceAs (IsFractionRing 𝒯 K)
  haveI := span_ϖ_isMaximal hϖ
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝓅) :=
    isDiscreteValuationRing_lineIdeal (b₄ := b₄) (θπ (ε := ε) (m := m) hker) hκ
    (dvd_mul_of_dvd_right (dvd_pow_self ϖ (NeZero.ne m)) ε) hϖ.ne_zero (θϖ hker) hker.le
  haveI := pointP_isMaximal (ε := ε) (m := m) (b₄ := b₄) (t := t) (κ := κ) hker
  exact CovData.stabilizerHom_bijective (C := C) 𝓅 (P := pointP (ε * ϖ ^ m) b₄ t κ (θπ hker))
    (algebraMap_mem_pointIdeal _ (θϖ hker)) (lineIdeal_lt_pointIdeal _) 𝔓

end

end TateS6

end SemistableReduction
