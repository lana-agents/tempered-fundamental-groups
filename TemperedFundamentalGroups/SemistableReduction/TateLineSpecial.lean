/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateLineVertex
import TemperedFundamentalGroups.SemistableReduction.P1ThreeMobius
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialEquiv

/-!
# The vertex datum over `V₁` of a Galois Tate cover (MR13 step 7, D1)

For a tame cover `C : TateS6.Cov …` and a component `𝔓` of the special fibre of `C.B₁` over the
generic point `P_ℓ` of the line `ℓ` of the Tate chart, the vertex chart
`C1 = (C.B₁/𝔓)[1/(h'(h' + 1))]` (`TateLineVertex`) is a finite étale algebra over

  `R = (T1/P_ℓ)[1/(h'(h' + 1))] ≅ k[h', 1/(h'(h' + 1))] ≅ R1/J`

(**`TateS6.lineREquiv`**: `T1/P_ℓ ≃ k[X]` (`quotientLineEquiv`) localised at `h'(h' + 1)`;
**`TateS6.vertexBaseEquiv`**: composed with the Möbius re-charting
`P1Three.vertexChartEquiv.symm`). Hence:

* **`TateS6.vertexSp`**: the special datum `P1Three.Special1 O θ a` over
  `V₁ = ℙ¹ ∖ {0, 1, ā}` given by `C1` (`CuspChart.Special.ofEquiv`);
* **`TateS6.vertexSp_finrank`** (`hdeg`): `rank_{R1/J} Sp.C1 = |Γ_v|` (`Γ_v = Stab(𝔓)`);
* **`TateS6.vertexSp_connected`** (`hconn`): `Sp.C1` has no non-trivial idempotents;
* **`TateS6.vertexAct`** (`act` on `V₁`): `Γ_v` acts on `Sp.C1` through
  `Γ_v ≃ Aut_{T1/P_ℓ}(C.B₁/𝔓)` and `ComponentChart.autC1`; **`vertexAct_one`**,
  **`vertexAct_mul`**, and **`vertexAct_faithful`** (`hfaith`).
-/

universe u

open Polynomial
open scoped Pointwise

namespace SemistableReduction

open TateTwoChart TateTwoChartNode TateGlue0 EtaleTower

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

set_option quotPrecheck false in
/-- `P_ℓ` for the Tate data of the section. -/
local notation "𝓅" => lineP (ε * ϖ ^ m) b₄ t κ (θπ (ε := ε) (m := m) hker)

omit [IsDomain O] [IsDiscreteValuationRing O] in
lemma quotientLineEquiv_glD :
    quotientLineEquiv (θπ (ε := ε) (m := m) hker) hθ.out
      (Ideal.Quotient.mk 𝓅 (glD (ε * ϖ ^ m) b₄ t κ)) = MobiusLine.p k := by
  change lineHom θ (ε * ϖ ^ m) b₄ t κ (θπ hker) (glD (ε * ϖ ^ m) b₄ t κ) = _
  simp only [glD, h1, map_mul, map_add, map_one, lineHom_of, Polynomial.map_X, MobiusLine.p]

/-- **`R = (T1/P_ℓ)[1/(h'(h' + 1))] ≃ k[h', 1/(h'(h' + 1))]`.** -/
def lineREquiv :
    ComponentChart.R 𝓅 (glD (ε * ϖ ^ m) b₄ t κ) ≃+* MobiusLine.B k :=
  IsLocalization.ringEquivOfRingEquiv (M := ComponentChart.M 𝓅
    (glD (ε * ϖ ^ m) b₄ t κ)) (T := Submonoid.powers (MobiusLine.p k)) _ _
    (quotientLineEquiv (θπ (ε := ε) (m := m) hker) hθ.out) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (quotientLineEquiv_glD hker))

variable (a : O) (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1)

/-- **`R = (T1/P_ℓ)[1/(h'(h' + 1))] ≃ R1/J`** (Möbius re-charting `P1Three.vertexChartEquiv`). -/
def vertexBaseEquiv :
    ComponentChart.R 𝓅 (glD (ε * ϖ ^ m) b₄ t κ) ≃+* Ts θ (P1Three.R1 O a) :=
  (lineREquiv hker).trans (P1Three.vertexChartEquiv a ha0 ha1).symm

variable (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K)

include hϖ hε h3 hE

/-- **The special datum over `V₁` of the component `𝔓`**: the vertex chart as a finite étale
`R1/J`-algebra. -/
def vertexSp (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅] :
    P1Three.Special1 O θ a :=
  haveI := vertexChart_finite hϖ hker hε h3 hE C 𝔓
  haveI := vertexChart_etale hϖ hker hε h3 hE C 𝔓
  P1Three.CuspChart.Special.ofEquiv
    (vertexBaseEquiv (ε := ε) (m := m) (b₄ := b₄) (t := t) (κ := κ) hker a ha0 ha1)
    (ComponentChart.C1 𝓅 (glD (ε * ϖ ^ m) b₄ t κ) 𝔓)

/-- **`hdeg`**: the degree of the vertex datum over `R1/J` is `|Γ_v|`. -/
theorem vertexSp_finrank (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅] :
    Module.finrank (Ts θ (P1Three.R1 O a)) (vertexSp hϖ hker hε h3 hE a ha0 ha1 C 𝔓).C1 =
      Nat.card (MulAction.stabilizer (C.L ≃ₐ[K] C.L) 𝔓) := by
  haveI := vertexChart_finite hϖ hker hε h3 hE C 𝔓
  haveI := vertexChart_etale hϖ hker hε h3 hE C 𝔓
  exact (P1Three.CuspChart.Special.finrank_ofEquiv _ _).trans
    (vertexChart_finrank hϖ hker hε h3 hE C 𝔓)

/-- **`hconn`**: the vertex datum over `V₁` is connected (`C1` is a domain). -/
theorem vertexSp_connected (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅]
    (x : (vertexSp hϖ hker hε h3 hE a ha0 ha1 C 𝔓).C1)
    (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  haveI := vertexChart_finite hϖ hker hε h3 hE C 𝔓
  haveI := vertexChart_etale hϖ hker hε h3 hE C 𝔓
  haveI := ComponentChart.isDomain_C1 (Q := 𝔓)
    (glD_notMem_lineP (ε := ε) (m := m) (b₄ := b₄) (t := t) (κ := κ) hker)
  exact P1Three.CuspChart.Special.isIdempotentElem_ofEquiv _ _ x hx

/-- **The action of `Γ_v = Stab(𝔓)` on the vertex datum over `V₁`**, through
`Γ_v → Aut_{T1/P_ℓ}(C.B₁/𝔓)` and `ComponentChart.autC1`. -/
def vertexAct (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅]
    (σ : MulAction.stabilizer (C.L ≃ₐ[K] C.L) 𝔓) :
    (vertexSp hϖ hker hε h3 hE a ha0 ha1 C 𝔓).C1 →ₐ[Ts θ (P1Three.R1 O a)]
      (vertexSp hϖ hker hε h3 hE a ha0 ha1 C 𝔓).C1 :=
  haveI := vertexChart_finite hϖ hker hε h3 hE C 𝔓
  haveI := vertexChart_etale hϖ hker hε h3 hE C 𝔓
  P1Three.CuspChart.Special.autOfEquiv _ _
    (ComponentChart.autC1 (Ideal.Quotient.stabilizerHom 𝔓 𝓅 _ σ))

lemma vertexAct_apply (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅]
    (σ : MulAction.stabilizer (C.L ≃ₐ[K] C.L) 𝔓)
    (x : ComponentChart.C1 𝓅 (glD (ε * ϖ ^ m) b₄ t κ) 𝔓) :
    vertexAct hϖ hker hε h3 hE a ha0 ha1 C 𝔓 σ x =
      ComponentChart.autC1 (Ideal.Quotient.stabilizerHom 𝔓 𝓅 _ σ) x := rfl

lemma vertexAct_one (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅]
    (x : (vertexSp hϖ hker hε h3 hE a ha0 ha1 C 𝔓).C1) :
    vertexAct hϖ hker hε h3 hE a ha0 ha1 C 𝔓 1 x = x :=
  (vertexAct_apply hϖ hker hε h3 hE a ha0 ha1 C 𝔓 1 x).trans
    ((congrArg (fun ρ ↦ ComponentChart.autC1 (g := glD (ε * ϖ ^ m) b₄ t κ) ρ x)
      (MonoidHom.map_one _)).trans (DFunLike.congr_fun ComponentChart.autC1_one x))

lemma vertexAct_mul (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅]
    (σ τ : MulAction.stabilizer (C.L ≃ₐ[K] C.L) 𝔓)
    (x : (vertexSp hϖ hker hε h3 hE a ha0 ha1 C 𝔓).C1) :
    vertexAct hϖ hker hε h3 hE a ha0 ha1 C 𝔓 (σ * τ) x =
      vertexAct hϖ hker hε h3 hE a ha0 ha1 C 𝔓 σ
        (vertexAct hϖ hker hε h3 hE a ha0 ha1 C 𝔓 τ x) :=
  (vertexAct_apply hϖ hker hε h3 hE a ha0 ha1 C 𝔓 (σ * τ) x).trans
    ((congrArg (fun ρ ↦ ComponentChart.autC1 (g := glD (ε * ϖ ^ m) b₄ t κ) ρ x)
      (MonoidHom.map_mul _ σ τ)).trans
      (DFunLike.congr_fun (ComponentChart.autC1_mul _ _) x))

/-- **`hfaith`**: `Γ_v` acts faithfully on the vertex datum over `V₁`. -/
theorem vertexAct_faithful (𝔓 : Ideal C.B₁) [𝔓.IsPrime] [𝔓.LiesOver 𝓅]
    (σ : MulAction.stabilizer (C.L ≃ₐ[K] C.L) 𝔓)
    (h : ∀ x, vertexAct hϖ hker hε h3 hE a ha0 ha1 C 𝔓 σ x = x) : σ = 1 := by
  have h1 : Ideal.Quotient.stabilizerHom 𝔓 𝓅 _ σ = 1 :=
    ComponentChart.autC1_injective
      (glD_notMem_lineP (ε := ε) (m := m) (b₄ := b₄) (t := t) (κ := κ) hker) h
  exact (vertexChart_stabilizerHom_bijective hϖ hker hε h3 hE C 𝔓).1
    (h1.trans (map_one _).symm)

end

end TateS6

end SemistableReduction
