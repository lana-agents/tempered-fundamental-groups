/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10MainE
import TemperedFundamentalGroups.SemistableReduction.W10ComponentData
import TemperedFundamentalGroups.SemistableReduction.ZariskiConnected

/-!
# The output of `StrongComponentAS` from a semistable Gauss tree over `E`

`strongComponentA_body_of_tree`: the strengthened copy of `strongA_body_of_tree` (W10MainE). In
addition to its hypotheses it takes `Statement.ZariskiConnected` (connected special fibres of the
summands, transported to `O` along `eComp`) and, for every component model over the tree
(`hunf`: any `g` whose projective model has the points of the normalized tree model and is
semistable), split nodes, no loops and unfoldedness on the line `xB`; it gives all clauses of
`Statement.StrongComponentAS` with `K' = E` (`strongComponentA_body_of_data`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits Polynomial TensorProduct

/-- The restriction of a field map to valuation subrings with `O'.comap f = O` is local. -/
theorem isLocalHom_restrict {K E : Type*} [Field K] [Field E] (f : K →+* E)
    (O : ValuationSubring K) (O' : ValuationSubring E) (h : O'.comap f = O)
    (hmem : ∀ x ∈ O, f x ∈ O') : IsLocalHom (f.restrict O O' hmem) := by
  constructor
  intro a ha
  obtain ⟨u, hu⟩ := ha
  have hu' : ((u : O') : E) = f a := congrArg Subtype.val hu
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    have : ((u : O') : E) = 0 := by rw [hu', h0, map_zero]
    exact u.ne_zero (Subtype.ext this)
  have hv : (((u⁻¹ : O'ˣ) : O') : E) * ((u : O') : E) = 1 := by
    have := congrArg Subtype.val u.inv_mul
    exact this
  have hinv : (a : K)⁻¹ ∈ O := by
    have h1 : f ((a : K)⁻¹) ∈ O' := by
      rw [map_inv₀, ← hu', ← eq_inv_of_mul_eq_one_left hv]
      exact ((u⁻¹ : O'ˣ) : O').2
    have h2 : (a : K)⁻¹ ∈ O'.comap f := h1
    rwa [h] at h2
  exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ ha0))

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields ProjScheme ZariskiModel W10Discs

attribute [local instance] polyAlgebra compAlgO

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

variable {K : Type u} [Field K] [CharZero K] (O : ValuationSubring K)
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B]
  [Module.IsTorsionFree K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Algebra.Smooth K B]
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] [Algebra K E]

/-- **The output of `StrongComponentAS` from a semistable Galois-stable Gauss tree over `E`.** -/
theorem strongComponentA_body_of_tree [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hZ : TemperedFundamentalGroups.SemistableReduction.Statement.ZariskiConnected.{u})
    {G : Type u} [Group G] [MulSemiringAction G B] [SMulCommClass G K B]
    (β : G →* (B ≃ₐ[K[X]] B))
    (hβ : ∀ g, (β g).restrictScalars K = MulSemiringAction.toAlgAut G K B g)
    [FiniteDimensional K E] [IsGalois K E]
    (hO' : (νE).valuationSubring.comap (algebraMap K E) = O)
    [IsDiscreteValuationRing (νE).valuationSubring] (ϖ' : (νE).valuationSubring)
    (hϖ' : Irreducible ϖ')
    (hσO' : ∀ σ : E ≃ₐ[K] E, ∀ y ∈ (νE).valuationSubring, σ y ∈ (νE).valuationSubring)
    (hiso : ∀ σ : E ≃ₐ[K] E, ∀ x, νE (σ x) = νE x)
    {r : ℕ} (θ : Fin r → (νE).valuationSubring) (hθ0 : ∀ s, (θ s : E) ≠ 0)
    (hθint : ∀ s, letI := algebraOO' O E (νE).valuationSubring hO'; IsIntegral O (θ s))
    (hθgen : ∀ y : (νE).valuationSubring, (y : E) ∈ Subring.closure
      ((((algebraMap K E).comp O.subtype).range : Set E) ∪ Set.range fun s ↦ (θ s : E)))
    {ιt : Type} [Fintype ιt] [Nonempty ιt] (aE cE : ιt → E) (hcE : ∀ i, cE i ≠ 0)
    (hconv : GaussTree.IsConvex νE aE cE) (hred : GaussTree.IsReduced νE aE cE)
    (hstab : ∀ σ : E ≃ₐ[K] E, ∀ i, ∃ i', νE (σ (cE i)) = νE (cE i') ∧
      νE (σ (aE i) - aE i') ≤ νE (cE i'))
    (hcharts : ∀ 𝔪 : MaximalSpectrum (LX K E B),
      ∀ Cc ∈ ((gaussJoinModel νE aE cE).normalization (Comp K E B 𝔪)).charts,
        ∀ [Algebra (νE).valuationSubring Cc],
          (∀ o, ((algebraMap (νE).valuationSubring Cc o : Cc) : Comp K E B 𝔪) =
            algebraMap (νE).valuationSubring (Comp K E B 𝔪) o) → IsSemistable ϖ' Cc)
    (I : Type u) [Finite I] (c₀ : I → ModelCode O)
    (j₀ : ∀ i, Spec (CommRingCat.of B) ⟶ (c₀ i).scheme)
    {nK : I → MaximalSpectrum (LB K B) → ℕ} {fK : ∀ i 𝔫, Fin (nK i 𝔫 + 1) → CompB K B 𝔫}
    (hfK : ∀ i 𝔫 j, fK i 𝔫 j ≠ 0)
    (ιK : ∀ i 𝔫, (projModelCode O (hfK i 𝔫)).scheme ⟶ (c₀ i).scheme)
    (hιK : ∀ i 𝔫, genericPt O (hfK i 𝔫) ≫ ιK i 𝔫 =
      Spec.map (CommRingCat.ofHom (toCompB 𝔫)) ≫ j₀ i)
    (hιOK : ∀ i 𝔫, ιK i 𝔫 ≫ (c₀ i).toSpec = (projModelCode O (hfK i 𝔫)).toSpec)
    (hV' : ∀ i 𝔪, ∀ W' ∈ RT (νE).valuationSubring
      ((projModel (baseRing (Comp K E B 𝔪) (νE).valuationSubring)
        (fE (f := fK i) 𝔪)).charts : Set (Subring (Comp K E B 𝔪))), ∃ j,
      W'.comap (algebraMap (RatFunc E) (Comp K E B 𝔪)) = (gaussRat νE (aE j)
        (Units.mk0 (νE (cE j)) ((Valuation.ne_zero_iff _).2 (hcE j)))).valuationSubring)
    (xB : B)
    (hunf : ∀ (𝔪 : MaximalSpectrum (LX K E B)) (n : ℕ) (g : Fin (n + 1) → Comp K E B 𝔪)
      (hg : ∀ l, g l ≠ 0),
      (projModel (algebraMap (νE).valuationSubring (Comp K E B 𝔪)).range g).points =
        ((gaussJoinModel νE aE cE).normalization (Comp K E B 𝔪)).points →
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ'
        (projModelCode (νE).valuationSubring hg) →
      TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ'
        (projModelCode (νE).valuationSubring hg) ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.NoLoops
        (projModelCode (νE).valuationSubring hg) ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsUnfolded (νE).valuationSubring
        (ψ (K := K) (B := B) (E := E) (1 ⊗ₜ xB) 𝔪) (projModelCode (νE).valuationSubring hg)
        (genericPt (νE).valuationSubring hg)) :
    ∃ (O' : ValuationSubring E) (_ : O'.comap (algebraMap K E) = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c' : TemperedFundamentalGroups.ModelCode O') (c : TemperedFundamentalGroups.ModelCode O)
      (e : c.scheme ≅ c'.scheme)
      (j : Spec (CommRingCat.of (TensorProduct K E B)) ⟶ c.scheme)
      (act : G × (E ≃ₐ[K] E) →* Aut c.scheme)
      (dom : ∀ i, c.scheme ⟶ (c₀ i).scheme),
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ' c' ∧
      e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K E).restrict O O' (fun x hx => by
          rw [← ‹O'.comap (algebraMap K E) = O›] at hx; exact hx))) = c.toSpec ∧
      IsSchemeTheoreticallyDominant j ∧
      j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeftRingHom).comp ((algebraMap K E).comp O.subtype))) ∧
      (∀ gσ : G × (E ≃ₐ[K] E), (act gσ).hom ≫ c.toSpec = c.toSpec) ∧
      (∀ gσ : G × (E ≃ₐ[K] E),
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr (gσ.2⁻¹)
          (MulSemiringAction.toAlgAut G K B gσ.1⁻¹)).toRingHom) ≫ j = j ≫ (act gσ).hom) ∧
      (∀ i, j ≫ dom i = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct K E B)) ≫ j₀ i) ∧
      (∀ i, dom i ≫ (c₀ i).toSpec = c.toSpec) ∧
      topologicalKrullDim (specialFibre c.toSpec) ≤ 1 ∧
      (∀ ε : TensorProduct K E B, IsIdempotentElem ε → ε ≠ 0 →
        (∀ f : TensorProduct K E B, IsIdempotentElem f → f * ε = 0 ∨ f * ε = ε) →
        ∃ (c₁' : TemperedFundamentalGroups.ModelCode O')
          (c₁ : TemperedFundamentalGroups.ModelCode O)
          (e₁ : c₁.scheme ≅ c₁'.scheme) (ι₁ : c₁.scheme ⟶ c.scheme)
          (j₁ : Spec (CommRingCat.of (TensorProduct K E B ⧸ Ideal.span {1 - ε})) ⟶ c₁.scheme),
          TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ' c₁' ∧
          TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ' c₁' ∧
          TemperedFundamentalGroups.SemistableReduction.ModelCode.NoLoops c₁' ∧
          e₁.hom ≫ c₁'.toSpec ≫ Spec.map (CommRingCat.ofHom
            ((algebraMap K E).restrict O O' (fun x hx => by
              rw [← ‹O'.comap (algebraMap K E) = O›] at hx; exact hx))) = c₁.toSpec ∧
          IsOpenImmersion ι₁ ∧ ι₁ ≫ c.toSpec = c₁.toSpec ∧ IsSchemeTheoreticallyDominant j₁ ∧
          j₁ ≫ ι₁ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - ε}))) ≫ j ∧
          (∀ gσ : G × (E ≃ₐ[K] E), Algebra.TensorProduct.congr (gσ.2⁻¹)
              (MulSemiringAction.toAlgAut G K B gσ.1⁻¹) ε = ε →
            ∃ ψ : c₁.scheme ⟶ c₁.scheme, ψ ≫ ι₁ = ι₁ ≫ (act gσ).hom) ∧
          ConnectedSpace (specialFibre c₁.toSpec) ∧
          ∃ (L₁ : Type u) (_ : Field L₁)
            (_ : Algebra (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁)
            (_ : IsFractionRing (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁)
            (_ : Algebra E L₁) (_ : Algebra O' L₁) (_ : IsScalarTower O' E L₁)
            (j₁' : Spec (CommRingCat.of L₁) ⟶ c₁'.scheme),
            algebraMap E L₁ = (algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁).comp
              ((Ideal.Quotient.mk (Ideal.span {1 - ε})).comp
                Algebra.TensorProduct.includeLeftRingHom) ∧
            TemperedFundamentalGroups.SemistableReduction.ModelCode.IsUnfolded O'
              (algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁
                (Ideal.Quotient.mk _ (1 ⊗ₜ xB))) c₁' j₁' ∧
            j₁' = Spec.map (CommRingCat.ofHom
              (algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁)) ≫ j₁ ≫ e₁.hom) := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI := isReduced_BX K E B
  have hn := isIntegrallyClosedIn_BX K E B
  -- the semistable model of every component
  have hcomp (𝔪 : MaximalSpectrum (LX K E B)) := exists_component_model (F₀ := Comp K E B 𝔪)
    hcE hconv hred ϖ' (hcharts 𝔪) (D K E B 𝔪) (fun z hz ↦ mem_D_of_isIntegral K E B hn 𝔪 hz)
    (by
      rintro _ ⟨o, rfl⟩
      refine ⟨algebraMap E (BX K E B) (o : E), ?_⟩
      change Ideal.Quotient.mk _ (algebraMap (BX K E B) (LX K E B)
        (algebraMap E[X] (BX K E B) (Polynomial.C (o : E)))) =
          Ideal.Quotient.mk _ (algebraMap E (LX K E B) (o : E))
      congr 1
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply E[X] (RatFunc E) (LX K E B),
        IsScalarTower.algebraMap_apply E (RatFunc E) (LX K E B), RatFunc.algebraMap_C]
      rfl)
  choose n g hg hpts hss hroot using hcomp
  have hR₁ (𝔪 : MaximalSpectrum (LX K E B)) : (algebraMap O (Comp K E B 𝔪)).range ≤
      baseRing (Comp K E B 𝔪) (νE).valuationSubring := by
    rintro _ ⟨o, rfl⟩
    refine ⟨algebraMap K E o, ?_, rfl⟩
    change algebraMap K E o ∈ (νE).valuationSubring
    rw [← ValuationSubring.mem_comap, hO']
    exact o.2
  have hR (𝔪 : MaximalSpectrum (LX K E B)) : (algebraMap O (Comp K E B 𝔪)).range ≤
      (algebraMap (νE).valuationSubring (Comp K E B 𝔪)).range := by
    rintro _ ⟨o, rfl⟩
    refine ⟨⟨algebraMap K E o, ?_⟩, rfl⟩
    rw [← ValuationSubring.mem_comap, hO']
    exact o.2
  have hunf' := fun 𝔪 ↦ hunf 𝔪 (n 𝔪) (g 𝔪) (hg 𝔪) (hpts 𝔪) (hss 𝔪)
  refine strongComponentA_body_of_data O β hβ E (νE).valuationSubring hO' ϖ' hϖ' hn hσO' n hg
    hss hroot (fun h 𝔫 ↦ ?_) θ hθ0 hθint hθgen I c₀ j₀ (fun i ↦ ?_) xB (fun 𝔪 ↦ (hunf' 𝔪).1)
    (fun 𝔪 ↦ (hunf' 𝔪).2.1) (fun 𝔪 ↦ ?_) (fun 𝔪 ↦ (hunf' 𝔪).2.2)
  · exact W10Stable.exists_projChart_map_le
      (((αH (G := G) h⁻¹ : E ≃ₐ[K] E) : E ≃+* E)) (hiso _) hcE hred (hstab _)
      (compEquiv (σh β h) 𝔫) (φh_algebraMap_ratFunc β h 𝔫) (hpts (πh β h 𝔫)) (hpts 𝔫)
  · refine ⟨fun 𝔪 ↦ nK i (contrB K E B 𝔪), fE (f := fK i), fE_ne_zero (hfK i),
      ιE O (c₀ i) (hfK i) (ιK i), ιE_toSpec O (c₀ i) (hfK i) (ιK i) (hιOK i),
      genericPt_ιE O (c₀ i) (j₀ i) (hfK i) (ιK i) (hιK i), fun 𝔪 l ↦ ?_⟩
    exact W10Dom.locallyDominates_of_tree (fun j ↦ rfl) hconv hred (hV' i 𝔪) (hR₁ 𝔪) (hR 𝔪)
      (hpts 𝔪) l
  · haveI : ConnectedSpace (specialFibre (projModelCode (νE).valuationSubring (hg 𝔪)).toSpec) :=
      hZ K O E (νE).valuationSubring hO' ϖ' hϖ' (Comp K E B 𝔪)
        (projModelCode (νE).valuationSubring (hg 𝔪)) (genericPt (νE).valuationSubring (hg 𝔪))
        (hss 𝔪) inferInstance (genericPt_toSpec _)
    haveI : IsLocalHom (algOO' O E (νE).valuationSubring hO') :=
      isLocalHom_restrict (algebraMap K E) O (νE).valuationSubring hO' _
    rw [← eComp_toSpec O (νE).valuationSubring hO' n hg θ hθ0 hθint hθgen 𝔪]
    exact connectedSpace_specialFibre_comp _
      (fun a b hab ↦ Subtype.ext ((algebraMap K E).injective (congrArg Subtype.val hab))) _ _

end W10Assembly

end SemistableReduction
