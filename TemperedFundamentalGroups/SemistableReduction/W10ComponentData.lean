/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10ComponentClause
import TemperedFundamentalGroups.SemistableReduction.SemistableFibreDim

/-!
# The output of `StrongComponentA` from the W10 data

`strongComponentA_body_of_data`: the strengthened copy of `strongA_body_of_data` (W10Final). Under
its hypotheses and, for the summands `projModelCode O' (hg 𝔪)`, split nodes, no loops,
connected special fibres and unfoldedness on the line `xB`, the W10 assembly satisfies all
clauses of `Statement.StrongComponentA` with `K' = E`: those of `StrongA`, the dimension bound
(`ModelCode.topologicalKrullDim_le_one_of_iso`) and the component clause (`component_clause`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits Polynomial TensorProduct

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields ProjScheme ZariskiModel

attribute [local instance] polyAlgebra compAlgO

/-- **The output of `StrongComponentA` from the W10 data.** -/
theorem strongComponentA_body_of_data {K : Type u} [Field K] (O : ValuationSubring K)
    [IsDiscreteValuationRing O]
    {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B]
    [Module.IsTorsionFree K[X] B] [Algebra K B] [IsScalarTower K K[X] B]
    {G : Type u} [Group G] [MulSemiringAction G B] [SMulCommClass G K B]
    (β : G →* (B ≃ₐ[K[X]] B))
    (hβ : ∀ g, (β g).restrictScalars K = MulSemiringAction.toAlgAut G K B g)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (O' : ValuationSubring E) (hO' : O'.comap (algebraMap K E) = O)
    [IsDiscreteValuationRing O'] (ϖ' : O') (hϖ' : Irreducible ϖ')
    [IsReduced (BX K E B)] (hn : IsIntegrallyClosedIn (BX K E B) (LX K E B))
    (hσO' : ∀ σ : E ≃ₐ[K] E, ∀ y ∈ O', σ y ∈ O')
    (n : MaximalSpectrum (LX K E B) → ℕ) {g : ∀ 𝔪, Fin (n 𝔪 + 1) → Comp K E B 𝔪}
    (hg : ∀ 𝔪 j, g 𝔪 j ≠ 0)
    (hss : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ'
      (projModelCode O' (hg 𝔪)))
    (hroot : ∀ 𝔪, LocallyDominates (algebraMap O' (Comp K E B 𝔪)).range (RingHom.id _)
      (D K E B 𝔪).subtype (g 𝔪))
    (hact : ∀ (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)),
      ∀ Q ∈ (projModel (algebraMap O' (Comp K E B 𝔫)).range (g 𝔫)).points, ∃ i,
        ∀ y ∈ projChart (algebraMap O' (Comp K E B (πh β h 𝔫))).range (g (πh β h 𝔫)) i,
          φh β h 𝔫 y ∈ Q)
    {r : ℕ} (θ : Fin r → O') (hθ0 : ∀ s, (θ s : E) ≠ 0)
    (hθint : ∀ s, letI := algebraOO' O E O' hO'; IsIntegral O (θ s))
    (hθgen : ∀ y : O', (y : E) ∈ Subring.closure
      ((((algebraMap K E).comp O.subtype).range : Set E) ∪ Set.range fun s ↦ (θ s : E)))
    (I : Type u) [Finite I] (c₀ : I → ModelCode O)
    (j₀ : ∀ i, Spec (CommRingCat.of B) ⟶ (c₀ i).scheme)
    (hdata : ∀ i, ∃ (nf : MaximalSpectrum (LX K E B) → ℕ)
      (f : ∀ 𝔪, Fin (nf 𝔪 + 1) → Comp K E B 𝔪) (hf : ∀ 𝔪 j, f 𝔪 j ≠ 0)
      (ι : ∀ 𝔪, (projModelCode O (hf 𝔪)).scheme ⟶ (c₀ i).scheme),
      (∀ 𝔪, ι 𝔪 ≫ (c₀ i).toSpec = (projModelCode O (hf 𝔪)).toSpec) ∧
      (∀ 𝔪, genericPt O (hf 𝔪) ≫ ι 𝔪 = compPt O (c₀ i) (j₀ i) 𝔪) ∧
      ∀ 𝔪 l, LocallyDominates (algebraMap O (Comp K E B 𝔪)).range (RingHom.id _)
        (projChart (algebraMap O' (Comp K E B 𝔪)).range (g 𝔪) l).subtype (f 𝔪))
    (xB : B)
    (hsp : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSplit ϖ'
      (projModelCode O' (hg 𝔪)))
    (hnl : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.NoLoops
      (projModelCode O' (hg 𝔪)))
    (hconn : ∀ 𝔪, ConnectedSpace (specialFibre
      (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).toSpec))
    (hunf : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.IsUnfolded O'
      (ψ (K := K) (B := B) (E := E) (1 ⊗ₜ xB) 𝔪) (projModelCode O' (hg 𝔪))
      (genericPt O' (hg 𝔪))) :
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
          TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSplit ϖ' c₁' ∧
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
  choose nf f hf ι hιO hι hdom using hdata
  have he := e_toSpec O O' hO' n hg θ hθ0 hθint hθgen
  refine ⟨O', hO', inferInstance, ϖ', hϖ', c' O' n hg, c O O' n hg θ hθ0,
    e O O' hO' n hg θ hθ0 hθint hθgen, jC O O' hO' hn n hg hroot θ hθ0 hθint hθgen,
    act O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen,
    fun i ↦ dom O O' hO' n hg θ hθ0 hθint hθgen (c₀ i) (hf i) (ι i) (hdom i),
    isSemistable_c' O' n hg ϖ' hss, he, inferInstance,
    jC_toSpec O O' hO' hn n hg hroot θ hθ0 hθint hθgen,
    act_toSpec O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen, fun h ↦ ?_,
    fun i ↦ jC_dom O O' hO' hn n hg hroot θ hθ0 hθint hθgen (c₀ i) (j₀ i) (hf i) (ι i) (hdom i)
      (hι i),
    fun i ↦ dom_toSpec O O' hO' n hg θ hθ0 hθint hθgen (c₀ i) (hf i) (ι i) (hdom i) (hιO i),
    ModelCode.topologicalKrullDim_le_one_of_iso _
      (fun a b hab ↦ Subtype.ext ((algebraMap K E).injective (congrArg Subtype.val hab)))
      hϖ' _ (isSemistable_c' O' n hg ϖ' hss) he,
    fun ε hε h0 hprim ↦ component_clause O O' hO' hn n hg hroot θ hθ0 hθint hθgen β hβ hσO'
      hact ϖ' xB hss hsp hnl hconn hunf ε hε h0 hprim⟩
  have := jC_equivariant O O' hO' hn β hσO' n hg hroot hact θ hθ0 hθint hθgen h
  have hb : (βH β h⁻¹).restrictScalars K = MulSemiringAction.toAlgAut G K B h.1⁻¹ := hβ _
  rw [hb] at this
  exact this

end W10Assembly

end SemistableReduction
