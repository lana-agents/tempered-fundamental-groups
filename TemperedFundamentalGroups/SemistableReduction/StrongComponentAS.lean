/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.StrongComponentA

/-!
# `Statement.StrongComponentAS`: `StrongComponentA` with split nodes only

The copy of `Statement.StrongComponentA` whose component clause asks for split nodes
(`ModelCode.HasSplitNodes`) instead of `ModelCode.IsSplit` (split nodes and geometrically
irreducible components). The geometric irreducibility is never used downstream (Blueprint §10.3.8,
dry check 2026-10-09).
`StrongComponentA → StrongComponentAS` (`strongComponentAS_of_strongComponentA`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

/-- **W10 for Theorem B with split nodes**: `StrongComponentA` with `HasSplitNodes` in the
component clause. -/
def Statement.StrongComponentAS : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
    (p : ℕ) (_ : p.Prime) (_ : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R]
    (_ : ringKrullDim R = 1) (x : R) (_ : (Polynomial.aeval (R := K) x).toRingHom.Finite)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] [Module.Finite R B]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G K B]
    [MulSemiringAction G R] [SMulCommClass G K R]
    (_ : ∀ (g : G) (r : R), g • algebraMap R B r = algebraMap R B (g • r))
    (_ : ∀ g : G, g • x = x)
    (ι : Type u) [Finite ι] (c₀ : ι → TemperedFundamentalGroups.ModelCode O)
    (j₀ : ∀ i, Spec (CommRingCat.of B) ⟶ (c₀ i).scheme)
    (_ : ∀ i, j₀ i ≫ (c₀ i).toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap K B).comp O.subtype))),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : IsGalois K K')
      (O' : ValuationSubring K') (_ : O'.comap (algebraMap K K') = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c' : TemperedFundamentalGroups.ModelCode O') (c : TemperedFundamentalGroups.ModelCode O)
      (e : c.scheme ≅ c'.scheme)
      (j : Spec (CommRingCat.of (TensorProduct K K' B)) ⟶ c.scheme)
      (act : G × (K' ≃ₐ[K] K') →* Aut c.scheme)
      (dom : ∀ i, c.scheme ⟶ (c₀ i).scheme),
      ModelCode.IsSemistable ϖ' c' ∧
      e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K K').restrict O O' (fun x hx => by
          rw [← ‹O'.comap (algebraMap K K') = O›] at hx; exact hx))) = c.toSpec ∧
      IsSchemeTheoreticallyDominant j ∧
      j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeftRingHom).comp ((algebraMap K K').comp O.subtype))) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'), (act gσ).hom ≫ c.toSpec = c.toSpec) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'),
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr (gσ.2⁻¹)
          (MulSemiringAction.toAlgAut G K B gσ.1⁻¹)).toRingHom) ≫ j = j ≫ (act gσ).hom) ∧
      (∀ i, j ≫ dom i = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct K K' B)) ≫ j₀ i) ∧
      (∀ i, dom i ≫ (c₀ i).toSpec = c.toSpec) ∧
      topologicalKrullDim (specialFibre c.toSpec) ≤ 1 ∧
      (∀ ε : TensorProduct K K' B, IsIdempotentElem ε → ε ≠ 0 →
        (∀ f : TensorProduct K K' B, IsIdempotentElem f → f * ε = 0 ∨ f * ε = ε) →
        ∃ (c₁' : TemperedFundamentalGroups.ModelCode O')
          (c₁ : TemperedFundamentalGroups.ModelCode O)
          (e₁ : c₁.scheme ≅ c₁'.scheme) (ι₁ : c₁.scheme ⟶ c.scheme)
          (j₁ : Spec (CommRingCat.of (TensorProduct K K' B ⧸ Ideal.span {1 - ε})) ⟶ c₁.scheme),
          ModelCode.IsSemistable ϖ' c₁' ∧ ModelCode.HasSplitNodes ϖ' c₁' ∧ ModelCode.NoLoops c₁' ∧
          e₁.hom ≫ c₁'.toSpec ≫ Spec.map (CommRingCat.ofHom
            ((algebraMap K K').restrict O O' (fun x hx => by
              rw [← ‹O'.comap (algebraMap K K') = O›] at hx; exact hx))) = c₁.toSpec ∧
          IsOpenImmersion ι₁ ∧ ι₁ ≫ c.toSpec = c₁.toSpec ∧ IsSchemeTheoreticallyDominant j₁ ∧
          j₁ ≫ ι₁ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - ε}))) ≫ j ∧
          (∀ gσ : G × (K' ≃ₐ[K] K'), Algebra.TensorProduct.congr (gσ.2⁻¹)
              (MulSemiringAction.toAlgAut G K B gσ.1⁻¹) ε = ε →
            ∃ ψ : c₁.scheme ⟶ c₁.scheme, ψ ≫ ι₁ = ι₁ ≫ (act gσ).hom) ∧
          ConnectedSpace (specialFibre c₁.toSpec) ∧
          ∃ (L₁ : Type u) (_ : Field L₁)
            (_ : Algebra (TensorProduct K K' B ⧸ Ideal.span {1 - ε}) L₁)
            (_ : IsFractionRing (TensorProduct K K' B ⧸ Ideal.span {1 - ε}) L₁)
            (_ : Algebra K' L₁) (_ : Algebra O' L₁) (_ : IsScalarTower O' K' L₁)
            (j₁' : Spec (CommRingCat.of L₁) ⟶ c₁'.scheme),
            algebraMap K' L₁ = (algebraMap (TensorProduct K K' B ⧸ Ideal.span {1 - ε}) L₁).comp
              ((Ideal.Quotient.mk (Ideal.span {1 - ε})).comp
                Algebra.TensorProduct.includeLeftRingHom) ∧
            ModelCode.IsUnfolded O' (algebraMap (TensorProduct K K' B ⧸ Ideal.span {1 - ε}) L₁
              (Ideal.Quotient.mk _ (1 ⊗ₜ algebraMap R B x))) c₁' j₁' ∧
            j₁' = Spec.map (CommRingCat.ofHom
              (algebraMap (TensorProduct K K' B ⧸ Ideal.span {1 - ε}) L₁)) ≫ j₁ ≫ e₁.hom)

/-- `StrongComponentA` implies `StrongComponentAS`. -/
theorem Statement.strongComponentAS_of_strongComponentA (h : Statement.StrongComponentA.{u}) :
    Statement.StrongComponentAS.{u} := by
  intro K _ _ O _ _ _ p hp hpm R _ _ _ _ hR x hx B _ _ _ _ _ _ G _ _ _ _ _ _ hGR hxG ι _ c₀ j₀ hj₀
  obtain ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, h₁, h₂, h₃, h₄, h₅, h₆,
    h₇, h₈, h₉, h₁₀⟩ := h K O p hp hpm R hR x hx B G hGR hxG ι c₀ j₀ hj₀
  refine ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, h₁, h₂, h₃, h₄, h₅, h₆,
    h₇, h₈, h₉, fun ε hε h0 hprim ↦ ?_⟩
  obtain ⟨c₁', c₁, e₁, ι₁, j₁, hss, hsp, rest⟩ := h₁₀ ε hε h0 hprim
  exact ⟨c₁', c₁, e₁, ι₁, j₁, hss, hsp.1, rest⟩

end TemperedFundamentalGroups.SemistableReduction
