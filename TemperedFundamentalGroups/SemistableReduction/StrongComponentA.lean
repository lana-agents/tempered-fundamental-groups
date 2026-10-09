/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.StrongA
import TemperedFundamentalGroups.Setup.InvariantLine

/-!
# `StrongA` with the component clause (the W10 form targeted for Theorem B)

Only a **definition** and two implications. `Statement.StrongComponentA` has **exactly the inputs
of `Statement.StrongA`** (mixed characteristic, perfect residue field, `IsDomain R`, `G` acting on
`R` and `B`) together with a `G`-invariant x-line `x ∈ R` (`R` finite over `K[x]`; invariance
because the W10 construction needs a `G`-invariant line for the stability of the Gauss tree).
Its output is the output conjunction of `StrongA`, followed by the dimension bound of the special
fibre and the component clause of `Statement.StrongComponent` (clopen semistable sub-models of
the connected components of the generic fibre with connected special fibres, unfolded W-models on
the x-line). Blueprint §10.3.8 (targeted for Theorem B, 2026-10-07).

* `Statement.strongA_of_strongComponentA`: projection (the meaning of `StrongA` is unchanged);
* `Statement.strongComponentA_of_strongComponent`: dropping clauses (the old `StrongComponent`,
  untargeted, has no mixed-characteristic hypotheses).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

/-- **W10 for Theorem B**: `StrongA` with an x-line input, the dimension bound and the component
clause. -/
def Statement.StrongComponentA : Prop :=
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
          ModelCode.IsSemistable ϖ' c₁' ∧ ModelCode.IsSplit ϖ' c₁' ∧ ModelCode.NoLoops c₁' ∧
          e₁.hom ≫ c₁'.toSpec ≫ Spec.map (CommRingCat.ofHom
            ((algebraMap K K').restrict O O' (fun x hx => by
              rw [← ‹O'.comap (algebraMap K K') = O›] at hx; exact hx))) = c₁.toSpec ∧
          IsOpenImmersion ι₁ ∧ IsClosedImmersion ι₁ ∧ ι₁ ≫ c.toSpec = c₁.toSpec ∧
          IsOpenImmersion j₁ ∧ IsSchemeTheoreticallyDominant j₁ ∧
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

/-- `StrongComponentA` implies `StrongA` (projection). -/
theorem Statement.strongA_of_strongComponentA (h : Statement.StrongComponentA.{u}) :
    Statement.StrongA.{u} := by
  intro K _ _ O _ _ _ p hp hpm R _ _ _ _ hR B _ _ _ _ _ _ G _ _ _ _ _ _ hGR ι _ c₀ j₀ hj₀
  obtain ⟨x, hxG, hx⟩ := exists_finite_aeval_invariant (K := K) (G := G) hR
  obtain ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, hss, he, hjd, hjS,
    hact, hactj, hdom, hdomS, -⟩ := h K O p hp hpm R hR x hx B G hGR hxG ι c₀ j₀ hj₀
  exact ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, hss, he, hjd, hjS, hact,
    hactj, hdom, hdomS⟩

/-- The old (untargeted) `StrongComponent` implies `StrongComponentA` (dropping clauses). -/
theorem Statement.strongComponentA_of_strongComponent (h : Statement.StrongComponent.{u}) :
    Statement.StrongComponentA.{u} := by
  intro K _ _ O _ _ _ p hp hpm R _ _ _ _ hR x hx B _ _ _ _ _ _ G _ _ _ _ _ _ hGR _ ι _ c₀ j₀
    hj₀
  obtain ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, hss, -, -, he, -, hjd,
    hjS, hact, hactj, hdom, hdomS, -, hdim, hcomp⟩ := h K O R hR x hx B G ι c₀ j₀ hj₀
  exact ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, hss, he, hjd, hjS, hact,
    hactj, hdom, hdomS, hdim, hcomp⟩

end TemperedFundamentalGroups.SemistableReduction
