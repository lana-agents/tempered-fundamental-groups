/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XHarmonic

/-!
# W10 with connected components (a strengthened copy of `Statement.Strong`)

Only a **definition** (no theorem, nothing assumed). `Statement.StrongComponent` is a verbatim
copy of `Statement.Strong` (same quantifiers, same outputs, same clauses), except that its last
clause ("if `K' ⊗_K B` has no nontrivial idempotents, the special fibre of `c` is connected") is
replaced by the **component clause**: for every primitive idempotent `ε` of `K' ⊗_K B`
(a connected component `Spec ((K' ⊗_K B) ⧸ (1 - ε))` of the generic fibre) there is

* a clopen sub-model `ι₁ : c₁ ⟶ c` (open and closed immersion over `O`; geometrically: the
  closure of the component, which is open since the local rings `O[u,v]/(uv − ϖⁿ)`, `O[u]` of a
  semistable model are domains), again a split semistable `O'`-model `c₁'`;
* the restriction `j₁ : Spec ((K' ⊗_K B) ⧸ (1 - ε)) ⟶ c₁` of `j`, an open immersion which is
  scheme-theoretically dominant;
* the action of the stabiliser of `ε` in `G × Gal(K'/K)` restricts to `c₁`;
* the special fibre of `c₁` is **connected** (Zariski connectedness for the normal proper model
  `c₁` of the connected `Spec ((K' ⊗_K B) ⧸ (1 - ε))` over the complete DVR `O'`);
* `c₁'` is an **unfolded W-model** (`ModelCode.IsUnfolded`, Blueprint §9.7) of the function
  field `L₁` of the component on the x-line given by the input `x ∈ R` (`R` finite over `K[x]`),
  with generic point the restriction of `j₁`: a W-model (`IsUnfolded.isWModel`) every node of
  which lies over a node of its Gauss tree (W7 (c): points over smooth points of the base tree are
  smooth). These are the models between which maps are x-harmonic (`Statement.HarmonicX`).

Domination of the `c₀ i` by `c₁` is `ι₁ ≫ dom i`. The case `ε = 1` (connected `K' ⊗_K B`)
recovers the connectedness clause of `Strong` (with `c₁ = c`). This is the form of W10 consumed by
the domination step of Theorem B (Blueprint §10.3.5, `Andre/GaloisClass2.lean`): the Galois
objects live over a connected component of `K' ⊗_K B*`, as `K' ⊗_K B*` is disconnected as soon as
`B*` has a nontrivial constant field which `K'` contains, and this cannot be avoided by the choice
of `B*`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

/-- **The strong form of W10 with connected components**: `Statement.Strong`, with its last
clause replaced by the component clause (see the module docstring). -/
def Statement.StrongComponent : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (R : Type u) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (_ : ringKrullDim R = 1)
    (x : R) (_ : (Polynomial.aeval (R := K) x).toRingHom.Finite)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] [Module.Finite R B]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G K B]
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
      ModelCode.IsSemistable ϖ' c' ∧ ModelCode.IsSplit ϖ' c' ∧ ModelCode.NoLoops c' ∧
      e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K K').restrict O O' (fun x hx => by
          rw [← ‹O'.comap (algebraMap K K') = O›] at hx; exact hx))) = c.toSpec ∧
      IsOpenImmersion j ∧ IsSchemeTheoreticallyDominant j ∧
      j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeftRingHom).comp ((algebraMap K K').comp O.subtype))) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'), (act gσ).hom ≫ c.toSpec = c.toSpec) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'),
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr (gσ.2⁻¹)
          (MulSemiringAction.toAlgAut G K B gσ.1⁻¹)).toRingHom) ≫ j = j ≫ (act gσ).hom) ∧
      (∀ i, j ≫ dom i = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct K K' B)) ≫ j₀ i) ∧
      (∀ i, dom i ≫ (c₀ i).toSpec = c.toSpec) ∧
      (∀ i, (∀ x : (c₀ i).scheme, IsDomain ((c₀ i).scheme.presheaf.stalk x) ∧
          IsIntegrallyClosed ((c₀ i).scheme.presheaf.stalk x)) → Flat (c₀ i).toSpec →
        (∀ z ∈ specialFibre (c₀ i).toSpec, ∃ y ∈ specialFibre c.toSpec, dom i y = z) ∧
        ∀ z ∈ specialFibre (c₀ i).toSpec,
          Finite (_root_.ConnectedComponents {y : specialFibre c.toSpec // dom i y.1 = z})) ∧
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

end TemperedFundamentalGroups.SemistableReduction
