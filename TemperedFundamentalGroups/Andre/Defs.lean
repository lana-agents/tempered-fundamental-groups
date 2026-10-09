/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Tempered.Category
import TemperedFundamentalGroups.SemistableReduction.Statement

/-!
# André's tempered group via semistable levels: definitions

Blueprint §10. Throughout, `K` is a field with a valuation subring `O`, `[Spec R / A]` an affine
orbifold over `K` and `Ω` a field with a valuation subring `V` over `O` (the geometric point).

* `LevelHom Lv' Lv`: a morphism of levels with models: a morphism of levels together with a
  morphism of models over `O`, compatible with the maps `j` (the data of a morphism of
  `TempObj` without the covering spaces).
* `LevelHom.IsRefinement`: a morphism of levels with models along which pulling back tempered
  coverings does not change the fibre functor:
  (i) `H'⁰ → H⁰` is surjective;
  (ii) the kernel acts transitively on the fibres of the geometric points `F_{L'} → F_L`;
  (iii) `F_{L'} → F_L` is surjective;
  (iv) the model morphism is equivariant.
  Base changes `B ↦ K' ⊗_K B` along finite Galois extensions, with a semistable model supplied by
  W10, are refinements when `Ω` is algebraically closed.
* `IsSemistableLevel Lv`: the model of `Lv` is (over `O`) a semistable model over the valuation
  ring `O'` of a finite extension `K'/K` (`SemistableReduction.ModelCode.IsSemistable`).
* `semistableObj`: the full subcategory of `TempObj` of tempered coverings presented through
  semistable levels, and **André's tempered group**
  `andreGroup := Aut (tempFibre restricted to semistableObj)`: the automorphism group of the
  fibre functor on tempered coverings defined through semistable models (Lepage, André
  III.2.1.5; Blueprint §10.1).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]

/-- **A morphism of levels with models** `Lv' ⟶ Lv`: a morphism of levels and a morphism of
models over `O` compatible with the maps from the finite étale covers. -/
@[ext]
structure LevelHom (Lv' Lv : Level O R A) : Type u where
  /-- The morphism of levels. -/
  φ : Lv'.L ⟶ Lv.L
  /-- The morphism of models. -/
  ψ : Lv'.c.scheme ⟶ Lv.c.scheme
  /-- It lies over `O`. -/
  ψ_toSpec : ψ ≫ Lv.c.toSpec = Lv'.c.toSpec
  /-- It is compatible with the maps from the finite étale covers. -/
  j_ψ : Lv'.j ≫ ψ = Spec.map (CommRingCat.ofHom (φ.f : Lv.L.B →+* Lv'.L.B)) ≫ Lv.j

namespace LevelHom

variable {O R A}

/-- The identity morphism of a level with a model. -/
def id (Lv : Level O R A) : LevelHom O R A Lv Lv where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by rw [TempObj.spec_map_id_f, Category.comp_id, Category.id_comp]

/-- Composition of morphisms of levels with models. -/
def comp {Lv'' Lv' Lv : Level O R A} (μ : LevelHom O R A Lv'' Lv') (ℓ : LevelHom O R A Lv' Lv) :
    LevelHom O R A Lv'' Lv where
  φ := μ.φ ≫ ℓ.φ
  ψ := μ.ψ ≫ ℓ.ψ
  ψ_toSpec := by rw [Category.assoc, ℓ.ψ_toSpec, μ.ψ_toSpec]
  j_ψ := by
    rw [← Category.assoc, μ.j_ψ, Category.assoc, ℓ.j_ψ, ← Category.assoc,
      TempObj.spec_map_comp_f]

/-- The level-with-model part of a morphism of tempered coverings. -/
def ofTempHom {X Y : TempObj O R A} (m : X ⟶ Y) : LevelHom O R A X.Lv Y.Lv where
  φ := m.φ
  ψ := m.ψ
  ψ_toSpec := m.ψ_toSpec
  j_ψ := m.j_ψ

variable (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- **A refinement**: a morphism of levels with models along which pulling back does not change the
fibre functor (Blueprint §10). -/
structure IsRefinement {Lv' Lv : Level O R A} (ℓ : LevelHom O R A Lv' Lv) : Prop where
  /-- (i) `H'⁰ → H⁰` is surjective. -/
  surj_H0 : ∀ h : Lv.L.H0, ∃ h' : Lv'.L.H0, (ℓ.φ.r h' : Lv.L.H) = h
  /-- (ii) The kernel of `H'⁰ → H⁰` acts transitively on the fibres of `F_{L'} → F_L`. -/
  trans_fibre : ∀ t₁ t₂ : Lv'.L.B →ₐ[R] Ω, t₁.comp ℓ.φ.f = t₂.comp ℓ.φ.f →
    ∃ k : Lv'.L.H0, ℓ.φ.r k = 1 ∧ FiniteLevel.fibreAct Ω Lv'.L k t₁ = t₂
  /-- (iii) `F_{L'} → F_L` is surjective. -/
  surj_fibre : ∀ t : Lv.L.B →ₐ[R] Ω, ∃ t' : Lv'.L.B →ₐ[R] Ω, t'.comp ℓ.φ.f = t
  /-- (iv) The morphism of models is equivariant. -/
  equivariant : ∀ h' : Lv'.L.H, (Lv'.ρ h').hom ≫ ℓ.ψ = ℓ.ψ ≫ (Lv.ρ (ℓ.φ.r h')).hom

end LevelHom

variable {O R A}

/-- **A semistable level**: the model is, over `O`, a semistable projective model over the
valuation ring `O'` of a finite extension `K'/K`. -/
def IsSemistableLevel (Lv : Level O R A) : Prop :=
  ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
    (O' : ValuationSubring K') (h : O'.comap (algebraMap K K') = O)
    (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
    (c' : ModelCode O') (e : Lv.c.scheme ≅ c'.scheme),
    SemistableReduction.ModelCode.IsSemistable ϖ' c' ∧
      e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K K').restrict O O' (fun x hx => by rw [← h] at hx; exact hx))) =
        Lv.c.toSpec

variable (O R A) in
/-- The tempered coverings presented through semistable levels. -/
def semistableObj : ObjectProperty (TempObj O R A) := fun X => IsSemistableLevel X.Lv

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

variable (O R A) in
/-- **André's tempered group** (Blueprint §10.1): the automorphism group of the fibre functor on
the tempered coverings defined through semistable models, with the topology of pointwise
convergence. -/
abbrev andreGroup : Type u := FibreAut ((semistableObj O R A).ι ⋙ tempFibre O R A V hV)

end

end TemperedFundamentalGroups
