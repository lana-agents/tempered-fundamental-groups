/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.Defs
import TemperedFundamentalGroups.FibreFunctor.SpanRealization

/-!
# Theorem A: the tempered group is André's group (the formal part)

Blueprint §10.2, A4. Restricting automorphisms of the fibre functor to the tempered coverings
presented through semistable levels is an isomorphism of topological groups
`temperedPi1 ≃ₜ* andreGroup` (`andreEquivOfInput`), given the geometric input `AndreInput`:

* **pullback**: tempered coverings pull back along refinements, by a cartesian morphism which is
  bijective on fibres (`Andre/Pullback.lean`);
* **refinement**: every level has a semistable refinement, and two refinements over a morphism of
  levels have a common semistable refinement (`Andre/Refinement.lean`, from W10).

The admissible spans are the cartesian morphisms `W ⟶ X` from semistable objects over
refinements, and (S1), (S2) of `FibreAut.HasPhiSpans` follow from the universal property of
cartesian morphisms.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

namespace LevelHom

/-- A morphism of levels with models is **equivariant** if its model morphism is. -/
def IsEquivariant {Lv' Lv : Level O R A} (ℓ : LevelHom O R A Lv' Lv) : Prop :=
  ∀ h' : Lv'.L.H, (Lv'.ρ h').hom ≫ ℓ.ψ = ℓ.ψ ≫ (Lv.ρ (ℓ.φ.r h')).hom

lemma comp_assoc {L₁ L₂ L₃ L₄ : Level O R A} (a : LevelHom O R A L₁ L₂)
    (b : LevelHom O R A L₂ L₃) (c : LevelHom O R A L₃ L₄) :
    (a.comp b).comp c = a.comp (b.comp c) := by
  ext1
  · exact Category.assoc _ _ _
  · exact Category.assoc _ _ _

lemma ofTempHom_comp {X Y Z : TempObj O R A} (m : X ⟶ Y) (n : Y ⟶ Z) :
    ofTempHom (m ≫ n) = (ofTempHom m).comp (ofTempHom n) := rfl

lemma ofTempHom_id (X : TempObj O R A) : ofTempHom (𝟙 X) = LevelHom.id X.Lv := rfl

lemma id_comp {Lv' Lv : Level O R A} (ℓ : LevelHom O R A Lv' Lv) : (id Lv').comp ℓ = ℓ := by
  ext1
  · exact Category.id_comp _
  · exact Category.id_comp _

lemma isRefinement_id (Ω : Type u) [Field Ω] [Algebra R Ω] (Lv : Level O R A) :
    (id Lv).IsRefinement Ω where
  surj_H0 h := ⟨h, rfl⟩
  trans_fibre t₁ t₂ h := ⟨1, rfl, by
    rw [FiniteLevel.fibreAct_one]
    simpa [id] using h⟩
  surj_fibre t := ⟨t, by simp [id]⟩
  equivariant h' := by simp [id]

end LevelHom

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- A morphism `m : W ⟶ X` of tempered coverings is **cartesian** if every morphism into `X` whose
level part factors equivariantly through that of `m` factors through `m`. -/
def IsCartesianHom {W X : TempObj O R A} (m : W ⟶ X) : Prop :=
  ∀ (W' : TempObj O R A) (μ : LevelHom O R A W'.Lv W.Lv), μ.IsEquivariant →
    ∀ g : W' ⟶ X, LevelHom.ofTempHom g = μ.comp (LevelHom.ofTempHom m) →
      ∃ g' : W' ⟶ W, LevelHom.ofTempHom g' = μ ∧ g' ≫ m = g

lemma isCartesianHom_id (X : TempObj O R A) : IsCartesianHom (𝟙 X) := by
  intro W' μ _ g hg
  refine ⟨g, ?_, Category.comp_id g⟩
  rw [hg, LevelHom.ofTempHom_id]
  ext1
  · exact Category.comp_id _
  · exact Category.comp_id _

variable (O R A Ω) in
/-- **The geometric input for Theorem A** (Blueprint §10.2, A2 and A3). -/
structure AndreInput : Prop where
  /-- Tempered coverings pull back along refinements. -/
  pullback : ∀ (X : TempObj O R A) (Lv' : Level O R A) (ℓ : LevelHom O R A Lv' X.Lv),
    ℓ.IsRefinement Ω → ∃ (P' : CoveringCode Lv'.ρs) (m : (⟨Lv', P'⟩ : TempObj O R A) ⟶ X),
      LevelHom.ofTempHom m = ℓ ∧ Function.Bijective ((tempFibre O R A V hV).map m) ∧
        IsCartesianHom m
  /-- Every level has a semistable refinement. -/
  refinement : ∀ Lv : Level O R A, ∃ (Lv₃ : Level O R A) (ℓ : LevelHom O R A Lv₃ Lv),
    IsSemistableLevel Lv₃ ∧ ℓ.IsRefinement Ω
  /-- Two refinements over a morphism have a common semistable refinement. -/
  common : ∀ {Lv₁ Lv Lv₂ Lv' : Level O R A} (ℓ₁ : LevelHom O R A Lv₁ Lv)
    (ℓ₂ : LevelHom O R A Lv₂ Lv') (u : LevelHom O R A Lv Lv'),
    ℓ₁.IsRefinement Ω → ℓ₂.IsRefinement Ω →
      ∃ (Lv₃ : Level O R A) (μ₁ : LevelHom O R A Lv₃ Lv₁) (μ₂ : LevelHom O R A Lv₃ Lv₂),
        IsSemistableLevel Lv₃ ∧ (μ₁.comp ℓ₁).IsRefinement Ω ∧ μ₁.IsEquivariant ∧
          μ₂.IsEquivariant ∧ (μ₁.comp ℓ₁).comp u = μ₂.comp ℓ₂

open FibreAut

/-- The span `X ⟵ ι c = ι c` of a morphism from a semistable object. -/
def spanOf {X : TempObj O R A} (c : (semistableObj O R A).FullSubcategory)
    (m : (semistableObj O R A).ι.obj c ⟶ X)
    (hm : Function.Bijective ((tempFibre O R A V hV).map m)) :
    PhiSpan (tempFibre O R A V hV) (semistableObj O R A) X where
  W := (semistableObj O R A).ι.obj c
  c := c
  m := m
  n := 𝟙 _
  bij_m := hm
  bij_n := by rw [CategoryTheory.Functor.map_id]; exact Function.bijective_id

variable (Ω) in
/-- Admissible spans: cartesian morphisms from semistable objects over refinements. -/
def AdmSpan (X : TempObj O R A) (s : PhiSpan (tempFibre O R A V hV) (semistableObj O R A) X) :
    Prop :=
  ∃ (c : (semistableObj O R A).FullSubcategory) (m : (semistableObj O R A).ι.obj c ⟶ X)
    (hm : Function.Bijective ((tempFibre O R A V hV).map m)),
    IsCartesianHom m ∧ (LevelHom.ofTempHom m).IsRefinement Ω ∧ s = spanOf V hV c m hm

variable {V hV}

lemma hasPhiSpans (hI : AndreInput O R A Ω V hV) :
    HasPhiSpans (tempFibre O R A V hV) (semistableObj O R A) (AdmSpan Ω V hV) where
  nonempty X := by
    obtain ⟨Lv₃, ℓ, hss, hℓ⟩ := hI.refinement X.Lv
    obtain ⟨P', m, hmℓ, hbij, hcart⟩ := hI.pullback X Lv₃ ℓ hℓ
    let c : (semistableObj O R A).FullSubcategory :=
      ⟨⟨Lv₃, P'⟩, (show IsSemistableLevel Lv₃ from hss)⟩
    exact ⟨spanOf V hV c m hbij, c, m, hbij, hcart, hmℓ ▸ hℓ, rfl⟩
  refine {X Y} u s s' hs hs' := by
    obtain ⟨c, m, hm, hcart, href, rfl⟩ := hs
    obtain ⟨c', m', hm', hcart', href', rfl⟩ := hs'
    obtain ⟨Lv₃, μ₁, μ₂, hss, hμ, he₁, he₂, hcomm⟩ :=
      hI.common (LevelHom.ofTempHom m) (LevelHom.ofTempHom m') (LevelHom.ofTempHom u) href href'
    obtain ⟨P₃, m₃, hm₃ℓ, hbij₃, hcart₃⟩ := hI.pullback X Lv₃ _ hμ
    let c₃ : (semistableObj O R A).FullSubcategory :=
      ⟨⟨Lv₃, P₃⟩, (show IsSemistableLevel Lv₃ from hss)⟩
    obtain ⟨w, -, hw⟩ := hcart c₃.obj μ₁ he₁ m₃ hm₃ℓ
    obtain ⟨w', -, hw'⟩ := hcart' c₃.obj μ₂ he₂ (m₃ ≫ u) (by
      rw [LevelHom.ofTempHom_comp, hm₃ℓ, hcomm])
    refine ⟨spanOf V hV c₃ m₃ hbij₃, w, ObjectProperty.homMk w, w', ObjectProperty.homMk w',
      ⟨c₃, m₃, hbij₃, hcart₃, hm₃ℓ ▸ hμ, rfl⟩, hw, ?_, hw', ?_⟩
    · change 𝟙 _ ≫ w = w ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · change 𝟙 _ ≫ w' = w' ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]

lemma admSpan_idSpan (c : (semistableObj O R A).FullSubcategory) :
    AdmSpan Ω V hV ((semistableObj O R A).ι.obj c) (idSpan c) := by
  refine ⟨c, 𝟙 _, ?_, isCartesianHom_id _, ?_, rfl⟩
  · rw [CategoryTheory.Functor.map_id]; exact Function.bijective_id
  · rw [LevelHom.ofTempHom_id]; exact LevelHom.isRefinement_id Ω _

/-- **Theorem A** (Blueprint §10.1): given the geometric input, the tempered fundamental group is
André's group, by restriction. -/
def andreEquivOfInput (hI : AndreInput O R A Ω V hV) :
    temperedPi1 O R A V hV ≃ₜ* andreGroup O R A V hV :=
  restrictEquivOfPhiSpans (hasPhiSpans hI) admSpan_idSpan

end

end TemperedFundamentalGroups
