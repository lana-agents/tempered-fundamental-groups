/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.Topology
import TemperedFundamentalGroups.Models.Projective
import TemperedFundamentalGroups.Models.Specialization
import TemperedFundamentalGroups.Topology.CoveringCode
import TemperedFundamentalGroups.Tempered.Finite

/-!
# The tempered fundamental group of `[Spec R / A]` through integral models

Fix a field `K` with a valuation subring `O`, an affine `K`-scheme `Y = Spec R` with an action of a
group `A` by `K`-algebra automorphisms, and a geometric point `ȳ : Spec Ω → Y` together with a
valuation subring `V ⊆ Ω` with `V ∩ K = O` (Blueprint §3.1).

A **level** is a Galois finite level `L` of `[Y/A]` (`FiniteLevel`) together with a projective
`O`-model: a closed subscheme `𝒯` of some `ℙ^m_O` (a `ModelCode`), a morphism
`j : Spec B_L → 𝒯` over `O`, and an action `ρ` of `G_L` on `𝒯` over `O` for which `j` is
equivariant (`g` acts on `Spec B_L` through `Spec (σ_g⁻¹)`).

An object of the **tempered category** `TempObj` is a level together with a `G_L`-equivariant
covering space of the special fibre `|𝒯_s|` (a `CoveringCode`). Morphisms are morphisms of
finite levels, morphisms of models over `O` compatible with the `j`'s, and equivariant continuous
maps of covering spaces over the induced map of special fibres.

The **fibre functor** sends `(L, P)` to the fibre of `P` over the specialization `sp(j ∘ t₀)` of
the base point. The object `(L, P)` stands for the tempered covering `(P ×_{sp} T^an)/G_L⁰` of
`[Y/A]`, whose fibre over `ȳ` is this set (Blueprint §3.4).

**The tempered fundamental group** is `temperedPi1 := Aut` of this fibre functor, with the
topology of pointwise convergence (`FibreAut`). Adding the trivial model and trivial coverings
embeds the finite category, which gives the continuous comparison homomorphism
`temperedToEtale : temperedPi1 →* etalePi1`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- The structure map `O → B` of a coded finite étale `R`-algebra. -/
noncomputable def levelStructureMap (L : FiniteLevel R A Ω) : O →+* L.B :=
  (algebraMap R L.B).comp ((algebraMap K R).comp O.subtype)

/-- **A level with a model**: a Galois finite level of `[Spec R / A]` together with a projective
`O`-model `𝒯`, a morphism `j : Spec B → 𝒯` over `O` and a compatible action of `G_B` on `𝒯`. -/
structure Level : Type u where
  /-- The finite level. -/
  L : FiniteLevel R A Ω
  /-- The model, as a closed subscheme of a projective space over `O`. -/
  c : ModelCode O
  /-- The map from the finite étale cover to the model. -/
  j : Spec (CommRingCat.of L.B) ⟶ c.scheme
  /-- `j` lies over `O`. -/
  j_toSpec : j ≫ c.toSpec = Spec.map (CommRingCat.ofHom (levelStructureMap O R A L))
  /-- The action of `G_B` on the model. -/
  ρ : L.G →* Aut c.scheme
  /-- The action lies over `O`. -/
  ρ_toSpec : ∀ g, (ρ g).hom ≫ c.toSpec = c.toSpec
  /-- `j` is equivariant. -/
  ρ_j : ∀ g, Spec.map (CommRingCat.ofHom (g.σ.symm : L.B →+* L.B)) ≫ j = j ≫ (ρ g).hom

namespace Level

variable {O R A}

/-- The special fibre `|𝒯_s|` of the model of a level. -/
abbrev Z (Lv : Level O R A (Ω := Ω)) : Type u := specialFibre Lv.c.toSpec

/-- The action of `G_B` on the special fibre of the model. -/
noncomputable def ρs (Lv : Level O R A (Ω := Ω)) : Lv.L.G →* (Lv.Z ≃ₜ Lv.Z) where
  toFun g := specialFibreHomeomorph (Lv.ρ g) (Lv.ρ_toSpec g)
  map_one' := by
    ext x
    simp [coe_specialFibreHomeomorph]
    rfl
  map_mul' g h := by
    ext x
    simp only [coe_specialFibreHomeomorph, map_mul, Homeomorph.mul_apply]
    rw [Aut.Aut_mul_def, Iso.trans_hom, Scheme.Hom.comp_apply]

lemma ρs_apply (Lv : Level O R A (Ω := Ω)) (g : Lv.L.G) (x : Lv.Z) :
    ((Lv.ρs g x : Lv.Z) : Lv.c.scheme) = (Lv.ρ g).hom (x : Lv.c.scheme) :=
  coe_specialFibreHomeomorph _ _ _

end Level

/-- An object of the tempered category: a level with a model and a `G_B`-equivariant covering
space of the special fibre of the model. -/
structure TempObj : Type u where
  /-- The level. -/
  Lv : Level O R A (Ω := Ω)
  /-- The equivariant covering space of the special fibre. -/
  P : CoveringCode Lv.ρs

namespace TempObj

variable {O R A}

/-- A morphism of the tempered category. -/
@[ext]
structure Hom (X Y : TempObj O R A (Ω := Ω)) : Type u where
  /-- The morphism of finite levels. -/
  φ : X.Lv.L ⟶ Y.Lv.L
  /-- The morphism of models. -/
  ψ : X.Lv.c.scheme ⟶ Y.Lv.c.scheme
  /-- It lies over `O`. -/
  ψ_toSpec : ψ ≫ Y.Lv.c.toSpec = X.Lv.c.toSpec
  /-- It is compatible with the maps from the finite étale covers. -/
  j_ψ : X.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (φ.f : Y.Lv.L.B →+* X.Lv.L.B)) ≫ Y.Lv.j
  /-- The map of covering spaces. -/
  h : X.P.carrier → Y.P.carrier
  continuous_h : Continuous h
  /-- `h` lies over the induced map of special fibres. -/
  fst_h : ∀ x, ((h x).1.1 : Y.Lv.c.scheme) = ψ (x.1.1 : X.Lv.c.scheme)
  /-- `h` is equivariant along `φ.r`. -/
  h_act : ∀ g x, h (X.P.act g x) = Y.P.act (φ.r g) (h x)

lemma spec_map_comp_f {L L' L'' : FiniteLevel R A Ω} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    Spec.map (CommRingCat.ofHom ((φ ≫ ψ).f : L''.B →+* L.B)) =
      Spec.map (CommRingCat.ofHom (φ.f : L'.B →+* L.B)) ≫
        Spec.map (CommRingCat.ofHom (ψ.f : L''.B →+* L'.B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma spec_map_id_f (L : FiniteLevel R A Ω) :
    Spec.map (CommRingCat.ofHom ((𝟙 L : L ⟶ L).f : L.B →+* L.B)) = 𝟙 _ := by
  rw [← Spec.map_id]
  rfl

/-- The identity morphism of the tempered category. -/
def Hom.id (X : TempObj O R A (Ω := Ω)) : Hom X X where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by rw [spec_map_id_f, Category.comp_id, Category.id_comp]
  h := fun x => x
  continuous_h := continuous_id
  fst_h := fun _ => rfl
  h_act := fun _ _ => rfl

/-- Composition in the tempered category. -/
def Hom.comp {X Y Z : TempObj O R A (Ω := Ω)} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  φ := φ.φ ≫ ψ.φ
  ψ := φ.ψ ≫ ψ.ψ
  ψ_toSpec := by rw [Category.assoc, ψ.ψ_toSpec, φ.ψ_toSpec]
  j_ψ := by
    rw [← Category.assoc, φ.j_ψ, Category.assoc, ψ.j_ψ, ← Category.assoc, spec_map_comp_f]
  h := ψ.h ∘ φ.h
  continuous_h := ψ.continuous_h.comp φ.continuous_h
  fst_h := fun x => by
    simp only [Function.comp_apply, ψ.fst_h, φ.fst_h, Scheme.Hom.comp_apply]
  h_act := fun g x => by
    simp only [Function.comp_apply, φ.h_act, ψ.h_act]
    rfl

noncomputable instance : Category (TempObj O R A (Ω := Ω)) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp m := Hom.ext (Category.id_comp m.φ) (Category.id_comp m.ψ) rfl
  comp_id m := Hom.ext (Category.comp_id m.φ) (Category.comp_id m.ψ) rfl
  assoc m n p := Hom.ext (Category.assoc m.φ n.φ p.φ) (Category.assoc m.ψ n.ψ p.ψ) rfl

@[simp] lemma id_h (X : TempObj O R A (Ω := Ω)) : Hom.h (𝟙 X) = id := rfl
@[simp] lemma id_ψ (X : TempObj O R A (Ω := Ω)) : Hom.ψ (𝟙 X) = 𝟙 _ := rfl
@[simp] lemma comp_h {X Y Z : TempObj O R A (Ω := Ω)} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).h = ψ.h ∘ φ.h := rfl
@[simp] lemma comp_ψ {X Y Z : TempObj O R A (Ω := Ω)} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).ψ = φ.ψ ≫ ψ.ψ := rfl

end TempObj

variable [Algebra K Ω] [IsScalarTower K R Ω] (V : ValuationSubring Ω)
  (hV : V.comap (algebraMap K Ω) = O)

namespace Level

variable {O R A}

/-- The geometric base point of the finite étale cover, as a morphism `Spec Ω → 𝒯`. -/
noncomputable def basePoint (Lv : Level O R A (Ω := Ω)) :
    Spec (CommRingCat.of Ω) ⟶ Lv.c.scheme :=
  Spec.map (CommRingCat.ofHom (Lv.L.t₀ : Lv.L.B →+* Ω)) ≫ Lv.j

lemma basePoint_toSpec (Lv : Level O R A (Ω := Ω)) :
    Lv.basePoint ≫ Lv.c.toSpec = Spec.map (CommRingCat.ofHom (valToField O)) := by
  rw [basePoint, Category.assoc, Lv.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp [levelStructureMap, valToField, ← IsScalarTower.algebraMap_apply]

/-- **The specialization of the base point** in the special fibre of the model. -/
noncomputable def spPoint (Lv : Level O R A (Ω := Ω)) : Lv.Z :=
  sp Lv.c.toSpec V hV Lv.basePoint (basePoint_toSpec Lv)

end Level

namespace TempObj

variable {O R A}

/-- The specialization of the base point is preserved by morphisms. -/
lemma ψ_spPoint {X Y : TempObj O R A (Ω := Ω)} (m : X ⟶ Y) :
    m.ψ (X.Lv.spPoint V hV : X.Lv.c.scheme) = (Y.Lv.spPoint V hV : Y.Lv.c.scheme) := by
  unfold Level.spPoint
  rw [← coe_sp_comp (hV := hV) m.ψ m.ψ_toSpec]
  congr 2
  rw [Level.basePoint, Level.basePoint, Category.assoc, m.j_ψ, ← Category.assoc,
    ← Spec.map_comp, ← m.φ.pointed]
  rfl

end TempObj

/-- **The fibre functor** of the tempered category: the fibre of the covering space over the
specialization of the base point. -/
noncomputable def tempFibre : TempObj O R A (Ω := Ω) ⥤ Type u where
  obj X := X.P.fibre (X.Lv.spPoint V hV)
  map {X Y} m := TypeCat.ofHom fun x =>
    ⟨m.h x.1, by
      apply Subtype.ext
      rw [m.fst_h, x.2, TempObj.ψ_spPoint]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The tempered fundamental group** of the orbifold `[Spec R / A]` over the valued field
`(K, O)`, at the geometric point `Spec Ω → Spec R` with the valuation `V` on `Ω`: the
automorphism group of the fibre functor on tempered coverings presented through levels with
integral models, with the topology of pointwise convergence. -/
abbrev temperedPi1 : Type u := FibreAut (tempFibre O R A V hV)

end

end TemperedFundamentalGroups
