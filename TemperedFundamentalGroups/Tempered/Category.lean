/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.Topology
import TemperedFundamentalGroups.Models.Projective
import TemperedFundamentalGroups.Models.Specialization
import TemperedFundamentalGroups.Topology.CoveringCode
import TemperedFundamentalGroups.Tempered.Level

/-!
# The tempered fundamental group of `[Spec R / A]` through integral models

Fix a field `K` with a valuation subring `O`, an affine `K`-scheme `Y = Spec R` with an action of a
group `A` by ring automorphisms, and a geometric point `ȳ : Spec Ω → Y` together with a
valuation subring `V ⊆ Ω` with `V ∩ K = O` (Blueprint §3.1).

A **level with a model** (`Level`) is a level `(B, H)` of `[Y/A]` (`FiniteLevel`: a finite étale
`R`-algebra with a group `H` of semilinear automorphisms surjecting onto `A`) together with a
projective `O`-model: a closed subscheme `𝒯` of some `ℙ^m_O` (a `ModelCode`), a morphism
`j : Spec B → 𝒯` over `O`, and an action `ρ` of `H` on `𝒯` over `O` for which `j` is
equivariant (`g` acts on `Spec B` through `Spec (σ_g⁻¹)`).

An object of the **tempered category** `TempObj` is a level with a model together with an
`H`-equivariant covering space `P` of the special fibre `|𝒯_s|` (a `CoveringCode`). It stands for
the tempered covering `(P ×_{sp} (Spec B)^an) / H⁰` of `[Y/A]`, where `sp` is the specialization
map of the model and `H⁰ = ker (H → A)`. Morphisms are morphisms of levels, morphisms of models
over `O` compatible with the `j`'s, and equivariant continuous maps of covering spaces over the
induced map of special fibres.

The **fibre functor** `tempFibre` sends `(L, P)` to the fibre of this covering over `ȳ`:
the set of pairs `(t, p)` of a geometric point `t : B →ₐ[R] Ω` over `ȳ` and a point `p ∈ P` over
the specialization `sp(j ∘ t)`, modulo the diagonal action of `H⁰` (Blueprint §3.4).

**The tempered fundamental group** is `temperedPi1 := Aut tempFibre`, with the topology of
pointwise convergence (`FibreAut`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]

/-- The structure map `O → B` of a coded finite étale `R`-algebra. -/
def levelStructureMap (L : FiniteLevel R A) : O →+* L.B :=
  (algebraMap R L.B).comp ((algebraMap K R).comp O.subtype)

/-- **A level with a model**: a level `(B, H)` of `[Spec R / A]` together with a projective
`O`-model `𝒯`, a morphism `j : Spec B → 𝒯` over `O` and a compatible action of `H` on `𝒯`. -/
structure Level : Type u where
  /-- The level. -/
  L : FiniteLevel R A
  /-- The model, as a closed subscheme of a projective space over `O`. -/
  c : ModelCode O
  /-- The map from the finite étale cover to the model. -/
  j : Spec (CommRingCat.of L.B) ⟶ c.scheme
  /-- `j` lies over `O`. -/
  j_toSpec : j ≫ c.toSpec = Spec.map (CommRingCat.ofHom (levelStructureMap O R A L))
  /-- The action of `H` on the model. -/
  ρ : L.H →* Aut c.scheme
  /-- The action lies over `O`. -/
  ρ_toSpec : ∀ g, (ρ g).hom ≫ c.toSpec = c.toSpec
  /-- `j` is equivariant. -/
  ρ_j : ∀ g : L.H, Spec.map (CommRingCat.ofHom
    ((g : SemilinearAut R A L.B).σ.symm : L.B →+* L.B)) ≫ j = j ≫ (ρ g).hom

namespace Level

variable {O R A}

/-- The special fibre `|𝒯_s|` of the model of a level. -/
abbrev Z (Lv : Level O R A) : Type u := specialFibre Lv.c.toSpec

/-- The action of `H` on the special fibre of the model. -/
def ρs (Lv : Level O R A) : Lv.L.H →* (Lv.Z ≃ₜ Lv.Z) where
  toFun g := specialFibreHomeomorph (Lv.ρ g) (Lv.ρ_toSpec g)
  map_one' := by
    ext x
    simp [coe_specialFibreHomeomorph]
    rfl
  map_mul' g h := by
    ext x
    simp only [coe_specialFibreHomeomorph, map_mul, Homeomorph.mul_apply]
    rw [Aut.Aut_mul_def, Iso.trans_hom, Scheme.Hom.comp_apply]

lemma ρs_apply (Lv : Level O R A) (g : Lv.L.H) (x : Lv.Z) :
    ((Lv.ρs g x : Lv.Z) : Lv.c.scheme) = (Lv.ρ g).hom (x : Lv.c.scheme) :=
  coe_specialFibreHomeomorph _ _ _

end Level

/-- An object of the tempered category: a level with a model and an `H`-equivariant covering
space of the special fibre of the model. -/
structure TempObj : Type u where
  /-- The level with its model. -/
  Lv : Level O R A
  /-- The equivariant covering space of the special fibre. -/
  P : CoveringCode Lv.ρs

namespace TempObj

variable {O R A}

/-- A morphism of the tempered category. -/
@[ext]
structure Hom (X Y : TempObj O R A) : Type u where
  /-- The morphism of levels. -/
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

lemma spec_map_comp_f {L L' L'' : FiniteLevel R A} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    Spec.map (CommRingCat.ofHom ((φ ≫ ψ).f : L''.B →+* L.B)) =
      Spec.map (CommRingCat.ofHom (φ.f : L'.B →+* L.B)) ≫
        Spec.map (CommRingCat.ofHom (ψ.f : L''.B →+* L'.B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma spec_map_id_f (L : FiniteLevel R A) :
    Spec.map (CommRingCat.ofHom ((𝟙 L : L ⟶ L).f : L.B →+* L.B)) = 𝟙 _ := by
  rw [← Spec.map_id]
  rfl

/-- The identity morphism of the tempered category. -/
def Hom.id (X : TempObj O R A) : Hom X X where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by rw [spec_map_id_f, Category.comp_id, Category.id_comp]
  h := fun x => x
  continuous_h := continuous_id
  fst_h := fun _ => rfl
  h_act := fun _ _ => rfl

/-- Composition in the tempered category. -/
def Hom.comp {X Y Z : TempObj O R A} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
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

instance : Category (TempObj O R A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp m := Hom.ext (Category.id_comp m.φ) (Category.id_comp m.ψ) rfl
  comp_id m := Hom.ext (Category.comp_id m.φ) (Category.comp_id m.ψ) rfl
  assoc m n p := Hom.ext (Category.assoc m.φ n.φ p.φ) (Category.assoc m.ψ n.ψ p.ψ) rfl

@[simp] lemma id_h (X : TempObj O R A) : Hom.h (𝟙 X) = id := rfl
@[simp] lemma id_ψ (X : TempObj O R A) : Hom.ψ (𝟙 X) = 𝟙 _ := rfl
@[simp] lemma comp_h {X Y Z : TempObj O R A} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).h = ψ.h ∘ φ.h := rfl
@[simp] lemma comp_ψ {X Y Z : TempObj O R A} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).ψ = φ.ψ ≫ ψ.ψ := rfl

end TempObj

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace Level

variable {O R A}

/-- A geometric point of the finite étale cover, as a morphism `Spec Ω → 𝒯`. -/
def point (Lv : Level O R A) (t : Lv.L.B →ₐ[R] Ω) : Spec (CommRingCat.of Ω) ⟶ Lv.c.scheme :=
  Spec.map (CommRingCat.ofHom (t : Lv.L.B →+* Ω)) ≫ Lv.j

lemma point_toSpec (Lv : Level O R A) (t : Lv.L.B →ₐ[R] Ω) :
    Lv.point t ≫ Lv.c.toSpec = Spec.map (CommRingCat.ofHom (valToField O)) := by
  rw [point, Category.assoc, Lv.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp [levelStructureMap, valToField, ← IsScalarTower.algebraMap_apply]

/-- **The specialization** of a geometric point of the finite étale cover in the special fibre of
the model. -/
def sp (Lv : Level O R A) (t : Lv.L.B →ₐ[R] Ω) : Lv.Z :=
  TemperedFundamentalGroups.sp Lv.c.toSpec V hV (Lv.point t) (point_toSpec Lv t)

/-- The specialization map is equivariant for `H⁰`. -/
lemma sp_fibreAct (Lv : Level O R A) (g : Lv.L.H0) (t : Lv.L.B →ₐ[R] Ω) :
    (Lv.sp V hV (FiniteLevel.fibreAct Ω Lv.L g t) : Lv.c.scheme) =
      (Lv.ρ g).hom (Lv.sp V hV t : Lv.c.scheme) := by
  unfold sp
  rw [← coe_sp_comp (hV := hV) (Lv.ρ g).hom (Lv.ρ_toSpec g)]
  congr 2
  rw [point, point, Category.assoc, ← Lv.ρ_j, ← Category.assoc, ← Spec.map_comp]
  rfl

end Level

namespace TempObj

variable {O R A}

/-- The specialization of geometric points is compatible with morphisms. -/
lemma ψ_sp {X Y : TempObj O R A} (m : X ⟶ Y) (t : X.Lv.L.B →ₐ[R] Ω) :
    m.ψ (X.Lv.sp V hV t : X.Lv.c.scheme) = (Y.Lv.sp V hV (t.comp m.φ.f) : Y.Lv.c.scheme) := by
  unfold Level.sp
  rw [← coe_sp_comp (hV := hV) m.ψ m.ψ_toSpec]
  congr 2
  rw [Level.point, Level.point, Category.assoc, m.j_ψ, ← Category.assoc, ← Spec.map_comp]
  rfl

variable (Ω) in
/-- The pairs `(t, p)` of a geometric point `t` of the finite étale cover and a point `p` of the
covering space over its specialization. -/
def PreFibre (X : TempObj O R A) : Type u :=
  {q : (X.Lv.L.B →ₐ[R] Ω) × X.P.carrier // (q.2.1.1 : X.Lv.c.scheme) = X.Lv.sp V hV q.1}

/-- The diagonal action of `H⁰` on the pairs `(t, p)`. -/
instance (X : TempObj O R A) : MulAction X.Lv.L.H0 (PreFibre Ω V hV X) where
  smul g q := ⟨(FiniteLevel.fibreAct Ω X.Lv.L g q.1.1, X.P.act g q.1.2), by
    rw [X.P.act_fst, Level.sp_fibreAct, Level.ρs_apply, q.2]⟩
  one_smul q := by
    apply Subtype.ext
    change (FiniteLevel.fibreAct Ω X.Lv.L 1 q.1.1, X.P.act (1 : X.Lv.L.H0) q.1.2) = q.1
    rw [FiniteLevel.fibreAct_one]
    simp
  mul_smul g h q := by
    apply Subtype.ext
    change (FiniteLevel.fibreAct Ω X.Lv.L (g * h) q.1.1,
        X.P.act ((g * h : X.Lv.L.H0) : X.Lv.L.H) q.1.2) =
      (FiniteLevel.fibreAct Ω X.Lv.L g (FiniteLevel.fibreAct Ω X.Lv.L h q.1.1),
        X.P.act (g : X.Lv.L.H) (X.P.act (h : X.Lv.L.H) q.1.2))
    rw [FiniteLevel.fibreAct_mul, Subgroup.coe_mul, map_mul, Homeomorph.mul_apply]

@[simp] lemma smul_val (X : TempObj O R A) (g : X.Lv.L.H0) (q : PreFibre Ω V hV X) :
    (g • q).1 = (FiniteLevel.fibreAct Ω X.Lv.L g q.1.1, X.P.act g q.1.2) := rfl

variable (Ω) in
/-- **The fibre** of the tempered covering attached to an object over the geometric point:
pairs `(t, p)` modulo `H⁰`. -/
abbrev Fibre (X : TempObj O R A) : Type u :=
  MulAction.orbitRel.Quotient X.Lv.L.H0 (PreFibre Ω V hV X)

/-- The map of pairs induced by a morphism. -/
def preMap {X Y : TempObj O R A} (m : X ⟶ Y) (q : PreFibre Ω V hV X) : PreFibre Ω V hV Y :=
  ⟨(q.1.1.comp m.φ.f, m.h q.1.2), by
    simp only
    rw [m.fst_h, q.2, ψ_sp]⟩

lemma preMap_smul {X Y : TempObj O R A} (m : X ⟶ Y) (g : X.Lv.L.H0) (q : PreFibre Ω V hV X) :
    preMap V hV m (g • q) = (⟨m.φ.r g, FiniteLevel.r_mem_H0 m.φ g.2⟩ : Y.Lv.L.H0) •
      preMap V hV m q := by
  apply Subtype.ext
  simp only [preMap, smul_val]
  rw [FiniteLevel.fibreAct_comp, m.h_act]

/-- The map of fibres induced by a morphism. -/
def fibreMap {X Y : TempObj O R A} (m : X ⟶ Y) : Fibre Ω V hV X → Fibre Ω V hV Y :=
  Quotient.map (preMap V hV m) fun q q' ⟨g, hg⟩ => by
    rw [← hg, preMap_smul]
    exact ⟨_, rfl⟩

end TempObj

/-- **The fibre functor** of the tempered category at the geometric point `Spec Ω → Spec R`. -/
def tempFibre : TempObj O R A ⥤ Type u where
  obj X := TempObj.Fibre Ω V hV X
  map m := TypeCat.ofHom (TempObj.fibreMap V hV m)
  map_id X := by
    ext x
    induction x using Quotient.inductionOn
    rfl
  map_comp m n := by
    ext x
    induction x using Quotient.inductionOn
    rfl

/-- **The tempered fundamental group** of the orbifold `[Spec R / A]` over the valued field
`(K, O)`, at the geometric point `Spec Ω → Spec R` with the valuation `V` on `Ω`: the
automorphism group of the fibre functor on tempered coverings presented through levels with
projective integral models, with the topology of pointwise convergence. -/
abbrev temperedPi1 : Type u := FibreAut (tempFibre O R A V hV)

end

end TemperedFundamentalGroups
