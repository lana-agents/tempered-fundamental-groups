/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Orbifold.FibreAut

/-!
# Automorphisms of a fibre functor as limits over Galois objects

Let `Φ : C ⥤ Type w` be a functor and `𝒢` a class of objects of `C` ("Galois objects") such that

* (gal) for `G ∈ 𝒢`, `Aut G` acts transitively on `Φ G` (`IsGaloisClass`);
* (dom) every finite family of pointed objects `(X_k, x_k)` is dominated by a pointed Galois
  object `(G, g)`: there are `f_k : G ⟶ X_k` with `Φ f_k g = x_k` (`IsDominating`);
* (rig) two morphisms `G ⟶ X` out of `G ∈ 𝒢` that agree at one fibre element are equal
  (`IsRigid`).

The pointed Galois objects `(G, g)` form a cofiltered (thin) category `PtGal Φ 𝒢`. Automorphisms
of `Φ` correspond to *compatible families* `γ_{(G,g)} ∈ Φ G` (K1, `FibreAut.compatibleEquiv`):
every compatible family `γ` defines `FibreAut.ofCompatible γ` with `α_G(g) = γ_{(G,g)}`.

König's lemma (K2, `exists_compatible_of_finite_nonempty`): if finite nonempty subsets
`S_{(G,g)} ⊆ Φ G` are mapped into each other by pointed morphisms, then a compatible family
through them exists. Combined: `exists_fibreAut_of_finite_nonempty`. See Blueprint §10.3.3.
-/

universe w v u

open CategoryTheory Pi1.Orbifold Pi1.Orbifold.FibreAut

namespace TemperedFundamentalGroups

namespace GaloisLimit

variable {C : Type u} [Category.{v} C] (Φ : C ⥤ Type w) (𝒢 : ObjectProperty C)

/-- (gal) For `G ∈ 𝒢`, `Aut G` acts simply transitively on `Φ G`. -/
def IsGaloisClass : Prop :=
  ∀ G, 𝒢 G → ∀ x y : Φ.obj G, ∃! σ : G ≅ G, Φ.map σ.hom x = y

/-- (dom) Every finite family of pointed objects is dominated by a pointed object of `𝒢`. -/
def IsDominating : Prop :=
  ∀ (n : ℕ) (P : Fin n → Σ X : C, Φ.obj X), ∃ G, 𝒢 G ∧ ∃ g : Φ.obj G,
    ∃ f : ∀ k, G ⟶ (P k).1, ∀ k, Φ.map (f k) g = (P k).2

/-- (rig) Morphisms out of objects of `𝒢` agreeing at one fibre element are equal. -/
def IsRigid : Prop :=
  ∀ G, 𝒢 G → ∀ {X : C} (f f' : G ⟶ X) (g : Φ.obj G), Φ.map f g = Φ.map f' g → f = f'

/-- Pointed objects of `𝒢`. -/
structure PtGal where
  /-- The underlying object. -/
  G : C
  mem : 𝒢 G
  /-- The base point. -/
  g : Φ.obj G

variable {Φ 𝒢}

instance : Category.{v} (PtGal Φ 𝒢) where
  Hom p q := {f : p.G ⟶ q.G // Φ.map f p.g = q.g}
  id p := ⟨𝟙 _, Functor.map_id_apply Φ _ _⟩
  comp f f' := ⟨f.1 ≫ f'.1, by rw [Functor.map_comp_apply, f.2, f'.2]⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f f' f'' := Subtype.ext (Category.assoc f.1 f'.1 f''.1)

/-- A family `γ_{(G,g)} ∈ Φ G` compatible with all pointed morphisms. -/
def IsCompatible (γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G) : Prop :=
  ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q), Φ.map f.1 (γ p) = γ q

lemma dom₁ (hdom : IsDominating Φ 𝒢) (X : C) (x : Φ.obj X) :
    ∃ p : PtGal Φ 𝒢, ∃ f : p.G ⟶ X, Φ.map f p.g = x := by
  obtain ⟨G, hG, g, f, hf⟩ := hdom 1 ![⟨X, x⟩]
  exact ⟨⟨G, hG, g⟩, f 0, hf 0⟩

lemma dom₂ (hdom : IsDominating Φ 𝒢) (X : C) (x : Φ.obj X) (Y : C) (y : Φ.obj Y) :
    ∃ p : PtGal Φ 𝒢, ∃ f : p.G ⟶ X, ∃ f' : p.G ⟶ Y, Φ.map f p.g = x ∧ Φ.map f' p.g = y := by
  obtain ⟨G, hG, g, f, hf⟩ := hdom 2 ![⟨X, x⟩, ⟨Y, y⟩]
  exact ⟨⟨G, hG, g⟩, f 0, f 1, hf 0, hf 1⟩

/-- The category of pointed Galois objects is cofiltered. -/
lemma isCofiltered (hdom : IsDominating Φ 𝒢) (hrig : IsRigid Φ 𝒢) :
    IsCofiltered (PtGal Φ 𝒢) where
  cone_objs p q := by
    obtain ⟨r, f, f', hf, hf'⟩ := dom₂ hdom p.G p.g q.G q.g
    exact ⟨r, ⟨f, hf⟩, ⟨f', hf'⟩, trivial⟩
  cone_maps p q f f' := ⟨p, 𝟙 p, by
    rw [Category.id_comp, Category.id_comp]
    exact Subtype.ext (hrig _ p.mem f.1 f'.1 p.g (f.2.trans f'.2.symm))⟩
  nonempty := by
    obtain ⟨G, hG, g, -⟩ := hdom 0 Fin.elim0
    exact ⟨⟨G, hG, g⟩⟩

section K1

variable (hdom : IsDominating Φ 𝒢)

/-- A chosen pointed Galois object dominating `(X, x)`. -/
noncomputable def choosePt (X : C) (x : Φ.obj X) : PtGal Φ 𝒢 := (dom₁ hdom X x).choose

/-- The chosen morphism from `choosePt` to `X`. -/
noncomputable def chooseHom (X : C) (x : Φ.obj X) : (choosePt hdom X x).G ⟶ X :=
  (dom₁ hdom X x).choose_spec.choose

lemma map_chooseHom (X : C) (x : Φ.obj X) :
    Φ.map (chooseHom hdom X x) (choosePt hdom X x).g = x :=
  (dom₁ hdom X x).choose_spec.choose_spec

/-- The extension of a family over pointed Galois objects to all fibres. -/
noncomputable def extend (γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G) (X : C) (x : Φ.obj X) : Φ.obj X :=
  Φ.map (chooseHom hdom X x) (γ (choosePt hdom X x))

variable (hrig : IsRigid Φ 𝒢) {γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G} (hγ : IsCompatible γ)
include hdom hrig hγ

lemma map_eq_map {X : C} {p q : PtGal Φ 𝒢} (f : p.G ⟶ X) (f' : q.G ⟶ X)
    (h : Φ.map f p.g = Φ.map f' q.g) : Φ.map f (γ p) = Φ.map f' (γ q) := by
  obtain ⟨r, a, a', ha, ha'⟩ := dom₂ hdom p.G p.g q.G q.g
  have he : a ≫ f = a' ≫ f' := hrig _ r.mem _ _ r.g (by
    rw [Functor.map_comp_apply, Functor.map_comp_apply, ha, ha', h])
  rw [← hγ (p := r) ⟨a, ha⟩, ← hγ (p := r) ⟨a', ha'⟩, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, he]

lemma extend_eq {X : C} {x : Φ.obj X} (p : PtGal Φ 𝒢) (f : p.G ⟶ X) (hf : Φ.map f p.g = x) :
    extend hdom γ X x = Φ.map f (γ p) :=
  map_eq_map hdom hrig hγ _ _ ((map_chooseHom hdom X x).trans hf.symm)

lemma extend_naturality {X Y : C} (u : X ⟶ Y) (x : Φ.obj X) :
    extend hdom γ Y (Φ.map u x) = Φ.map u (extend hdom γ X x) := by
  rw [extend_eq hdom hrig hγ (choosePt hdom X x) (chooseHom hdom X x ≫ u)
    (by rw [Functor.map_comp_apply, map_chooseHom]), Functor.map_comp_apply]
  rfl

lemma extend_pt (p : PtGal Φ 𝒢) : extend hdom γ p.G p.g = γ p := by
  rw [extend_eq hdom hrig hγ p (𝟙 _) (Functor.map_id_apply Φ _ _), Functor.map_id_apply]

lemma extend_bijective (hgal : IsGaloisClass Φ 𝒢) (X : C) :
    Function.Bijective (extend hdom γ X) := by
  refine ⟨fun x x' hx => ?_, fun y => ?_⟩
  · obtain ⟨r, f, f', hf, hf'⟩ := dom₂ hdom X x X x'
    rw [extend_eq hdom hrig hγ r f hf, extend_eq hdom hrig hγ r f' hf'] at hx
    rw [← hf, ← hf', hrig _ r.mem f f' _ hx]
  · obtain ⟨p, f, hf⟩ := dom₁ hdom X y
    obtain ⟨σ, hσ, -⟩ := hgal _ p.mem (γ p) p.g
    refine ⟨Φ.map f (Φ.map σ.hom p.g), ?_⟩
    rw [extend_eq hdom hrig hγ p (σ.hom ≫ f) (Functor.map_comp_apply _ _ _ _),
      Functor.map_comp_apply, hσ, hf]

end K1

end GaloisLimit

namespace FibreAut

open GaloisLimit

variable {C : Type u} [Category.{v} C] {Φ : C ⥤ Type w} {𝒢 : ObjectProperty C}

/-- **K1.** The automorphism of `Φ` defined by a compatible family over pointed Galois
objects. -/
noncomputable def ofCompatible (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G) (hγ : IsCompatible γ) :
    FibreAut Φ :=
  show Φ ≅ Φ from NatIso.ofComponents
    (fun X => (Equiv.ofBijective _ (extend_bijective hdom hrig hγ hgal X)).toIso)
    fun {X Y} u => by
      ext x
      exact extend_naturality hdom hrig hγ u x

lemma ofCompatible_app (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G) (hγ : IsCompatible γ)
    (X : C) (x : Φ.obj X) : (ofCompatible hgal hdom hrig γ hγ).app X x = extend hdom γ X x :=
  rfl

/-- **K1.** `(ofCompatible γ).app G g = γ (G, g)`. -/
lemma ofCompatible_app_pt (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G) (hγ : IsCompatible γ)
    (p : PtGal Φ 𝒢) : (ofCompatible hgal hdom hrig γ hγ).app p.G p.g = γ p :=
  extend_pt hdom hrig hγ p

lemma ofCompatible_app_of_mem (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G) (hγ : IsCompatible γ)
    (G : C) (hG : 𝒢 G) (g : Φ.obj G) :
    (ofCompatible hgal hdom hrig γ hγ).app G g = γ ⟨G, hG, g⟩ :=
  extend_pt hdom hrig hγ ⟨G, hG, g⟩

/-- The compatible family of an automorphism of `Φ`: its values at pointed Galois objects. -/
def toCompatible (α : FibreAut Φ) (p : PtGal Φ 𝒢) : Φ.obj p.G := α.app p.G p.g

lemma isCompatible_toCompatible (α : FibreAut Φ) : IsCompatible (toCompatible (𝒢 := 𝒢) α) :=
  fun {p q} f => by
    rw [toCompatible, toCompatible, ← app_naturality, f.2]

/-- **K1.** Automorphisms of `Φ` are the compatible families over pointed Galois objects. -/
noncomputable def compatibleEquiv (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) : FibreAut Φ ≃ {γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G // IsCompatible γ} where
  toFun α := ⟨toCompatible α, isCompatible_toCompatible α⟩
  invFun γ := ofCompatible hgal hdom hrig γ.1 γ.2
  left_inv α := by
    ext X x
    rw [ofCompatible_app, extend]
    change Φ.map (chooseHom hdom X x) (α.app _ (choosePt hdom X x).g) = α.app X x
    rw [← app_naturality, map_chooseHom]
  right_inv γ := Subtype.ext (funext fun p => ofCompatible_app_pt hgal hdom hrig γ.1 γ.2 p)

end FibreAut

namespace GaloisLimit

section K2

variable {C : Type u} [Category.{v} C] {Φ : C ⥤ Type w} {𝒢 : ObjectProperty C}
  (S : ∀ p : PtGal Φ 𝒢, Set (Φ.obj p.G))
  (hS : ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q), Φ.map f.1 '' S p ⊆ S q)

/-- The inverse system of the subsets `S p`. -/
def subsetSystem : PtGal Φ 𝒢 ⥤ Type w where
  obj p := S p
  map f := TypeCat.ofHom fun s => ⟨Φ.map f.1 s.1, hS f ⟨s.1, s.2, rfl⟩⟩
  map_id p := by
    ext s
    exact Functor.map_id_apply Φ _ _
  map_comp f f' := by
    ext s
    exact Functor.map_comp_apply Φ f.1 f'.1 _

include hS

/-- **K2 (König).** Finite nonempty subsets mapped into each other by pointed morphisms admit a
compatible family through them. -/
theorem exists_compatible_of_finite_nonempty (hdom : IsDominating Φ 𝒢) (hrig : IsRigid Φ 𝒢)
    (hfin : ∀ p, (S p).Finite) (hne : ∀ p, (S p).Nonempty) :
    ∃ γ : ∀ p : PtGal Φ 𝒢, Φ.obj p.G, IsCompatible γ ∧ ∀ p, γ p ∈ S p := by
  haveI := isCofiltered hdom hrig
  haveI : ∀ p, Finite ((subsetSystem S hS).obj p) := fun p => (hfin p).to_subtype
  haveI : ∀ p, Nonempty ((subsetSystem S hS).obj p) := fun p => (hne p).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system (subsetSystem S hS)
  exact ⟨fun p => (u p).1, fun f => congrArg Subtype.val (hu f), fun p => (u p).2⟩

/-- **K1 + K2.** An automorphism of `Φ` whose values at the pointed Galois objects lie in
prescribed finite nonempty subsets mapped into each other by pointed morphisms. -/
theorem exists_fibreAut_of_finite_nonempty (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (hfin : ∀ p, (S p).Finite) (hne : ∀ p, (S p).Nonempty) :
    ∃ α : FibreAut Φ, ∀ p : PtGal Φ 𝒢, α.app p.G p.g ∈ S p := by
  obtain ⟨γ, hγ, hγS⟩ := exists_compatible_of_finite_nonempty S hS hdom hrig hfin hne
  exact ⟨FibreAut.ofCompatible hgal hdom hrig γ hγ, fun p => by
    rw [FibreAut.ofCompatible_app_pt]
    exact hγS p⟩

end K2

end GaloisLimit

end TemperedFundamentalGroups
