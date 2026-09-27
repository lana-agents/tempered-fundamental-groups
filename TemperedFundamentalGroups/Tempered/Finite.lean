/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.Topology
import TemperedFundamentalGroups.Tempered.Level

/-!
# The étale fundamental group of `[Spec R / A]` through Galois levels

The category `FiniteObj R A Ω` has objects `(L, S)` with `L` a finite (Galois) level of the
orbifold `[Spec R / A]` and `S` a finite `G_L`-set (coded as `Fin n` with an action), and
morphisms pairs of a morphism of levels and an equivariant map. Its fibre functor
`finFibre (L, S) = S` realizes `(L, S)` as the finite étale cover `(Spec B_L × S)/G_L⁰` of
`[Spec R / A]`, whose geometric fibre at `ȳ` is `S` (Galois condition). By Galois theory
(SGA 1, V) every finite étale cover of `[Spec R / A]` arises this way and morphisms are realized
after refinement, so

`etalePi1 R A Ω := Aut (finFibre)`

is the étale fundamental group `π₁ᵉᵗ([Spec R / A], ȳ)`; the identification with the automorphism
group of the fibre functor on finite étale covers is Blueprint item E1.
-/

universe u

open CategoryTheory

namespace TemperedFundamentalGroups

variable (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]
  (Ω : Type u) [CommRing Ω] [Algebra R Ω]

/-- An object of the category of finite étale covers of `[Spec R / A]` presented through a
Galois level: a level `L` and a finite `G_L`-set `Fin n`. -/
structure FiniteObj : Type u where
  /-- The Galois level. -/
  L : FiniteLevel R A Ω
  /-- The cardinality of the `G_L`-set. -/
  n : ℕ
  /-- The action of `G_L`. -/
  α : L.G →* Equiv.Perm (Fin n)

namespace FiniteObj

variable {R A Ω}

/-- A morphism of finite objects: a morphism of levels and an equivariant map. -/
@[ext]
structure Hom (X Y : FiniteObj R A Ω) : Type u where
  /-- The morphism of levels. -/
  φ : X.L ⟶ Y.L
  /-- The map of `G`-sets. -/
  h : Fin X.n → Fin Y.n
  /-- Equivariance. -/
  h_α : ∀ g x, h (X.α g x) = Y.α (φ.r g) (h x)

noncomputable instance : Category (FiniteObj R A Ω) where
  Hom := Hom
  id X := ⟨𝟙 X.L, id, fun _ _ => rfl⟩
  comp φ ψ := ⟨φ.φ ≫ ψ.φ, ψ.h ∘ φ.h, fun g x => by simp [φ.h_α, ψ.h_α]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] lemma id_h (X : FiniteObj R A Ω) : Hom.h (𝟙 X) = id := rfl
@[simp] lemma comp_h {X Y Z : FiniteObj R A Ω} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).h = ψ.h ∘ φ.h := rfl

end FiniteObj

/-- The fibre functor on finite objects: `(L, Fin n) ↦ Fin n`. -/
noncomputable def finFibre : FiniteObj R A Ω ⥤ Type u where
  obj X := ULift.{u} (Fin X.n)
  map φ := TypeCat.ofHom fun x => ⟨φ.h x.down⟩

/-- **The étale fundamental group** of `[Spec R / A]` at the geometric point `Ω`, as the
automorphism group of the fibre functor on finite covers presented through Galois levels. -/
abbrev etalePi1 : Type u := FibreAut (finFibre R A Ω)

end TemperedFundamentalGroups
