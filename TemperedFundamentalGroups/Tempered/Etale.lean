/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.Topology
import TemperedFundamentalGroups.Tempered.Level

/-!
# The étale fundamental group of `[Spec R / A]`

The finite étale covers of the orbifold `[Spec R / A]` are the `A`-equivariant finite étale
covers of `Spec R`: finite étale `R`-algebras `B` with an action of `A` by ring automorphisms
that are semilinear over the action of `A` on `R` (`EquivEtale R A`, coded by presentations so
that the category is small). The fibre functor at the geometric point `Spec Ω → Spec R` sends
`B` to `B →ₐ[R] Ω`, and

`etalePi1 R A Ω := Aut (etaleFibre R A Ω)`

is the étale fundamental group `π₁ᵉᵗ([Spec R / A], ȳ)` with its profinite topology. For `A`
trivial this is Grothendieck's `π₁ᵉᵗ(Spec R, ȳ)` (the automorphism group of the fibre functor on
finite étale covers, which are the spectra of finite étale `R`-algebras).
-/

universe u

open CategoryTheory

namespace TemperedFundamentalGroups

noncomputable section

variable (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]
  (Ω : Type u) [CommRing Ω] [Algebra R Ω]

/-- **An `A`-equivariant finite étale `R`-algebra**, i.e. a finite étale cover of
`[Spec R / A]`: a coded finite étale `R`-algebra with a lift of the action of `A`. -/
structure EquivEtale extends EtaleCode R where
  /-- The action of `A`. -/
  act : A →* SemilinearAut R A (LevelRing R n I)
  /-- It lifts the action on `R`. -/
  act_a : ∀ a, (act a).a = a

namespace EquivEtale

variable {R A}

/-- The algebra of an equivariant finite étale algebra. -/
abbrev B (X : EquivEtale R A) : Type u := LevelRing R X.n X.I

/-- An `A`-equivariant `R`-algebra map `Y.B → X.B`, i.e. a morphism of covers `X ⟶ Y`. -/
@[ext]
structure Hom (X Y : EquivEtale R A) : Type u where
  /-- The map of algebras (contravariant). -/
  f : Y.B →ₐ[R] X.B
  /-- Equivariance. -/
  f_act : ∀ a y, f ((Y.act a).σ y) = (X.act a).σ (f y)

instance : Category (EquivEtale R A) where
  Hom := Hom
  id X := ⟨AlgHom.id R X.B, fun _ _ => rfl⟩
  comp φ ψ := ⟨φ.f.comp ψ.f, fun a y => by simp [ψ.f_act, φ.f_act]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] lemma id_f (X : EquivEtale R A) : Hom.f (𝟙 X) = AlgHom.id R X.B := rfl
@[simp] lemma comp_f {X Y Z : EquivEtale R A} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).f = φ.f.comp ψ.f := rfl

end EquivEtale

/-- The fibre functor on finite étale covers of `[Spec R / A]` at `Spec Ω → Spec R`. -/
def etaleFibre : EquivEtale R A ⥤ Type u where
  obj X := X.B →ₐ[R] Ω
  map φ := TypeCat.ofHom fun t => t.comp φ.f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The étale fundamental group** of the orbifold `[Spec R / A]` at the geometric point
`Spec Ω → Spec R`: the automorphism group of the fibre functor on `A`-equivariant finite étale
covers, with the topology of pointwise convergence. -/
abbrev etalePi1 : Type u := FibreAut (etaleFibre R A Ω)

end

end TemperedFundamentalGroups
