/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import TemperedFundamentalGroups.SemiAnbd.SemiGraph

/-!
# Anabelioids and semi-graphs of anabelioids (Blueprint §12.2, A1–A4)

A connected anabelioid ([SemiAnbd] §2, after [Mzk4] §1) is a Galois category. With a fibre
functor `F` it is equivalent to the category of finite continuous `Aut F`-sets, `Aut F` profinite
(Mathlib, `PreGaloisCategory.functorToContAction`). Following Blueprint §12.0 (D1) we therefore
present semi-graphs of anabelioids by profinite groups (one choice of base points).

* `anabelioidGroup F`: `Aut F` as a profinite group, `anabelioidEquiv F : C ≌ ContAction`.
* `SemiGraphOfAnabelioids 𝔾` (**A2**): profinite vertex and edge groups with continuous branch
  homomorphisms `Π_e → Π_v` for the branches abutting to `v`.
* `SemiGraphOfAnabelioids.Cov` (**A3**): the finite `𝒢`-coverings `B(𝒢)` ([SemiAnbd] Def. 2.1):
  finite sets `S_v` with continuous `Π_v`-actions (open stabilizers) and, for every closed edge,
  a `Π_e`-equivariant gluing bijection `S_{v₁} ≃ S_{v₂}` between the two branches; morphisms are
  families of equivariant maps compatible with the gluings.
* `SemiGraphOfAnabelioids.fibre v₀` and **`SemiGraphOfAnabelioids.Pi v₀ := Aut (fibre v₀)`**, the
  fundamental group `Π_𝒢` (as an abstract group).
* `SemiGraphOfAnabelioids.vertHom v₀ : Π_{v₀} →* Π_𝒢` (**A4**, the verticial homomorphism) and
  `SemiGraphOfAnabelioids.edgeHom` for edges abutting to `v₀`.

That `B(𝒢)` is a Galois category for connected `𝔾` (so that `Π_𝒢` is profinite and `B(𝒢)` is
`B(Π_𝒢)`) is not formalized (Blueprint §12.2, A5).
-/

universe u w u₁ u₂

open CategoryTheory

namespace TemperedFundamentalGroups

section Anabelioid

open PreGaloisCategory
open scoped FintypeCatDiscrete

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{u₂})
  [FiberFunctor F]

/-- **A1**: the profinite group of a connected anabelioid with a fibre functor. -/
noncomputable abbrev anabelioidGroup : ProfiniteGrp := ProfiniteGrp.of (Aut F)

/-- **A1**: a connected anabelioid is the category of finite continuous sets of its group. -/
noncomputable def anabelioidEquiv : C ≌ ContAction FintypeCat (Aut F) :=
  (functorToContAction F).asEquivalence

end Anabelioid

/-- **A2**: a **semi-graph of anabelioids** on a semi-graph `𝔾`, in group form: profinite vertex
and edge groups and continuous branch homomorphisms for the abutting branches. -/
structure SemiGraphOfAnabelioids (𝔾 : SemiGraph.{u}) where
  /-- The vertex groups. -/
  vGrp : 𝔾.V → ProfiniteGrp.{w}
  /-- The edge groups. -/
  eGrp : 𝔾.E → ProfiniteGrp.{w}
  /-- The branch homomorphisms. -/
  br : ∀ (e : 𝔾.E) (b : Bool) (v : 𝔾.V), 𝔾.ζ (e, b) = some v → (eGrp e ⟶ vGrp v)

namespace SemiGraphOfAnabelioids

variable {𝔾 : SemiGraph.{u}} (𝒢 : SemiGraphOfAnabelioids.{u, w} 𝔾)

/-- The edge group acting on a vertex set through a branch. -/
def brHom (e : 𝔾.E) (b : Bool) (v : 𝔾.V) (h : 𝔾.ζ (e, b) = some v) : 𝒢.eGrp e →* 𝒢.vGrp v :=
  (𝒢.br e b v h).hom.toMonoidHom

/-- **A3**: a finite `𝒢`-covering. -/
structure Cov where
  /-- The vertex sets. -/
  S : 𝔾.V → Type w
  [fin : ∀ v, Finite (S v)]
  [act : ∀ v, MulAction (𝒢.vGrp v) (S v)]
  /-- The actions are continuous: stabilizers are open. -/
  isOpen_stabilizer : ∀ v (x : S v), IsOpen (MulAction.stabilizer (𝒢.vGrp v) x : Set (𝒢.vGrp v))
  /-- The gluing along a closed edge. -/
  glue : ∀ (e : 𝔾.E) (v₁ v₂ : 𝔾.V), 𝔾.ζ (e, true) = some v₁ → 𝔾.ζ (e, false) = some v₂ →
    S v₁ ≃ S v₂
  glue_smul : ∀ (e : 𝔾.E) (v₁ v₂ : 𝔾.V) (h₁ : 𝔾.ζ (e, true) = some v₁)
    (h₂ : 𝔾.ζ (e, false) = some v₂) (g : 𝒢.eGrp e) (x : S v₁),
    glue e v₁ v₂ h₁ h₂ (𝒢.brHom e true v₁ h₁ g • x) =
      𝒢.brHom e false v₂ h₂ g • glue e v₁ v₂ h₁ h₂ x

namespace Cov

attribute [instance] fin act

variable {𝒢}

/-- Morphisms of `𝒢`-coverings: equivariant maps compatible with the gluings. -/
@[ext]
structure Hom (X Y : Cov 𝒢) where
  /-- The vertex maps. -/
  f : ∀ v, X.S v → Y.S v
  map_smul : ∀ v (g : 𝒢.vGrp v) (x : X.S v), f v (g • x) = g • f v x
  map_glue : ∀ (e : 𝔾.E) (v₁ v₂ : 𝔾.V) (h₁ : 𝔾.ζ (e, true) = some v₁)
    (h₂ : 𝔾.ζ (e, false) = some v₂) (x : X.S v₁),
    f v₂ (X.glue e v₁ v₂ h₁ h₂ x) = Y.glue e v₁ v₂ h₁ h₂ (f v₁ x)

instance : Category (Cov 𝒢) where
  Hom := Hom
  id X := ⟨fun _ x ↦ x, fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
  comp φ ψ := ⟨fun v ↦ ψ.f v ∘ φ.f v, fun v g x ↦ by simp [φ.map_smul, ψ.map_smul],
    fun e v₁ v₂ h₁ h₂ x ↦ by simp [φ.map_glue, ψ.map_glue]⟩

@[simp]
lemma id_f (X : Cov 𝒢) (v : 𝔾.V) (x : X.S v) : Hom.f (𝟙 X) v x = x := rfl

@[simp]
lemma comp_f {X Y Z : Cov 𝒢} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (v : 𝔾.V) (x : X.S v) :
    Hom.f (φ ≫ ψ) v x = ψ.f v (φ.f v x) := rfl

@[ext]
lemma hom_ext {X Y : Cov 𝒢} {φ ψ : X ⟶ Y} (h : ∀ v x, φ.f v x = ψ.f v x) : φ = ψ :=
  Hom.ext (funext fun v ↦ funext (h v))

end Cov

/-- The **fibre functor** at a vertex `v₀`: `X ↦ S_{v₀}`. -/
def fibre (v₀ : 𝔾.V) : Cov 𝒢 ⥤ Type w where
  obj X := X.S v₀
  map φ := TypeCat.ofHom (φ.f v₀)

/-- The fundamental group `Π_𝒢` of a semi-graph of anabelioids, based at `v₀`: the automorphisms
of the fibre functor. -/
abbrev Pi (v₀ : 𝔾.V) : Type _ := Aut (𝒢.fibre v₀)

/-- The action of `Π_{v₀}` on the fibre at `v₀`, as an automorphism of the fibre functor. -/
def vertAut (v₀ : 𝔾.V) (g : 𝒢.vGrp v₀) : 𝒢.Pi v₀ :=
  NatIso.ofComponents
    (fun X ↦ (Equiv.toIso (MulAction.toPerm g : Equiv.Perm (X.S v₀))))
    (fun {X Y} φ ↦ by
      ext x
      exact (φ.map_smul v₀ g x).symm)

@[simp]
lemma vertAut_hom_app (v₀ : 𝔾.V) (g : 𝒢.vGrp v₀) (X : Cov 𝒢) (x : X.S v₀) :
    (𝒢.vertAut v₀ g).hom.app X x = (g • x : X.S v₀) := rfl

/-- **A4**: the verticial homomorphism `Π_{v₀} →* Π_𝒢`. -/
def vertHom (v₀ : 𝔾.V) : 𝒢.vGrp v₀ →* 𝒢.Pi v₀ where
  toFun := 𝒢.vertAut v₀
  map_one' := by
    ext X x
    exact one_smul (𝒢.vGrp v₀) (show X.S v₀ from x)
  map_mul' g h := by
    ext X x
    exact mul_smul g h (show X.S v₀ from x)

/-- **A4**: the edge-like homomorphism `Π_e →* Π_𝒢` for a branch of `e` abutting to `v₀`. -/
def edgeHom (v₀ : 𝔾.V) (e : 𝔾.E) (b : Bool) (h : 𝔾.ζ (e, b) = some v₀) : 𝒢.eGrp e →* 𝒢.Pi v₀ :=
  (𝒢.vertHom v₀).comp (𝒢.brHom e b v₀ h)

end SemiGraphOfAnabelioids

end TemperedFundamentalGroups
