/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Equivariant covering spaces, coded inside `Z × ℕ`

Let `Z` be a topological space with an action of a group `G` by homeomorphisms. A *covering
code* over `Z` is a `G`-equivariant covering space `P → Z` whose points are points of `Z × ℕ`
lying over their first coordinate: the carrier is a subset of `Z × ℕ` with *some* topology for
which the first projection is a covering map. Every covering space with countable fibres is
isomorphic to one of this form; connected covering spaces of the spaces we use (special fibres of
proper models, which are noetherian) have countable fibres, so nothing is lost up to
isomorphism. The point of the coding is size: covering codes over `Z : Type u` form a
`Type u`, so categories built from them are small and their fibre-functor automorphism groups
live in `Type u`.

## Main definitions

* `CoveringCode ρ`: a `G`-equivariant covering space over `Z`, for `ρ : G →* (Z ≃ₜ Z)`.
* `CoveringCode.Hom P P' ψ r`: a continuous map `P → P'` over `ψ : Z → Z'`, equivariant along
  `r : G →* G'`.
* `CoveringCode.fibre P z`: the fibre of `P` over `z`.
* `CoveringCode.trivial ρ n α`: the trivial covering `Z × {0, …, n-1}` with the diagonal action,
  for a finite `G`-set `α : G →* Equiv.Perm (Fin n)`.
-/

universe u

open Topology

namespace TemperedFundamentalGroups

variable {Z : Type u} [TopologicalSpace Z] {G : Type u} [Group G]

/-- A `G`-equivariant covering space of `Z`, coded as a subset of `Z × ℕ` (with its own
topology) lying over the first coordinate. -/
structure CoveringCode (ρ : G →* (Z ≃ₜ Z)) : Type u where
  /-- The points of the covering space. -/
  carrier : Set (Z × ℕ)
  /-- The topology of the covering space. -/
  top : TopologicalSpace carrier
  /-- The first projection is a covering map. -/
  isCoveringMap : IsCoveringMap (X := Z) (fun x : carrier => x.1.1)
  /-- The action of `G` on the covering space. -/
  act : G →* (carrier ≃ₜ carrier)
  /-- The action lies over the action on `Z`. -/
  act_fst : ∀ (g : G) (x : carrier), (act g x).1.1 = ρ g x.1.1

attribute [instance] CoveringCode.top

namespace CoveringCode

variable {ρ : G →* (Z ≃ₜ Z)}

/-- The projection of a covering code to the base. -/
def proj (P : CoveringCode ρ) (x : P.carrier) : Z := x.1.1

lemma continuous_proj (P : CoveringCode ρ) : Continuous P.proj := P.isCoveringMap.continuous

/-- The fibre of a covering code over a point of the base. -/
def fibre (P : CoveringCode ρ) (z : Z) : Type u := {x : P.carrier // x.1.1 = z}

section Hom

variable {Z' : Type u} [TopologicalSpace Z'] {G' : Type u} [Group G'] {ρ' : G' →* (Z' ≃ₜ Z')}

/-- A morphism of covering codes over a continuous map `ψ : Z → Z'` of bases, equivariant
along a group homomorphism `r : G →* G'`. -/
@[ext]
structure Hom (P : CoveringCode ρ) (P' : CoveringCode ρ') (ψ : Z → Z') (r : G →* G') where
  /-- The underlying map. -/
  toFun : P.carrier → P'.carrier
  continuous_toFun : Continuous toFun
  fst_toFun : ∀ x, (toFun x).1.1 = ψ x.1.1
  toFun_act : ∀ g x, toFun (P.act g x) = P'.act (r g) (toFun x)

/-- The identity morphism of a covering code. -/
def Hom.id (P : CoveringCode ρ) : Hom P P id (MonoidHom.id G) where
  toFun := fun x => x
  continuous_toFun := continuous_id
  fst_toFun := fun _ => rfl
  toFun_act := fun _ _ => rfl

variable {Z'' : Type u} [TopologicalSpace Z''] {G'' : Type u} [Group G'']
  {ρ'' : G'' →* (Z'' ≃ₜ Z'')}

/-- Composition of morphisms of covering codes. -/
def Hom.comp {P : CoveringCode ρ} {P' : CoveringCode ρ'} {P'' : CoveringCode ρ''}
    {ψ : Z → Z'} {ψ' : Z' → Z''} {r : G →* G'} {r' : G' →* G''}
    (h : Hom P P' ψ r) (h' : Hom P' P'' ψ' r') : Hom P P'' (ψ' ∘ ψ) (r'.comp r) where
  toFun := h'.toFun ∘ h.toFun
  continuous_toFun := h'.continuous_toFun.comp h.continuous_toFun
  fst_toFun := fun x => by simp [h'.fst_toFun, h.fst_toFun]
  toFun_act := fun g x => by simp [h.toFun_act, h'.toFun_act]

/-- A morphism of covering codes maps the fibre over `z` to the fibre over `ψ z`. -/
def Hom.fibreMap {P : CoveringCode ρ} {P' : CoveringCode ρ'} {ψ : Z → Z'} {r : G →* G'}
    (h : Hom P P' ψ r) {z : Z} {z' : Z'} (hz : ψ z = z') (x : P.fibre z) : P'.fibre z' :=
  ⟨h.toFun x.1, by rw [h.fst_toFun, x.2, hz]⟩

/-- Transport a morphism of covering codes along equalities of the base map and the group
homomorphism. -/
def Hom.cast {P : CoveringCode ρ} {P' : CoveringCode ρ'} {ψ₁ ψ₂ : Z → Z'} {r₁ r₂ : G →* G'}
    (h : Hom P P' ψ₁ r₁) (hψ : ψ₁ = ψ₂) (hr : r₁ = r₂) : Hom P P' ψ₂ r₂ := hψ ▸ hr ▸ h

@[simp] lemma Hom.cast_toFun {P : CoveringCode ρ} {P' : CoveringCode ρ'} {ψ₁ ψ₂ : Z → Z'}
    {r₁ r₂ : G →* G'} (h : Hom P P' ψ₁ r₁) (hψ : ψ₁ = ψ₂) (hr : r₁ = r₂) :
    (h.cast hψ hr).toFun = h.toFun := by
  subst hψ hr; rfl

end Hom

section Trivial

/-- The projection `Z ×ˢ N → Z` (subspace topology, `ℕ` discrete) is a covering map. -/
lemma isCoveringMap_fst_prod (N : Set ℕ) :
    IsCoveringMap (X := Z) (fun x : (Set.univ ×ˢ N : Set (Z × ℕ)) => x.1.1) := by
  intro z
  let H : (fun x : (Set.univ ×ˢ N : Set (Z × ℕ)) => x.1.1) ⁻¹' Set.univ ≃ₜ
      ↥(Set.univ : Set Z) × ↥N :=
    { toFun := fun x => (⟨x.1.1.1, Set.mem_univ _⟩, ⟨x.1.1.2, x.1.2.2⟩)
      invFun := fun y => ⟨⟨(y.1.1, y.2.1), Set.mem_univ _, y.2.2⟩, Set.mem_univ _⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact IsEvenlyCovered.to_isEvenlyCovered_preimage (I := N) ⟨inferInstance, Set.univ,
    Set.mem_univ _, isOpen_univ, by simp, H, fun _ => rfl⟩

/-- The trivial covering code `Z × {0, …, n-1}` with the diagonal action given by a finite
`G`-set `α`. -/
def trivial (ρ : G →* (Z ≃ₜ Z)) (n : ℕ) (α : G →* Equiv.Perm (Fin n)) : CoveringCode ρ where
  carrier := Set.univ ×ˢ {k | k < n}
  top := inferInstance
  isCoveringMap := isCoveringMap_fst_prod _
  act :=
    { toFun := fun g =>
        { toFun := fun x => ⟨(ρ g x.1.1, (α g ⟨x.1.2, x.2.2⟩ : ℕ)), Set.mem_univ _, (α g _).2⟩
          invFun := fun x => ⟨((ρ g).symm x.1.1, ((α g).symm ⟨x.1.2, x.2.2⟩ : ℕ)), Set.mem_univ _,
            ((α g).symm _).2⟩
          left_inv := fun x => by ext <;> simp
          right_inv := fun x => by ext <;> simp
          continuous_toFun := by
            apply Continuous.subtype_mk
            refine Continuous.prodMk ((ρ g).continuous.comp (by fun_prop)) ?_
            exact continuous_subtype_val.comp
              ((continuous_of_discreteTopology (f := fun k : {k : ℕ | k < n} =>
                (⟨(α g ⟨k.1, k.2⟩ : ℕ), (α g _).2⟩ : {k : ℕ | k < n}))).comp
              (Continuous.subtype_mk (by fun_prop) fun x => x.2.2))
          continuous_invFun := by
            apply Continuous.subtype_mk
            refine Continuous.prodMk ((ρ g).symm.continuous.comp (by fun_prop)) ?_
            exact continuous_subtype_val.comp
              ((continuous_of_discreteTopology (f := fun k : {k : ℕ | k < n} =>
                (⟨((α g).symm ⟨k.1, k.2⟩ : ℕ), ((α g).symm _).2⟩ : {k : ℕ | k < n}))).comp
              (Continuous.subtype_mk (by fun_prop) fun x => x.2.2)) }
      map_one' := by ext x <;> simp
      map_mul' := fun g h => by ext x <;> simp [Equiv.Perm.mul_apply] }
  act_fst := fun _ _ => rfl

end Trivial

end CoveringCode

end TemperedFundamentalGroups
