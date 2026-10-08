/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Centres of valuations on schemes (Blueprint §10.3.8, I4)

Let `X` be a scheme, `F` a field and `g : Spec F ⟶ X` (a "generic point"). A valuation subring
`V ⊆ F` has **centre** `x ∈ X` (`ValuativeCentre.IsCentre g V x`) if `g` extends to
`l : Spec V ⟶ X` sending the closed point to `x`.

* `exists_isCentre`: every specialization `x` of the image of `g` is the centre of some valuation
  subring of `F` (stalk at `x`, then a valuation ring dominating it, Mathlib's
  `IsLocalRing.exists_factor_valuationRing`);
* `lift_unique`: on a scheme separated over an affine scheme, extensions of `g` to `Spec V` are
  unique (valuative criterion); in particular the centre of `V` is unique;
* `exists_lift`: on a scheme universally closed over `Spec A`, `g` extends to `Spec V` as soon as
  the composite `Spec F ⟶ Spec A` does (valuative criterion);
* `CentreDetermines g x`: at most one valuation subring of `F` has centre `x` (true at the generic
  points of the components of the special fibre of a model whose local rings there are valuation
  rings of `F`, e.g. DVRs with fraction field `F`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups

noncomputable section

namespace ValuativeCentre

variable {X : Scheme.{u}} {F : Type u} [Field F]

/-- The generic point `Spec F ⟶ Spec V` of the spectrum of a valuation subring. -/
abbrev genMap (V : ValuationSubring F) :
    Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (algebraMap V F))

/-- `x` is the **centre** of the valuation subring `V` with respect to `g : Spec F ⟶ X`. -/
def IsCentre (g : Spec (CommRingCat.of F) ⟶ X) (V : ValuationSubring F) (x : X) : Prop :=
  ∃ l : Spec (CommRingCat.of V) ⟶ X, genMap V ≫ l = g ∧ l (closedPoint V) = x

/-- **The centre `x` determines the valuation** (with respect to `g`). -/
def CentreDetermines (g : Spec (CommRingCat.of F) ⟶ X) (x : X) : Prop :=
  ∀ V₁ V₂ : ValuationSubring F, IsCentre g V₁ x → IsCentre g V₂ x → V₁ = V₂

/-- **Existence of valuations with a given centre**: every specialization of the image of `g` is
the centre of a valuation subring. -/
theorem exists_isCentre (g : Spec (CommRingCat.of F) ⟶ X) {x : X}
    (h : g (closedPoint F) ⤳ x) : ∃ V : ValuationSubring F, IsCentre g V x := by
  let f₀ : X.presheaf.stalk x ⟶ CommRingCat.of F :=
    X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo g
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f₀.hom
  let f' : X.presheaf.stalk x ⟶ CommRingCat.of V :=
    CommRingCat.ofHom (f₀.hom.codRestrict V.toSubring hV)
  haveI : IsLocalHom f'.hom := hloc
  refine ⟨V, Spec.map f' ≫ X.fromSpecStalk x, ?_, ?_⟩
  · have hf : f' ≫ CommRingCat.ofHom (algebraMap V F) = f₀ := rfl
    rw [genMap, ← Category.assoc, ← Spec.map_comp, hf, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- Morphisms from the spectrum of a valuation subring to an affine scheme are determined by
their restriction to the generic point. -/
lemma hom_ext_affine (V : ValuationSubring F) {A : CommRingCat.{u}}
    (h₁ h₂ : Spec (CommRingCat.of V) ⟶ Spec A) (h : genMap V ≫ h₁ = genMap V ≫ h₂) :
    h₁ = h₂ := by
  obtain ⟨a₁, rfl⟩ := Spec.map_surjective h₁
  obtain ⟨a₂, rfl⟩ := Spec.map_surjective h₂
  rw [genMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact congrArg (fun φ : A ⟶ CommRingCat.of F => φ a) h'

/-- **Uniqueness of extensions** over a separated morphism to an affine scheme. -/
theorem lift_unique {A : CommRingCat.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    (V : ValuationSubring F) (l₁ l₂ : Spec (CommRingCat.of V) ⟶ X)
    (h : genMap V ≫ l₁ = genMap V ≫ l₂) : l₁ = l₂ := by
  have hf : l₂ ≫ f = l₁ ≫ f :=
    hom_ext_affine V _ _ (by rw [← Category.assoc, ← h, Category.assoc])
  let S : ValuativeCommSq f :=
    { R := V, K := F, i₁ := genMap V ≫ l₁, i₂ := l₁ ≫ f, commSq := ⟨by simp⟩ }
  have hS := IsSeparated.valuativeCriterion f S
  have e := hS.elim ⟨l₁, rfl, rfl⟩ ⟨l₂, h.symm, hf⟩
  exact congrArg CommSq.LiftStruct.l e

/-- **The centre is unique**. -/
theorem centre_unique {A : CommRingCat.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    {g : Spec (CommRingCat.of F) ⟶ X} {V : ValuationSubring F} {x y : X}
    (hx : IsCentre g V x) (hy : IsCentre g V y) : x = y := by
  obtain ⟨l₁, h₁, rfl⟩ := hx
  obtain ⟨l₂, h₂, rfl⟩ := hy
  rw [lift_unique f V l₁ l₂ (h₁.trans h₂.symm)]

/-- **Existence of extensions** over a universally closed morphism. -/
theorem exists_lift {A : CommRingCat.{u}} (f : X ⟶ Spec A) [UniversallyClosed f]
    (g : Spec (CommRingCat.of F) ⟶ X) (V : ValuationSubring F) (a : A ⟶ CommRingCat.of V)
    (hg : g ≫ f = genMap V ≫ Spec.map a) :
    ∃ l : Spec (CommRingCat.of V) ⟶ X, genMap V ≫ l = g ∧ l ≫ f = Spec.map a := by
  have hE : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq f :=
    { R := V, K := F, i₁ := g, i₂ := Spec.map a, commSq := ⟨hg⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hE S).exists_lift
  exact ⟨l, hl₁, hl₂⟩

end ValuativeCentre

end

end TemperedFundamentalGroups
