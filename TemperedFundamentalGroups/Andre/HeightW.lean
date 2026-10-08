/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.LengthW
import TemperedFundamentalGroups.Andre.WEdgeLifting
import TemperedFundamentalGroups.Andre.TateObject

/-!
# The height-corrected length on members (Blueprint §10.3.8, I6)

Scheme case. For a member `X` of `galClassW` with a presentation `P : Pres x X` and a morphism
`a : X ⟶ X₀` to the Tate object, the components of the special fibre of the level that are not
contracted by the model map to the Tate model `𝒯` form the set `ν` (`Pres.tateNu`); the model map
does not depend on `a` (`Pres.ψ_eq`: the level of `X₀` is `(R, 1)`, and `j` is dominant). The
**height-corrected length condition** of a fibre element `γ` relative to `g`
(`Pres.HCW`) is `CurveConfig.HC` with the x-length weights and `ν`, between the vertices of `g`
and `γ`: `Q − 2h ≤ ℓ` (Blueprint §10.3.8).

* `Pres.hcw_map` (**monotonicity**): along morphisms of members, from (X1)–(X3) of
  `Statement.HarmonicX` (`CurveConfig.hc_map`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) {x : R}
  (T : TateObject.Data O R)

namespace Pres

variable {X : TempObj O R A} (P : Pres x X)

/-- **Model maps to the Tate object are unique.** -/
lemma ψ_eq (f f' : P.U ⟶ TateObject.X₀ (A := A) T) : f.ψ = f'.ψ := by
  have hf : f.φ.f = f'.φ.f := (TateObject.subsingleton_fibre (A := A)).elim _ _
  haveI : IsSchemeTheoreticallyDominant P.U.Lv.j := P.dom
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated (TateObject.X₀ T).Lv.c.toSpec
    (by rw [f.ψ_toSpec, f'.ψ_toSpec]) P.U.Lv.j ?_
  rw [f.j_ψ, f'.j_ψ, hf]

/-- The map of special fibres to the Tate model. -/
def tateMap (a : X ⟶ TateObject.X₀ (A := A) T) : P.Lv.Z → (TateObject.X₀ (A := A) T).Lv.Z :=
  specialFibreMap (P.iso.inv ≫ a).ψ (P.iso.inv ≫ a).ψ_toSpec

lemma tateMap_eq (a a' : X ⟶ TateObject.X₀ (A := A) T) : P.tateMap T a = P.tateMap T a' := by
  funext z
  apply Subtype.ext
  change (P.iso.inv ≫ a).ψ z.1 = (P.iso.inv ≫ a').ψ z.1
  rw [P.ψ_eq T (P.iso.inv ≫ a) (P.iso.inv ≫ a')]

/-- **The components not contracted over the Tate model.** -/
def tateNu (a : X ⟶ TateObject.X₀ (A := A) T) : irreducibleComponents P.Lv.Z → Prop :=
  fun i => ¬ CurveConfig.Contr (K := curveConfig P.Lv.Z P.hdim) (P.tateMap T a) i

/-- **The height-corrected length condition** `Q − 2h ≤ ℓ` between the fibre elements `g` and
`γ` of a member. -/
def HCW (a : X ⟶ TateObject.X₀ (A := A) T) (ϖ : O) (g γ : (tempFibre O R A V hV).obj X)
    (ℓ : ℝ≥0∞) : Prop :=
  CurveConfig.HC (P.D.weight ϖ) (P.tateNu T a)
    (P.vtx V hV ((tempFibre O R A V hV).map P.iso.hom g))
    (P.vtx V hV ((tempFibre O R A V hV).map P.iso.hom γ)) ℓ

end Pres

section Map

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

omit [IsReduced R] [Subsingleton A] [CharZero K] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma WData.weight_ne_top {Lv : Level O R A} (D : WData x Lv) (ϖ : O) (z : Lv.Z) :
    D.weight ϖ z ≠ ⊤ := by
  unfold WData.weight
  split_ifs <;> simp

/-- **Monotonicity of the height-corrected length condition** along morphisms of members. -/
theorem Pres.hcw_map (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {X Y : TempObj O R A} (P : Pres x X) (Q : Pres x Y) (m : X ⟶ Y)
    (aY : Y ⟶ TateObject.X₀ (A := A) T) (g γ : (tempFibre O R A V hV).obj X) (ℓ : ℝ≥0∞)
    (H : P.HCW V hV T (m ≫ aY) ϖ g γ ℓ) :
    Q.HCW V hV T aY ϖ ((tempFibre O R A V hV).map m g) ((tempFibre O R A V hV).map m γ) ℓ := by
  let mm : P.U ⟶ Q.U := P.iso.inv ≫ m ≫ Q.iso.hom
  have key : ∀ γ, (tempFibre O R A V hV).map Q.iso.hom ((tempFibre O R A V hV).map m γ) =
      (tempFibre O R A V hV).map mm ((tempFibre O R A V hV).map P.iso.hom γ) := fun γ => by
    simp only [mm, Functor.map_comp_apply, Functor.map_hom_inv'_apply]
  unfold Pres.HCW at H ⊢
  rw [key, key, vtx_map, vtx_map]
  have hNC := fun i hi => curveConfig_contr_or P.hdim Q.hdim (continuous_specialFibreMap _ _)
    (isClosedMap_specialFibreMap mm) i hi
  have hw := WData.isHarmonicWeight hX hN ϖ hϖ mm P.D Q.D P.hdim Q.hdim
  refine CurveConfig.hc_map (continuous_covMap P Q mm) (covMap_fst P Q mm) hNC
    (curveConfig_injective_C Q.hdim) hw (WData.weight_ne_top P.D ϖ)
    (CurveConfig.isWalkLifting_of_isEdgeLifting (continuous_covMap P Q mm) (covMap_fst P Q mm)
      hNC (curveConfig_injective_C Q.hdim) hw
      (WData.isEdgeLifting hX hN ϖ hϖ mm P.D Q.D P.hdim Q.hdim)) ?_ _ _ ℓ H
  -- the components not contracted over `𝒯`
  intro t ht hc hνQ hcP
  obtain ⟨i, hi⟩ := ht
  rw [CurveConfig.lab_of hi] at hc hcP
  obtain ⟨i', hi', hii'⟩ := CurveConfig.map_gen_of_not_contr (covMap_fst P Q mm) hNC hi hc
  rw [CurveConfig.img, CurveConfig.lab_of hi'] at hνQ
  apply hνQ
  obtain ⟨y, hy⟩ := hcP
  refine ⟨y, ?_⟩
  have hcomp : P.tateMap T (m ≫ aY) = Q.tateMap T aY ∘ specialFibreMap mm.ψ mm.ψ_toSpec := by
    funext z
    apply Subtype.ext
    change (P.iso.inv ≫ m ≫ aY).ψ z.1 = (Q.iso.inv ≫ aY).ψ (mm.ψ z.1)
    simp only [mm, comp_ψ, Scheme.Hom.comp_apply]
    congr 1
    have h := congrArg (fun f => f.ψ) Q.iso.hom_inv_id
    simp only [comp_ψ] at h
    rw [← Scheme.Hom.comp_apply Q.iso.hom.ψ Q.iso.inv.ψ, h]
    rfl
  have hy' : Q.tateMap T aY '' (specialFibreMap mm.ψ mm.ψ_toSpec ''
      (curveConfig P.Lv.Z P.hdim).C i) = {y} := by
    rw [← hy, hcomp]
    exact (Set.image_comp _ _ _).symm
  exact (congrArg (fun s => Q.tateMap T aY '' s) hii').symm.trans hy'

end Map

end

end TemperedFundamentalGroups
