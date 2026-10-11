/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChangeComp
import TemperedFundamentalGroups.Tempered.FieldChange

/-!
# Change of the valued field and composition (Blueprint §11, F8)

For an extension of valued fields `(K, O) → (K', O')`, maps of orbifolds
`μ₁ : OrbMap R A R₁ A₁` (over `K`) and `μ₂ : OrbMap R₁ A₁ R' A'` (`R'` a `K'`-algebra),

`temperedPi1FieldMap hO (μ₁.comp μ₂) = temperedPi1Map μ₁ ∘ temperedPi1FieldMap hO μ₂`

(`temperedPi1FieldMap_comp`). It is proved with the comparison morphism
`fc₂ (bc₁ Y) ⟶ fc₁₂ Y` of tempered coverings over `O'` (`TempObj.fcCmpHom`): both models are
scheme-theoretic images in the same scheme `𝒯 ×_O O'`, and the comparison of levels is
`cmpLevel` of F4.

In particular (`μ₂ = OrbMap.id`) every field change factors through the *pure* field change
`temperedPi1FieldMap hO (OrbMap.id R' A')` (same ring `R'`, base `(K', O') → (K, O)`)
followed by `temperedPi1Map μ` over `O` (`temperedPi1FieldMap_eq_comp`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {K' : Type u} [Field K'] [Algebra K K'] {O' : ValuationSubring K'}
  (hO : O'.comap (algebraMap K K') = O)
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R₁ : Type u} [CommRing R₁] [Algebra K R₁] [Algebra R R₁] [IsScalarTower K R R₁]
  {A₁ : Type u} [Group A₁] [MulSemiringAction A₁ R₁]
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  [Algebra R₁ R'] [IsScalarTower K R₁ R'] [Algebra R R'] [IsScalarTower R R₁ R']
  [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']
  (μ₁ : OrbMap R A R₁ A₁) (μ₂ : OrbMap R₁ A₁ R' A')

namespace TempObj

variable (Y : TempObj O R A)

/-- The two maps to `𝒯 ×_O O'` agree after the comparison of levels. -/
lemma fcCmp_w : (Y.baseChange μ₁).Lv.fcJ hO μ₂ =
    Spec.map (CommRingCat.ofHom ((Y.Lv.L.cmpLevel μ₁ μ₂).f :
      (Y.Lv.L.baseChange (μ₁.comp μ₂)).B →+* ((Y.Lv.L.baseChange μ₁).baseChange μ₂).B)) ≫
      Y.Lv.fcJ hO (μ₁.comp μ₂) := by
  refine Y.Lv.c.bc_hom_ext (valMap hO) ?_ ?_
  · have h := Y.cmp_j_ψ μ₁ μ₂
    rw [Category.comp_id] at h
    exact ((Y.baseChange μ₁).Lv.fcJ_fst hO μ₂).trans (h.trans (((Category.assoc _ _ _).trans
      (congrArg (Spec.map (CommRingCat.ofHom ((Y.Lv.L.cmpLevel μ₁ μ₂).f :
        (Y.Lv.L.baseChange (μ₁.comp μ₂)).B →+* ((Y.Lv.L.baseChange μ₁).baseChange μ₂).B)) ≫ ·)
        (Y.Lv.fcJ_fst hO (μ₁.comp μ₂)))).symm))
  · exact ((Y.baseChange μ₁).Lv.fcJ_toSpec hO μ₂).trans
      ((spec_levelStructureMap O' R' A' (Y.Lv.L.cmpLevel μ₁ μ₂)).trans
      (((Category.assoc _ _ _).trans
      (congrArg (Spec.map (CommRingCat.ofHom ((Y.Lv.L.cmpLevel μ₁ μ₂).f :
        (Y.Lv.L.baseChange (μ₁.comp μ₂)).B →+* ((Y.Lv.L.baseChange μ₁).baseChange μ₂).B)) ≫ ·)
        (Y.Lv.fcJ_toSpec hO (μ₁.comp μ₂)))).symm))

/-- The comparison map of models `𝒯''_{fc₂ (bc₁ Y)} ⟶ 𝒯''_{fc₁₂ Y}` (images in `𝒯 ×_O O'`). -/
def fcCmpψ : ((Y.baseChange μ₁).Lv.fcI hO μ₂).scheme ⟶ (Y.Lv.fcI hO (μ₁.comp μ₂)).scheme :=
  ((Y.baseChange μ₁).Lv.fcC hO).imageMap ((Y.baseChange μ₁).Lv.fcJ hO μ₂)
    (Y.Lv.fcJ hO (μ₁.comp μ₂)) (𝟙 ((Y.baseChange μ₁).Lv.fcC hO).scheme) _
    ((Category.comp_id _).trans (Y.fcCmp_w hO μ₁ μ₂))

@[reassoc]
lemma fcCmpψ_imgι : Y.fcCmpψ hO μ₁ μ₂ ≫ (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (μ₁.comp μ₂)) =
    ((Y.baseChange μ₁).Lv.fcC hO).imgι ((Y.baseChange μ₁).Lv.fcJ hO μ₂) := by
  exact (ModelCode.imageMap_imgι _ _ _ _ _ _).trans (Category.comp_id _)

lemma fcCmpψ_toSpec : Y.fcCmpψ hO μ₁ μ₂ ≫ (Y.Lv.fcI hO (μ₁.comp μ₂)).toSpec =
    ((Y.baseChange μ₁).Lv.fcI hO μ₂).toSpec := by
  calc Y.fcCmpψ hO μ₁ μ₂ ≫ (Y.Lv.fcI hO (μ₁.comp μ₂)).toSpec
      = Y.fcCmpψ hO μ₁ μ₂ ≫ (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (μ₁.comp μ₂)) ≫
          (Y.Lv.fcC hO).toSpec := by rw [ModelCode.imgι_toSpec]
    _ = ((Y.baseChange μ₁).Lv.fcC hO).imgι ((Y.baseChange μ₁).Lv.fcJ hO μ₂) ≫
          (Y.Lv.fcC hO).toSpec := Y.fcCmpψ_imgι_assoc hO μ₁ μ₂ _
    _ = ((Y.baseChange μ₁).Lv.fcI hO μ₂).toSpec := ModelCode.imgι_toSpec _ _

lemma toImg_fcCmpψ : ((Y.baseChange μ₁).Lv.fieldChange hO μ₂).j ≫ Y.fcCmpψ hO μ₁ μ₂ =
    Spec.map (CommRingCat.ofHom ((Y.Lv.L.cmpLevel μ₁ μ₂).f :
      (Y.Lv.L.baseChange (μ₁.comp μ₂)).B →+* ((Y.Lv.L.baseChange μ₁).baseChange μ₂).B)) ≫
      (Y.Lv.fieldChange hO (μ₁.comp μ₂)).j :=
  ((Y.baseChange μ₁).Lv.fcC hO).toImg_imageMap ((Y.baseChange μ₁).Lv.fcJ hO μ₂)
    (Y.Lv.fcJ hO (μ₁.comp μ₂)) (𝟙 ((Y.baseChange μ₁).Lv.fcC hO).scheme) _
    ((Category.comp_id _).trans (Y.fcCmp_w hO μ₁ μ₂))

/-- The comparison map of special fibres. -/
def fcCmpS : ((Y.baseChange μ₁).Lv.fieldChange hO μ₂).Z →
    (Y.Lv.fieldChange hO (μ₁.comp μ₂)).Z :=
  specialFibreMap (Y.fcCmpψ hO μ₁ μ₂) (Y.fcCmpψ_toSpec hO μ₁ μ₂)

lemma fcS_fcCmpS (z : ((Y.baseChange μ₁).Lv.fieldChange hO μ₂).Z) :
    Y.Lv.fcS hO (μ₁.comp μ₂) (Y.fcCmpS hO μ₁ μ₂ z) = (Y.baseChange μ₁).Lv.fcS hO μ₂ z := by
  apply Subtype.ext
  change Y.Lv.c.bcFst (valMap hO) (((Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (μ₁.comp μ₂)))
    (Y.fcCmpψ hO μ₁ μ₂ z.1)) = Y.Lv.c.bcFst (valMap hO)
      ((((Y.baseChange μ₁).Lv.fcC hO).imgι ((Y.baseChange μ₁).Lv.fcJ hO μ₂)) z.1)
  refine Eq.trans ?_ (congrArg (fun f : ((Y.baseChange μ₁).Lv.fcI hO μ₂).scheme ⟶
    (Y.Lv.fcC hO).scheme => Y.Lv.c.bcFst (valMap hO) (f z.1)) (Y.fcCmpψ_imgι hO μ₁ μ₂))
  rw [Scheme.Hom.comp_apply]

lemma fcCmpH_aux (q : ((Y.baseChange μ₁).fieldChange hO μ₂).P.carrier) :
    (CoveringCode.pullbackPt (Y.baseChange μ₁).P ((Y.baseChange μ₁).Lv.fcS hO μ₂) q).1.1 =
      Y.Lv.fcS hO (μ₁.comp μ₂) (Y.fcCmpS hO μ₁ μ₂ q.1.1) :=
  (Y.fcS_fcCmpS hO μ₁ μ₂ q.1.1).symm

/-- The comparison map of covering spaces. -/
def fcCmpH : ((Y.baseChange μ₁).fieldChange hO μ₂).P.carrier →
    (Y.fieldChange hO (μ₁.comp μ₂)).P.carrier :=
  CoveringCode.pullbackLiftFun Y.P (ψ := Y.Lv.fcS hO (μ₁.comp μ₂))
    (fun q => Y.fcCmpS hO μ₁ μ₂ q.1.1)
    (fun q => CoveringCode.pullbackPt (Y.baseChange μ₁).P ((Y.baseChange μ₁).Lv.fcS hO μ₂) q)
    (Y.fcCmpH_aux hO μ₁ μ₂)

lemma pullbackPt_fcCmpH (q : ((Y.baseChange μ₁).fieldChange hO μ₂).P.carrier) :
    CoveringCode.pullbackPt Y.P (Y.Lv.fcS hO (μ₁.comp μ₂)) (Y.fcCmpH hO μ₁ μ₂ q) =
      CoveringCode.pullbackPt (Y.baseChange μ₁).P ((Y.baseChange μ₁).Lv.fcS hO μ₂) q :=
  CoveringCode.pullbackPt_liftFun _ _ _ _ _

lemma fcEnd_cmp (g : ((Y.Lv.L.baseChange μ₁).baseChange μ₂).H) :
    (Y.baseChange μ₁).Lv.fcEnd hO ((Y.Lv.L.baseChange μ₁).bcPr μ₂ g) =
      Y.Lv.fcEnd hO (Y.Lv.L.bcPr (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g)) := by
  rw [FiniteLevel.bcPr_cmpR]
  rfl

lemma imgEnd_fcCmpψ (g : ((Y.Lv.L.baseChange μ₁).baseChange μ₂).H) :
    (Y.baseChange μ₁).Lv.imgEnd hO μ₂ g ≫ Y.fcCmpψ hO μ₁ μ₂ =
      Y.fcCmpψ hO μ₁ μ₂ ≫ Y.Lv.imgEnd hO (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g) := by
  refine (cancel_mono ((Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (μ₁.comp μ₂)))).1 ?_
  have h1 : ((Y.baseChange μ₁).Lv.imgEnd hO μ₂ g ≫ Y.fcCmpψ hO μ₁ μ₂) ≫
        (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (μ₁.comp μ₂)) =
      (Y.baseChange μ₁).Lv.imgEnd hO μ₂ g ≫
          ((Y.baseChange μ₁).Lv.fcC hO).imgι ((Y.baseChange μ₁).Lv.fcJ hO μ₂) := by
    rw [Category.assoc, fcCmpψ_imgι]
    rfl
  have h2 := (Y.baseChange μ₁).Lv.imgEnd_imgι hO μ₂ g
  have h3 : ((Y.baseChange μ₁).Lv.fcC hO).imgι ((Y.baseChange μ₁).Lv.fcJ hO μ₂) ≫
        (Y.baseChange μ₁).Lv.fcEnd hO ((Y.Lv.L.baseChange μ₁).bcPr μ₂ g) =
      ((Y.baseChange μ₁).Lv.fcC hO).imgι ((Y.baseChange μ₁).Lv.fcJ hO μ₂) ≫
        Y.Lv.fcEnd hO (Y.Lv.L.bcPr (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g)) := by
    rw [fcEnd_cmp]
    rfl
  have h4 := (Y.fcCmpψ_imgι_assoc hO μ₁ μ₂
    (Y.Lv.fcEnd hO (Y.Lv.L.bcPr (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g)))).symm
  have h5 : Y.fcCmpψ hO μ₁ μ₂ ≫ (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (μ₁.comp μ₂)) ≫
        Y.Lv.fcEnd hO (Y.Lv.L.bcPr (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g)) =
      (Y.fcCmpψ hO μ₁ μ₂ ≫ Y.Lv.imgEnd hO (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g)) ≫
        (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (μ₁.comp μ₂)) := by
    rw [Category.assoc, Level.imgEnd_imgι]
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- **The comparison morphism** `fc₂ (bc₁ Y) ⟶ fc₁₂ Y` of tempered coverings over `O'`. -/
def fcCmpHom : (Y.baseChange μ₁).fieldChange hO μ₂ ⟶ Y.fieldChange hO (μ₁.comp μ₂) where
  φ := Y.Lv.L.cmpLevel μ₁ μ₂
  ψ := Y.fcCmpψ hO μ₁ μ₂
  ψ_toSpec := Y.fcCmpψ_toSpec hO μ₁ μ₂
  j_ψ := Y.toImg_fcCmpψ hO μ₁ μ₂
  h := Y.fcCmpH hO μ₁ μ₂
  continuous_h := CoveringCode.continuous_pullbackLiftFun Y.P (Y.fcCmpH_aux hO μ₁ μ₂)
    ((continuous_specialFibreMap _ _).comp
      ((Y.baseChange μ₁).fieldChange hO μ₂).P.continuous_proj)
    (CoveringCode.continuous_pullbackPt (Y.baseChange μ₁).P)
  fst_h _ := rfl
  h_act g q := by
    refine CoveringCode.pullback_ext Y.P (Y.Lv.fcS hO (μ₁.comp μ₂)) (Subtype.ext ?_) ?_
    · change Y.fcCmpψ hO μ₁ μ₂ ((Y.baseChange μ₁).Lv.imgEnd hO μ₂ g q.1.1.1) =
        Y.Lv.imgEnd hO (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g) (Y.fcCmpψ hO μ₁ μ₂ q.1.1.1)
      rw [← Scheme.Hom.comp_apply, imgEnd_fcCmpψ, Scheme.Hom.comp_apply]
    · change ((Y.baseChange μ₁).P.act ((Y.Lv.L.baseChange μ₁).bcPr μ₂ g)
          (CoveringCode.pullbackPt (Y.baseChange μ₁).P ((Y.baseChange μ₁).Lv.fcS hO μ₂) q)).1.2 =
        (Y.P.act (Y.Lv.L.bcPr (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g))
          (CoveringCode.pullbackPt Y.P (Y.Lv.fcS hO (μ₁.comp μ₂)) (Y.fcCmpH hO μ₁ μ₂ q))).1.2
      rw [pullbackPt_fcCmpH, FiniteLevel.bcPr_cmpR]
      rfl

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R₁ Ω] [IsScalarTower K R₁ Ω]
  [IsScalarTower R R₁ Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  [IsScalarTower R₁ R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- The comparison morphism is compatible with the fibre isomorphisms. -/
lemma fcFibreEquiv_fcCmpHom (z : Fibre Ω V hV' ((Y.baseChange μ₁).fieldChange hO μ₂)) :
    fcFibreEquiv hO (μ₁.comp μ₂) V hV' Y (fibreMap V hV' (Y.fcCmpHom hO μ₁ μ₂) z) =
      bcFibreEquiv μ₁ V (comap_eq hO V hV') Y
        (fcFibreEquiv hO μ₂ V hV' (Y.baseChange μ₁) z) := by
  induction z using Quotient.inductionOn with | h q => ?_
  apply congrArg Quotient.mk''
  apply Subtype.ext
  refine Prod.ext ?_ (pullbackPt_fcCmpH hO μ₁ μ₂ Y q.1.2)
  ext b
  change q.1.1 (Y.Lv.L.cmpF μ₁ μ₂ (Y.Lv.L.bcι (μ₁.comp μ₂) b)) = _
  rw [FiniteLevel.cmpF_bcι]
  rfl

end TempObj

section Map

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R₁ Ω] [IsScalarTower K R₁ Ω]
  [IsScalarTower R R₁ Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  [IsScalarTower R₁ R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

omit [Algebra R₁ R'] [IsScalarTower K R₁ R'] [IsScalarTower R R₁ R'] [Algebra R₁ Ω]
  [IsScalarTower K R₁ Ω] [IsScalarTower R R₁ Ω] [IsScalarTower R₁ R' Ω]
  [IsScalarTower K R' Ω] [Algebra K R₁] [Algebra R R₁] [IsScalarTower K R R₁] in
lemma temperedPi1FieldMap_app (μ : OrbMap R A R' A') (γ : temperedPi1 O' R' A' V hV')
    (Y : TempObj O R A) (y : TempObj.Fibre Ω V (TempObj.comap_eq hO V hV') Y) :
    (temperedPi1FieldMap hO μ V hV' γ).app Y y = TempObj.fcFibreEquiv hO μ V hV' Y
      (γ.app (Y.fieldChange hO μ) ((TempObj.fcFibreEquiv hO μ V hV' Y).symm y)) := rfl

/-- **Change of the valued field is compatible with composition**:
`fc (μ₁ ∘ μ₂) = temperedPi1Map μ₁ ∘ fc μ₂`. -/
theorem temperedPi1FieldMap_comp (γ : temperedPi1 O' R' A' V hV') :
    temperedPi1FieldMap hO (μ₁.comp μ₂) V hV' γ =
      temperedPi1Map μ₁ V (TempObj.comap_eq hO V hV') (temperedPi1FieldMap hO μ₂ V hV' γ) := by
  ext Y y
  rw [temperedPi1FieldMap_app, temperedPi1Map_app, temperedPi1FieldMap_app]
  set z := (TempObj.fcFibreEquiv hO μ₂ V hV' (Y.baseChange μ₁)).symm
    ((TempObj.bcFibreEquiv μ₁ V (TempObj.comap_eq hO V hV') Y).symm y) with hz
  have hy : (TempObj.fcFibreEquiv hO (μ₁.comp μ₂) V hV' Y).symm y =
      TempObj.fibreMap V hV' (Y.fcCmpHom hO μ₁ μ₂) z := by
    rw [Equiv.symm_apply_eq, TempObj.fcFibreEquiv_fcCmpHom, hz, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  rw [hy, show γ.app _ (TempObj.fibreMap V hV' (Y.fcCmpHom hO μ₁ μ₂) z) =
    TempObj.fibreMap V hV' (Y.fcCmpHom hO μ₁ μ₂) (γ.app _ z) from
      FibreAut.app_naturality γ (Y.fcCmpHom hO μ₁ μ₂) z, TempObj.fcFibreEquiv_fcCmpHom]

end Map

end

end TemperedFundamentalGroups
