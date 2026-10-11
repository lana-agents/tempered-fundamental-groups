/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.FieldChangeImage
import TemperedFundamentalGroups.Models.RestrictScalars
import TemperedFundamentalGroups.FibreFunctor.SectionRestrict

/-!
# The pure change of the valued field is an isomorphism (Blueprint §11, F8)

Let `(K, O) → (K', O')` be an extension of valued fields with `O'` **finite over `O`**
(`(valMap hO).Finite`; e.g. `K'/K` finite and `O` henselian), and `R'` a `K'`-algebra. Then
the pure field change

`temperedPi1FieldMap hO (OrbMap.id R' A') : temperedPi1 O' R' A' →* temperedPi1 O R' A'`

is an **isomorphism of topological groups** (`temperedPi1FieldEquiv`,
`bijective_temperedPi1FieldMap_pure`).

Proof: restriction of scalars of models (`ModelCode.restrictScalars`, a closed immersion
`ℙᵐ_{O'} ⟶ ℙᴺ_{O}`) turns every tempered covering `X'` over `(K', O')` into one over `(K, O)`,
`TempObj.rsObj X'`, with the same level, the same model scheme and the same covering space (the
special fibres agree since `O'` is local and finite over `O`). The comparison morphisms
`TempObj.rsW : fc (rsObj X') ⟶ X'` (projection from the scheme-theoretic image in
`𝒯' ×_O O'`) are bijective on fibres and natural, and `TempObj.rsπ : rsObj (fc Y) ⟶ Y` is
compatible with them, which is the abstract criterion `SectionData` of
`FibreFunctor/SectionRestrict.lean`.

Consequently (with `Tempered/FieldChangeImage.lean`) in the scheme case, for `R'` finite étale
over `R`, the field change `temperedPi1FieldMap hO μ` is an open embedding onto the stabilizer
of the base point of `Spec R' → Spec R`, a subgroup of finite index
(`isOpenEmbedding_temperedPi1FieldMap`, `range_temperedPi1FieldMap`,
`finiteIndex_range_temperedPi1FieldMap`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {K' : Type u} [Field K'] [Algebra K K'] {O' : ValuationSubring K'}
  (hO : O'.comap (algebraMap K K') = O) (hfin : (valMap hO).Finite)
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']

lemma levelStructureMap_comp_valMap (L : FiniteLevel R' A') :
    (levelStructureMap O' R' A' L).comp (valMap hO) = levelStructureMap O R' A' L := by
  ext o
  change algebraMap R' L.B (algebraMap K' R' (algebraMap K K' (o : K))) =
    algebraMap R' L.B (algebraMap K R' o)
  rw [← IsScalarTower.algebraMap_apply K K' R']

namespace FiniteLevel

/-- The comparison `id^* L ⟶ L` of levels. -/
def bcIdφ (L : FiniteLevel R' A') : L.baseChange (OrbMap.id R' A') ⟶ L where
  f := { L.bcι (OrbMap.id R' A') with
    commutes' := fun r => by
      change L.bcι (OrbMap.id R' A') (algebraMap R' L.B r) = _
      rw [FiniteLevel.bcι_algebraMap]
      rfl }
  r := L.bcPr (OrbMap.id R' A')
  r_a g := L.bcPr_a (OrbMap.id R' A') g
  f_σ g y := (L.bcσ_bcι (OrbMap.id R' A') g y).symm

lemma bcIdφ_f_apply (L : FiniteLevel R' A') (y : L.B) :
    (bcIdφ L).f y = L.bcι (OrbMap.id R' A') y := rfl

end FiniteLevel

namespace Level

variable (Lv : Level O' R' A')

/-- **Restriction of scalars of a level with a model**: the same level, the model viewed over
`O` (`ModelCode.restrictScalars`). -/
abbrev rs : Level O R' A' where
  L := Lv.L
  c := Lv.c.restrictScalars hfin
  j := Lv.j ≫ (Lv.c.rsIso hfin).hom
  j_toSpec := by
    rw [Category.assoc, ModelCode.rsIso_hom_toSpec, ← Category.assoc, Lv.j_toSpec,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, levelStructureMap_comp_valMap]
  ρ := (Lv.c.rsIso hfin).conjAut.toMonoidHom.comp Lv.ρ
  ρ_toSpec g := by
    change ((Lv.c.rsIso hfin).conjAut (Lv.ρ g)).hom ≫ _ = _
    rw [Iso.conjAut_hom, Iso.conj_apply, Category.assoc, Category.assoc,
      ModelCode.rsIso_hom_toSpec, ← Category.assoc (Lv.ρ g).hom, Lv.ρ_toSpec,
      ModelCode.rsIso_inv_toSpec]
  ρ_j g := by
    change _ = _ ≫ ((Lv.c.rsIso hfin).conjAut (Lv.ρ g)).hom
    rw [Iso.conjAut_hom, Iso.conj_apply, ← Category.assoc, Lv.ρ_j, Category.assoc,
      Category.assoc, Iso.hom_inv_id_assoc]

lemma rs_ρ_hom (g : Lv.L.H) :
    ((Lv.rs hO hfin).ρ g).hom = (Lv.c.rsIso hfin).inv ≫ (Lv.ρ g).hom ≫ (Lv.c.rsIso hfin).hom := by
  change ((Lv.c.rsIso hfin).conjAut (Lv.ρ g)).hom = _
  rw [Iso.conjAut_hom, Iso.conj_apply]

/-- The special fibres before and after restriction of scalars. -/
def rsZ : Lv.Z ≃ₜ (Lv.rs hO hfin).Z := Lv.c.rsSpecialHomeo hfin

lemma coe_rsZ_symm (z : (Lv.rs hO hfin).Z) :
    ((Lv.rsZ hO hfin).symm z : Lv.c.scheme) = (Lv.c.rsIso hfin).inv z.1 := rfl

lemma rsZ_symm_ρs (g : Lv.L.H) (z : (Lv.rs hO hfin).Z) :
    (Lv.rsZ hO hfin).symm ((Lv.rs hO hfin).ρs g z) = Lv.ρs g ((Lv.rsZ hO hfin).symm z) := by
  apply Subtype.ext
  rw [coe_rsZ_symm, Level.ρs_apply, Level.ρs_apply, coe_rsZ_symm, rs_ρ_hom]
  change ((Lv.c.rsIso hfin).inv ≫ (Lv.ρ g).hom ≫ (Lv.c.rsIso hfin).hom ≫
    (Lv.c.rsIso hfin).inv) z.1 = ((Lv.c.rsIso hfin).inv ≫ (Lv.ρ g).hom) z.1
  rw [Iso.hom_inv_id, Category.comp_id]

section Sp

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

omit [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R'] [SMulCommClass A' K' R']
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω] in
/-- Specialization commutes with restriction of scalars of model codes. -/
lemma sp_rsIso (c : ModelCode O') (x : Spec (CommRingCat.of Ω) ⟶ c.scheme)
    (hx : x ≫ c.toSpec = Spec.map (CommRingCat.ofHom (valToField O')))
    (hx' : (x ≫ (c.rsIso hfin).hom) ≫ (c.restrictScalars hfin).toSpec =
      Spec.map (CommRingCat.ofHom (valToField O))) :
    (TemperedFundamentalGroups.sp (c.restrictScalars hfin).toSpec V (TempObj.comap_eq hO V hV')
      (x ≫ (c.rsIso hfin).hom) hx' : (c.restrictScalars hfin).scheme) =
      (c.rsIso hfin).hom (TemperedFundamentalGroups.sp c.toSpec V hV' x hx : _) := by
  rw [sp_eq_of_lift (x ≫ (c.rsIso hfin).hom) hx'
    ((spLift (hV := hV') x hx).l ≫ (c.rsIso hfin).hom)
    (by rw [← Category.assoc, spLift_fac_left])
    (by
      rw [Category.assoc, ModelCode.rsIso_hom_toSpec, ← Category.assoc]
      erw [spLift_fac_right]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, TempObj.valToVal_valMap])]
  rfl

/-- **Specialization commutes with restriction of scalars.** -/
lemma rs_sp (t : Lv.L.B →ₐ[R'] Ω) :
    ((Lv.rs hO hfin).sp V (TempObj.comap_eq hO V hV') t).1 =
      (Lv.c.rsIso hfin).hom (Lv.sp V hV' t).1 := by
  have hx' : (Lv.point t ≫ (Lv.c.rsIso hfin).hom) ≫ (Lv.c.restrictScalars hfin).toSpec =
      Spec.map (CommRingCat.ofHom (valToField O)) := by
    simpa only [Level.point, Category.assoc] using (Lv.rs hO hfin).point_toSpec t
  have e := TempObj.sp_congr' hO V hV' (f := (Lv.c.restrictScalars hfin).toSpec)
    (x := (Lv.rs hO hfin).point t) (y := Lv.point t ≫ (Lv.c.rsIso hfin).hom)
    (by simp only [Level.point, Category.assoc]) ((Lv.rs hO hfin).point_toSpec t) hx'
  exact (congrArg Subtype.val e).trans
    (sp_rsIso hO hfin V hV' Lv.c (Lv.point t) (Lv.point_toSpec t) hx')

lemma rsZ_symm_sp (t : Lv.L.B →ₐ[R'] Ω) :
    (Lv.rsZ hO hfin).symm ((Lv.rs hO hfin).sp V (TempObj.comap_eq hO V hV') t) =
      Lv.sp V hV' t := by
  apply Subtype.ext
  rw [coe_rsZ_symm, rs_sp hO hfin Lv V hV']
  change ((Lv.c.rsIso hfin).hom ≫ (Lv.c.rsIso hfin).inv) _ = _
  rw [Iso.hom_inv_id]
  rfl

end Sp

end Level

namespace CoveringCode

variable {Z : Type u} [TopologicalSpace Z] {G : Type u} [Group G] {ρ : G →* (Z ≃ₜ Z)}
  (P : CoveringCode ρ) {Z' : Type u} {ψ : Z' → Z}

lemma pullbackPt_injective (hψ : Function.Injective ψ) :
    Function.Injective (pullbackPt P ψ) := fun x y h => by
  have h' := congrArg (fun p : P.carrier => p.1) h
  simp only [pullbackPt, Prod.mk.injEq] at h'
  exact pullback_ext P ψ (hψ h'.1) h'.2

end CoveringCode

namespace TempObj

/-- **Restriction of scalars of a tempered covering** over `(K', O')` to one over `(K, O)`: the
level `Level.rs`, and the covering space transported along the identification of special
fibres. -/
abbrev rsObj (X : TempObj O' R' A') : TempObj O R' A' where
  Lv := X.Lv.rs hO hfin
  P := X.P.pullback (MonoidHom.id _) (fun g z => X.Lv.rsZ_symm_ρs hO hfin g z)
    (X.Lv.rsZ hO hfin).symm.continuous

section RsMap

variable {X Y : TempObj O' R' A'} (m : X ⟶ Y)

/-- The model map after restriction of scalars. -/
def rsψ : (X.Lv.c.restrictScalars hfin).scheme ⟶ (Y.Lv.c.restrictScalars hfin).scheme :=
  (X.Lv.c.rsIso hfin).inv ≫ m.ψ ≫ (Y.Lv.c.rsIso hfin).hom

lemma rsψ_toSpec : rsψ hO hfin m ≫ (Y.Lv.c.restrictScalars hfin).toSpec =
    (X.Lv.c.restrictScalars hfin).toSpec := by
  rw [rsψ, Category.assoc, Category.assoc, ModelCode.rsIso_hom_toSpec, ← Category.assoc m.ψ,
    m.ψ_toSpec, ModelCode.rsIso_inv_toSpec]

lemma rsH_aux (q : (rsObj hO hfin X).P.carrier) :
    (m.h (CoveringCode.pullbackPt X.P _ q)).1.1 =
      (Y.Lv.rsZ hO hfin).symm (specialFibreMap (rsψ hO hfin m) (rsψ_toSpec hO hfin m) q.1.1) := by
  apply Subtype.ext
  rw [m.fst_h, Level.coe_rsZ_symm, coe_specialFibreMap]
  change m.ψ ((X.Lv.c.rsIso hfin).inv q.1.1.1) =
    ((X.Lv.c.rsIso hfin).inv ≫ m.ψ ≫ (Y.Lv.c.rsIso hfin).hom ≫ (Y.Lv.c.rsIso hfin).inv) q.1.1.1
  rw [Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The map of covering spaces after restriction of scalars. -/
def rsH : (rsObj hO hfin X).P.carrier → (rsObj hO hfin Y).P.carrier :=
  CoveringCode.pullbackLiftFun Y.P (ψ := (Y.Lv.rsZ hO hfin).symm)
    (fun q => specialFibreMap (rsψ hO hfin m) (rsψ_toSpec hO hfin m) q.1.1)
    (fun q => m.h (CoveringCode.pullbackPt X.P _ q)) (rsH_aux hO hfin m)

lemma pullbackPt_rsH (q : (rsObj hO hfin X).P.carrier) :
    CoveringCode.pullbackPt Y.P _ (rsH hO hfin m q) = m.h (CoveringCode.pullbackPt X.P _ q) :=
  CoveringCode.pullbackPt_liftFun _ _ _ _ _

lemma rsH_act (g : X.Lv.L.H) (q : (rsObj hO hfin X).P.carrier) :
    rsH hO hfin m ((rsObj hO hfin X).P.act g q) =
      (rsObj hO hfin Y).P.act (m.φ.r g) (rsH hO hfin m q) := by
  refine CoveringCode.pullbackPt_injective Y.P (Y.Lv.rsZ hO hfin).symm.injective ?_
  rw [pullbackPt_rsH, CoveringCode.pullbackPt_act, CoveringCode.pullbackPt_act, pullbackPt_rsH]
  exact m.h_act g _

/-- **Restriction of scalars of a morphism.** -/
def rsMap : rsObj hO hfin X ⟶ rsObj hO hfin Y where
  φ := m.φ
  ψ := rsψ hO hfin m
  ψ_toSpec := rsψ_toSpec hO hfin m
  j_ψ := by
    change (X.Lv.j ≫ (X.Lv.c.rsIso hfin).hom) ≫ (X.Lv.c.rsIso hfin).inv ≫ m.ψ ≫
      (Y.Lv.c.rsIso hfin).hom = _ ≫ Y.Lv.j ≫ (Y.Lv.c.rsIso hfin).hom
    rw [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% m.j_ψ]
  h := rsH hO hfin m
  continuous_h := CoveringCode.continuous_pullbackLiftFun Y.P (rsH_aux hO hfin m)
    ((continuous_specialFibreMap _ _).comp (rsObj hO hfin X).P.continuous_proj)
    (m.continuous_h.comp (CoveringCode.continuous_pullbackPt X.P))
  fst_h _ := rfl
  h_act := rsH_act hO hfin m

lemma rsMap_h : (rsMap hO hfin m).h = rsH hO hfin m := rfl

end RsMap

section W

variable (X : TempObj O' R' A')

/-- The model map `𝒯'' ⊆ 𝒯' ×_O O' ⟶ 𝒯'` of the comparison `fc (rsObj X') ⟶ X'`. -/
def rsWψ : ((rsObj hO hfin X).Lv.fcI hO (OrbMap.id R' A')).scheme ⟶ X.Lv.c.scheme :=
  ((rsObj hO hfin X).Lv.fcC hO).imgι ((rsObj hO hfin X).Lv.fcJ hO (OrbMap.id R' A')) ≫
    (X.Lv.c.restrictScalars hfin).bcFst (valMap hO) ≫ (X.Lv.c.rsIso hfin).inv

lemma toImg_rsWψ :
    ((rsObj hO hfin X).Lv.fcC hO).toImg ((rsObj hO hfin X).Lv.fcJ hO (OrbMap.id R' A')) ≫
      rsWψ hO hfin X = Spec.map (CommRingCat.ofHom
        ((FiniteLevel.bcIdφ X.Lv.L).f : X.Lv.L.B →+* _)) ≫ X.Lv.j := by
  rw [rsWψ, ModelCode.toImg_imgι_assoc, reassoc_of% Level.fcJ_fst]
  change _ ≫ (X.Lv.j ≫ (X.Lv.c.rsIso hfin).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

lemma rsWψ_toSpec : rsWψ hO hfin X ≫ X.Lv.c.toSpec =
    ((rsObj hO hfin X).Lv.fcI hO (OrbMap.id R' A')).toSpec := by
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    (Spec.map (CommRingCat.ofHom (valMap hO))) ?_
    (((rsObj hO hfin X).Lv.fcC hO).toImg ((rsObj hO hfin X).Lv.fcJ hO (OrbMap.id R' A'))) ?_
  · rw [rsWψ, Category.assoc, Category.assoc, Category.assoc, ModelCode.rsIso_inv_toSpec,
      ModelCode.bcFst_toSpec, ← Category.assoc, ModelCode.imgι_toSpec]
  · rw [reassoc_of% toImg_rsWψ, X.Lv.j_toSpec]
    have := ((rsObj hO hfin X).Lv.fieldChange hO (OrbMap.id R' A')).j_toSpec
    refine Eq.trans ?_ this.symm
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    exact FiniteLevel.bcι_levelStructureMap (OrbMap.id R' A') X.Lv.L o

/-- **The comparison morphism** `fc (rsObj X') ⟶ X'`. -/
def rsW : (rsObj hO hfin X).fieldChange hO (OrbMap.id R' A') ⟶ X where
  φ := FiniteLevel.bcIdφ X.Lv.L
  ψ := rsWψ hO hfin X
  ψ_toSpec := rsWψ_toSpec hO hfin X
  j_ψ := toImg_rsWψ hO hfin X
  h q := CoveringCode.pullbackPt X.P (X.Lv.rsZ hO hfin).symm
    (CoveringCode.pullbackPt (rsObj hO hfin X).P
      ((rsObj hO hfin X).Lv.fcS hO (OrbMap.id R' A')) q)
  continuous_h := @Continuous.comp _ _ _ _ (rsObj hO hfin X).P.top _ _ _
    (CoveringCode.continuous_pullbackPt X.P) (CoveringCode.continuous_pullbackPt _)
  fst_h _ := rfl
  h_act g q := by
    have e1 := CoveringCode.pullbackPt_act (rsObj hO hfin X).P
      (X.Lv.L.bcPr (OrbMap.id R' A')) ((rsObj hO hfin X).Lv.fcS_ρs hO (OrbMap.id R' A'))
      ((rsObj hO hfin X).Lv.continuous_fcS hO (OrbMap.id R' A')) g q
    have e2 := CoveringCode.pullbackPt_act X.P (MonoidHom.id _)
      (fun g z => X.Lv.rsZ_symm_ρs hO hfin g z) (X.Lv.rsZ hO hfin).symm.continuous
      (X.Lv.L.bcPr (OrbMap.id R' A') g) (CoveringCode.pullbackPt (rsObj hO hfin X).P
        ((rsObj hO hfin X).Lv.fcS hO (OrbMap.id R' A')) q)
    exact (congrArg (CoveringCode.pullbackPt X.P (X.Lv.rsZ hO hfin).symm) e1).trans e2

end W

section Pi

variable (Y : TempObj O R' A')

/-- The model map of `rsObj (fc Y) ⟶ Y`. -/
def rsπψ : ((Y.Lv.fcI hO (OrbMap.id R' A')).restrictScalars hfin).scheme ⟶ Y.Lv.c.scheme :=
  ((Y.Lv.fcI hO (OrbMap.id R' A')).rsIso hfin).inv ≫
    (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO (OrbMap.id R' A')) ≫ Y.Lv.c.bcFst (valMap hO)

lemma rsπψ_toSpec : rsπψ hO hfin Y ≫ Y.Lv.c.toSpec =
    ((Y.Lv.fcI hO (OrbMap.id R' A')).restrictScalars hfin).toSpec := by
  rw [rsπψ, Category.assoc, Category.assoc, ModelCode.bcFst_toSpec, ← Category.assoc
    ((Y.Lv.fcC hO).imgι _), ModelCode.imgι_toSpec, ModelCode.rsIso_inv_toSpec]

/-- **The comparison morphism** `rsObj (fc Y) ⟶ Y`. -/
def rsπ : rsObj hO hfin (Y.fieldChange hO (OrbMap.id R' A')) ⟶ Y where
  φ := FiniteLevel.bcIdφ Y.Lv.L
  ψ := rsπψ hO hfin Y
  ψ_toSpec := rsπψ_toSpec hO hfin Y
  j_ψ := by
    change (((Y.Lv.fcC hO).toImg _) ≫ ((Y.Lv.fcI hO (OrbMap.id R' A')).rsIso hfin).hom) ≫
      ((Y.Lv.fcI hO (OrbMap.id R' A')).rsIso hfin).inv ≫ _ ≫ _ = _
    rw [Category.assoc, Iso.hom_inv_id_assoc, ModelCode.toImg_imgι_assoc, Level.fcJ_fst]
    rfl
  h q := CoveringCode.pullbackPt Y.P (Y.Lv.fcS hO (OrbMap.id R' A'))
    (CoveringCode.pullbackPt (Y.fieldChange hO (OrbMap.id R' A')).P
      ((Y.fieldChange hO (OrbMap.id R' A')).Lv.rsZ hO hfin).symm q)
  continuous_h := @Continuous.comp _ _ _ _ (Y.fieldChange hO (OrbMap.id R' A')).P.top _ _ _
    (CoveringCode.continuous_pullbackPt Y.P) (CoveringCode.continuous_pullbackPt _)
  fst_h _ := rfl
  h_act g q := by
    have e1 := CoveringCode.pullbackPt_act (Y.fieldChange hO (OrbMap.id R' A')).P
      (MonoidHom.id _) (fun g z => (Y.fieldChange hO (OrbMap.id R' A')).Lv.rsZ_symm_ρs hO hfin g z)
      ((Y.fieldChange hO (OrbMap.id R' A')).Lv.rsZ hO hfin).symm.continuous g q
    have e2 := CoveringCode.pullbackPt_act Y.P (Y.Lv.L.bcPr (OrbMap.id R' A'))
      (Y.Lv.fcS_ρs hO (OrbMap.id R' A')) (Y.Lv.continuous_fcS hO (OrbMap.id R' A')) g
      (CoveringCode.pullbackPt (Y.fieldChange hO (OrbMap.id R' A')).P
        ((Y.fieldChange hO (OrbMap.id R' A')).Lv.rsZ hO hfin).symm q)
    exact (congrArg (CoveringCode.pullbackPt Y.P (Y.Lv.fcS hO (OrbMap.id R' A'))) e1).trans e2

end Pi


section Natural

variable {X Y : TempObj O' R' A'} (m : X ⟶ Y)

/-- **Naturality of the comparison morphisms.** -/
lemma rsW_natural : fcHom hO (OrbMap.id R' A') (rsMap hO hfin m) ≫ rsW hO hfin Y =
    rsW hO hfin X ≫ m := by
  refine Hom.ext ?_ ?_ (funext fun q => ?_)
  · refine FiniteLevel.Hom.ext (AlgHom.ext fun y => ?_) (MonoidHom.ext fun g => ?_)
    · exact FiniteLevel.bcMap_f_bcι (μ := OrbMap.id R' A') m.φ y
    · exact FiniteLevel.bcPr_bcMap (μ := OrbMap.id R' A') m.φ g
  · change fcψ hO (OrbMap.id R' A') (rsMap hO hfin m) ≫ rsWψ hO hfin Y = rsWψ hO hfin X ≫ m.ψ
    rw [rsWψ, rsWψ, fcψ_imgι_assoc, fcψ0_fst_assoc]
    change _ ≫ _ ≫ ((X.Lv.c.rsIso hfin).inv ≫ m.ψ ≫ (Y.Lv.c.rsIso hfin).hom) ≫ _ = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change CoveringCode.pullbackPt Y.P _ (CoveringCode.pullbackPt (rsObj hO hfin Y).P _
      (fcH hO (OrbMap.id R' A') (rsMap hO hfin m) q)) = m.h (CoveringCode.pullbackPt X.P _
        (CoveringCode.pullbackPt (rsObj hO hfin X).P _ q))
    exact (congrArg (CoveringCode.pullbackPt Y.P _)
      (pullbackPt_fcH hO (OrbMap.id R' A') (rsMap hO hfin m) q)).trans (pullbackPt_rsH hO hfin m _)

end Natural

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

section FibreEquiv

variable (X : TempObj O' R' A')

/-- Pairs `(t, p)` over `rsObj X` give pairs over `X`. -/
def rsPre (q : PreFibre Ω V (comap_eq hO V hV') (rsObj hO hfin X)) : PreFibre Ω V hV' X :=
  ⟨(q.1.1, CoveringCode.pullbackPt X.P (X.Lv.rsZ hO hfin).symm q.1.2), by
    change ((X.Lv.rsZ hO hfin).symm q.1.2.1.1 : X.Lv.c.scheme) = _
    rw [show q.1.2.1.1 = (X.Lv.rs hO hfin).sp V (comap_eq hO V hV') q.1.1 from Subtype.ext q.2,
      Level.rsZ_symm_sp]⟩

/-- Pairs `(t, p)` over `X` give pairs over `rsObj X`. -/
def rsPreInv (q : PreFibre Ω V hV' X) : PreFibre Ω V (comap_eq hO V hV') (rsObj hO hfin X) :=
  ⟨(q.1.1, ⟨((X.Lv.rs hO hfin).sp V (comap_eq hO V hV') q.1.1, q.1.2.1.2), by
    change ((X.Lv.rsZ hO hfin).symm ((X.Lv.rs hO hfin).sp V (comap_eq hO V hV') q.1.1),
      q.1.2.1.2) ∈ X.P.carrier
    rw [Level.rsZ_symm_sp hO hfin X.Lv V hV', ← Subtype.ext q.2]
    exact q.1.2.2⟩), rfl⟩

lemma rsPreInv_rsPre (q : PreFibre Ω V (comap_eq hO V hV') (rsObj hO hfin X)) :
    rsPreInv hO hfin V hV' X (rsPre hO hfin V hV' X q) = q :=
  Subtype.ext (Prod.ext rfl (CoveringCode.pullback_ext X.P _ (Subtype.ext q.2).symm rfl))

lemma rsPre_rsPreInv (q : PreFibre Ω V hV' X) :
    rsPre hO hfin V hV' X (rsPreInv hO hfin V hV' X q) = q := by
  refine Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext ?_ rfl)))
  change (X.Lv.rsZ hO hfin).symm ((X.Lv.rs hO hfin).sp V (comap_eq hO V hV') q.1.1) = q.1.2.1.1
  rw [Level.rsZ_symm_sp hO hfin X.Lv V hV']
  exact (Subtype.ext q.2).symm

lemma rsPre_smul (g : (rsObj hO hfin X).Lv.L.H0)
    (q : PreFibre Ω V (comap_eq hO V hV') (rsObj hO hfin X)) :
    rsPre hO hfin V hV' X (g • q) = (show X.Lv.L.H0 from g) • rsPre hO hfin V hV' X q :=
  Subtype.ext (Prod.ext rfl (CoveringCode.pullbackPt_act X.P (MonoidHom.id _)
    (fun g z => X.Lv.rsZ_symm_ρs hO hfin g z) (X.Lv.rsZ hO hfin).symm.continuous g.1 q.1.2))

lemma rsPreInv_smul (g : X.Lv.L.H0) (q : PreFibre Ω V hV' X) :
    rsPreInv hO hfin V hV' X (g • q) =
      (show (rsObj hO hfin X).Lv.L.H0 from g) • rsPreInv hO hfin V hV' X q := by
  have := rsPre_smul hO hfin V hV' X g (rsPreInv hO hfin V hV' X q)
  rw [rsPre_rsPreInv] at this
  rw [← this, rsPreInv_rsPre]

/-- **The fibres before and after restriction of scalars agree.** -/
def rsFibreEquiv : Fibre Ω V (comap_eq hO V hV') (rsObj hO hfin X) ≃ Fibre Ω V hV' X where
  toFun := Quotient.map (rsPre hO hfin V hV' X) fun q q' ⟨g, hg⟩ => by
    rw [← hg, rsPre_smul]
    exact ⟨g, rfl⟩
  invFun := Quotient.map (rsPreInv hO hfin V hV' X) fun q q' ⟨g, hg⟩ => by
    rw [← hg, rsPreInv_smul]
    exact ⟨g, rfl⟩
  left_inv x := by
    induction x using Quotient.inductionOn
    exact congrArg Quotient.mk'' (rsPreInv_rsPre hO hfin V hV' X _)
  right_inv x := by
    induction x using Quotient.inductionOn
    exact congrArg Quotient.mk'' (rsPre_rsPreInv hO hfin V hV' X _)

lemma fibreMap_rsW (x : Fibre Ω V hV' ((rsObj hO hfin X).fieldChange hO (OrbMap.id R' A'))) :
    fibreMap V hV' (rsW hO hfin X) x = rsFibreEquiv hO hfin V hV' X
      (fcFibreEquiv hO (OrbMap.id R' A') V hV' (rsObj hO hfin X) x) := by
  induction x using Quotient.inductionOn with
  | h q => exact congrArg Quotient.mk'' (Subtype.ext (Prod.ext (AlgHom.ext fun _ => rfl) rfl))

/-- **The comparison morphism is bijective on fibres.** -/
lemma bijective_fibreMap_rsW : Function.Bijective (fibreMap V hV' (rsW hO hfin X)) := by
  have : fibreMap V hV' (rsW hO hfin X) = ((fcFibreEquiv hO (OrbMap.id R' A') V hV'
      (rsObj hO hfin X)).trans (rsFibreEquiv hO hfin V hV' X)) :=
    funext (fibreMap_rsW hO hfin V hV' X)
  rw [this]
  exact Equiv.bijective _

end FibreEquiv

lemma fibreMap_rsπ (Y : TempObj O R' A')
    (z : (tempFibre O' R' A' V hV').obj ((fcFunctor O O' hO (OrbMap.id R' A')).obj
      (rsObj hO hfin ((fcFunctor O O' hO (OrbMap.id R' A')).obj Y)))) :
    (tempFibre O R' A' V (comap_eq hO V hV')).map (rsπ hO hfin Y)
      ((fcFibreIso O O' hO (OrbMap.id R' A') V hV').hom.app _ z) =
      (fcFibreIso O O' hO (OrbMap.id R' A') V hV').hom.app Y
        ((tempFibre O' R' A' V hV').map (rsW hO hfin _) z) := by
  induction z using Quotient.inductionOn with
  | h q => exact congrArg Quotient.mk'' (Subtype.ext (Prod.ext (AlgHom.ext fun _ => rfl) rfl))

variable (O O') in
/-- **Section data for the pure field change** (abstract criterion of
`FibreFunctor/SectionRestrict.lean`). -/
def rsSectionData : SectionData (fcFunctor O O' hO (OrbMap.id R' A'))
    (fcFibreIso O O' hO (OrbMap.id R' A') V hV') where
  S := rsObj hO hfin
  map m := rsMap hO hfin m
  w X := rsW hO hfin X
  w_natural m := rsW_natural hO hfin m
  w_bijective X := bijective_fibreMap_rsW hO hfin V hV' X
  π Y := rsπ hO hfin Y
  π_e Y z := fibreMap_rsπ hO hfin V hV' Y z

end Fibre

end TempObj

section Map

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

include hfin in
/-- **F8, pure case: the change of the valued field is bijective** (`O'` finite over `O`). -/
theorem bijective_temperedPi1FieldMap_pure :
    Function.Bijective (temperedPi1FieldMap hO (OrbMap.id R' A') V hV') :=
  (TempObj.rsSectionData O O' hO hfin V hV').bijective_restrict

include hfin in
theorem isOpenEmbedding_temperedPi1FieldMap_pure :
    Topology.IsOpenEmbedding (temperedPi1FieldMap hO (OrbMap.id R' A') V hV') :=
  (TempObj.rsSectionData O O' hO hfin V hV').isOpenEmbedding_restrict

/-- **F8, pure case: the change of the valued field is an isomorphism of topological groups**
`temperedPi1 O' R' A' ≃ₜ* temperedPi1 O R' A'` (`O'` finite over `O`). -/
def temperedPi1FieldEquiv :
    temperedPi1 O' R' A' V hV' ≃ₜ* temperedPi1 O R' A' V (TempObj.comap_eq hO V hV') :=
  (TempObj.rsSectionData O O' hO hfin V hV').restrictEquiv

lemma temperedPi1FieldEquiv_apply (γ : temperedPi1 O' R' A' V hV') :
    temperedPi1FieldEquiv hO hfin V hV' γ = temperedPi1FieldMap hO (OrbMap.id R' A') V hV' γ :=
  rfl

end Map

section Etale

variable {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [Algebra R R'] [IsScalarTower K R R'] (μ : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')
  [Subsingleton A] [Subsingleton A'] [SMulCommClass A K R]
  [Algebra.Etale R R'] [Module.Finite R R']

include hfin in
/-- **F8 (scheme case): the change of the valued field is injective** (`O'` finite over `O`,
`R'` finite étale over `R`). -/
theorem temperedPi1FieldMap_injective :
    Function.Injective (temperedPi1FieldMap hO μ V hV') :=
  temperedPi1FieldMap_injective_of_pure hO μ V hV'
    (bijective_temperedPi1FieldMap_pure hO hfin V hV').1

include hfin in
/-- **F8 (scheme case): the change of the valued field is an open embedding.** -/
theorem isOpenEmbedding_temperedPi1FieldMap :
    Topology.IsOpenEmbedding (temperedPi1FieldMap hO μ V hV') :=
  isOpenEmbedding_temperedPi1FieldMap_of_pure hO μ V hV'
    (isOpenEmbedding_temperedPi1FieldMap_pure hO hfin V hV')

include hfin in
/-- **F8 (scheme case): the image of the change of the valued field is the stabilizer** of the
base point of the finite étale cover `Spec R' → Spec R`. -/
theorem range_temperedPi1FieldMap :
    (temperedPi1FieldMap hO μ V hV').range =
      (temperedPi1Map μ V (TempObj.comap_eq hO V hV')).range :=
  range_temperedPi1FieldMap_of_pure hO μ V hV'
    (bijective_temperedPi1FieldMap_pure hO hfin V hV').2

include hfin in
theorem mem_range_temperedPi1FieldMap (γ : temperedPi1 O R A V (TempObj.comap_eq hO V hV')) :
    γ ∈ (temperedPi1FieldMap hO μ V hV').range ↔
      γ.app (coverObj O R A R') (coverFibrePt V (TempObj.comap_eq hO V hV')) =
        coverFibrePt V (TempObj.comap_eq hO V hV') :=
  mem_range_temperedPi1FieldMap_of_pure hO μ V hV'
    (bijective_temperedPi1FieldMap_pure hO hfin V hV').2 γ

include hfin in
/-- **F8 (scheme case): the image has finite index.** -/
theorem finiteIndex_range_temperedPi1FieldMap :
    (temperedPi1FieldMap hO μ V hV').range.FiniteIndex :=
  finiteIndex_range_temperedPi1FieldMap_of_pure hO μ V hV'
    (bijective_temperedPi1FieldMap_pure hO hfin V hV').2

end Etale

end

end TemperedFundamentalGroups
