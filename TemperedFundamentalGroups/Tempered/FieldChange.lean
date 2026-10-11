/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChange
import TemperedFundamentalGroups.Tempered.Comparison
import TemperedFundamentalGroups.Models.BaseChange
import TemperedFundamentalGroups.Models.Image
import TemperedFundamentalGroups.Andre.Pullback

/-!
# Change of the valued field (Blueprint §11, F8)

Let `(K, O) → (K', O')` be an extension of valued fields (`O'.comap (algebraMap K K') = O`) and
`μ : OrbMap R A R' A'` a map of orbifolds `[Spec R' / A'] → [Spec R / A]` with `R'` a
`K'`-algebra (e.g. `R' = K' ⊗_K R`). A tempered covering of `[Spec R / A]` over `(K, O)` pulls
back to a tempered covering of `[Spec R' / A']` over `(K', O')` (`TempObj.fieldChange`): the level
is base-changed as in F1, the model is the scheme-theoretic image `𝒯''` of `Spec (R' ⊗_R B)` in
the base change `𝒯 ×_O O'` (`ModelCode.baseChange`, `ModelCode.image`; taking the image makes
`j'` scheme-theoretically dominant, so that base-changed model maps are automatically
equivariant, `TempObj.imgEnd_fcψ`), and the covering space is pulled back along
`|𝒯''_s| → |𝒯_s|`. Its fibre at a
geometric point `Spec Ω → Spec R'` (with `V ∩ K' = O'`) is the fibre of the given covering
(`TempObj.fcFibreIso`). Restriction of fibre-functor automorphisms gives the continuous
homomorphism

`temperedPi1FieldMap : temperedPi1 O' R' A' V hV' →* temperedPi1 O R A V hV`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {K' : Type u} [Field K'] [Algebra K K'] {O' : ValuationSubring K'}
  (hO : O'.comap (algebraMap K K') = O)

/-- The inclusion `O → O'` of valuation rings. -/
def valMap : O →+* O' :=
  ((algebraMap K K').comp O.subtype).codRestrict O'.toSubring fun o => by
    have h : (o : K) ∈ O'.comap (algebraMap K K') := by rw [hO]; exact o.2
    exact h

lemma coe_valMap (o : O) : (valMap hO o : K') = algebraMap K K' o := rfl

instance : IsLocalHom (valMap hO) where
  map_nonunit a ha := by
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ha
    have hb' : (a : K) ≠ 0 := by
      intro h0
      have := congrArg Subtype.val hb
      simp [coe_valMap, h0] at this
    have hinv : ((a : K)⁻¹) ∈ O := by
      suffices h : algebraMap K K' (a : K)⁻¹ ∈ O' by
        have h' : (a : K)⁻¹ ∈ O'.comap (algebraMap K K') := h
        rwa [hO] at h'
      have : (b : K') = (algebraMap K K' a)⁻¹ := by
        have : (valMap hO a : K') * b = 1 := congrArg Subtype.val hb
        rw [coe_valMap] at this
        exact eq_inv_of_mul_eq_one_right this
      rw [map_inv₀, ← this]
      exact b.2
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb')⟩

variable {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra R R'] [Algebra K R']
  [IsScalarTower K R R'] [IsScalarTower K K' R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']
  (μ : OrbMap R A R' A')

namespace FiniteLevel

lemma bcι_comp_levelStructureMap (L : FiniteLevel R A) :
    (L.bcι μ).comp (levelStructureMap O R A L) =
      (levelStructureMap O' R' A' (L.baseChange μ)).comp (valMap hO) := by
  ext o
  change L.bcι μ (algebraMap R L.B (algebraMap K R o)) =
    algebraMap R' _ (algebraMap K' R' (algebraMap K K' o))
  rw [FiniteLevel.bcι_algebraMap]
  congr 1
  rw [← IsScalarTower.algebraMap_apply K R R', ← IsScalarTower.algebraMap_apply K K' R']

end FiniteLevel

namespace Level

variable (Lv : Level O R A)

/-- The base-changed model `𝒯 ×_O O'`. -/
abbrev fcC : ModelCode O' := Lv.c.baseChange (valMap hO)

lemma fc_j_w : (Spec.map (CommRingCat.ofHom (Lv.L.bcι μ)) ≫ Lv.j) ≫ Lv.c.toSpec =
    Spec.map (CommRingCat.ofHom (levelStructureMap O' R' A' (Lv.L.baseChange μ))) ≫
      Spec.map (CommRingCat.ofHom (valMap hO)) := by
  rw [Category.assoc, Lv.j_toSpec, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, FiniteLevel.bcι_comp_levelStructureMap hO μ Lv.L]

/-- The map `j' : Spec (R' ⊗_R B) ⟶ 𝒯 ×_O O'`. -/
def fcJ : Spec (CommRingCat.of (Lv.L.baseChange μ).B) ⟶ (Lv.fcC hO).scheme :=
  Lv.c.bcLift (valMap hO) _ _ (Lv.fc_j_w hO μ)

/-- The action of `g ∈ H` on `𝒯 ×_O O'`. -/
def fcEnd (g : Lv.L.H) : (Lv.fcC hO).scheme ⟶ (Lv.fcC hO).scheme :=
  Lv.c.bcLift (valMap hO) (Lv.c.bcFst (valMap hO) ≫ (Lv.ρ g).hom) (Lv.fcC hO).toSpec (by
    rw [Category.assoc, Lv.ρ_toSpec, ModelCode.bcFst_toSpec])

@[reassoc]
lemma fcEnd_fst (g : Lv.L.H) :
    Lv.fcEnd hO g ≫ Lv.c.bcFst (valMap hO) = Lv.c.bcFst (valMap hO) ≫ (Lv.ρ g).hom :=
  ModelCode.bcLift_fst _ _ _ _ _

@[reassoc]
lemma fcEnd_toSpec (g : Lv.L.H) : Lv.fcEnd hO g ≫ (Lv.fcC hO).toSpec = (Lv.fcC hO).toSpec :=
  ModelCode.bcLift_toSpec _ _ _ _ _

lemma fcEnd_comp (g g' : Lv.L.H) : Lv.fcEnd hO g ≫ Lv.fcEnd hO g' = Lv.fcEnd hO (g' * g) := by
  refine Lv.c.bc_hom_ext (valMap hO) ?_ ?_
  · rw [Category.assoc, fcEnd_fst, fcEnd_fst_assoc, fcEnd_fst, map_mul, Aut.Aut_mul_def,
      Iso.trans_hom]
  · rw [Category.assoc, fcEnd_toSpec, fcEnd_toSpec, fcEnd_toSpec]

lemma fcEnd_one : Lv.fcEnd hO 1 = 𝟙 _ := by
  refine Lv.c.bc_hom_ext (valMap hO) ?_ ?_
  · rw [fcEnd_fst, map_one, Category.id_comp]
    exact Category.comp_id _
  · rw [fcEnd_toSpec, Category.id_comp]

lemma fcJ_fst : Lv.fcJ hO μ ≫ Lv.c.bcFst (valMap hO) =
    Spec.map (CommRingCat.ofHom (Lv.L.bcι μ)) ≫ Lv.j :=
  ModelCode.bcLift_fst _ _ _ _ _

lemma fcJ_toSpec : Lv.fcJ hO μ ≫ (Lv.fcC hO).toSpec =
    Spec.map (CommRingCat.ofHom (levelStructureMap O' R' A' (Lv.L.baseChange μ))) :=
  ModelCode.bcLift_toSpec _ _ _ _ _

/-- `j'` is equivariant for the action of `g ∈ H'` through `bcPr g`. -/
lemma fcJ_fcEnd (g : (Lv.L.baseChange μ).H) :
    Lv.fcJ hO μ ≫ Lv.fcEnd hO (Lv.L.bcPr μ g) =
      Spec.map (CommRingCat.ofHom
        ((g : SemilinearAut R' A' (Lv.L.baseChange μ).B).σ.symm :
          (Lv.L.baseChange μ).B →+* (Lv.L.baseChange μ).B)) ≫ Lv.fcJ hO μ := by
  refine Lv.c.bc_hom_ext (valMap hO) ?_ ?_
  · simp only [Category.assoc]
    rw [fcEnd_fst, ← Category.assoc (Lv.fcJ hO μ), fcJ_fst]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine (congrArg (Spec.map (CommRingCat.ofHom (Lv.L.bcι μ)) ≫ ·)
      (Lv.ρ_j (Lv.L.bcPr μ g))).symm.trans ?_
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact (RingHom.ext fun y => FiniteLevel.bcσ_symm_bcι μ Lv.L g y).symm
  · simp only [Category.assoc, fcEnd_toSpec]
    rw [fcJ_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun o => ?_)
    exact (levelStructureMap_σ O' R' A' _
      (g : SemilinearAut R' A' (Lv.L.baseChange μ).B)⁻¹ o).symm

instance (priority := high) fcJ_qc : QuasiCompact (Lv.fcJ hO μ) :=
  quasiCompact_of_compactSpace _

/-- The model over `O'`: the scheme-theoretic image of `j'` in `𝒯 ×_O O'`. -/
abbrev fcI : ModelCode O' := (Lv.fcC hO).image (Lv.fcJ hO μ)

/-- The action of `g ∈ H'` on the image. -/
def imgEnd (g : (Lv.L.baseChange μ).H) : (Lv.fcI hO μ).scheme ⟶ (Lv.fcI hO μ).scheme :=
  (Lv.fcC hO).imageMap (Lv.fcJ hO μ) (Lv.fcJ hO μ) (Lv.fcEnd hO (Lv.L.bcPr μ g)) _
    (Lv.fcJ_fcEnd hO μ g)

@[reassoc]
lemma imgEnd_imgι (g : (Lv.L.baseChange μ).H) :
    Lv.imgEnd hO μ g ≫ (Lv.fcC hO).imgι (Lv.fcJ hO μ) =
      (Lv.fcC hO).imgι (Lv.fcJ hO μ) ≫ Lv.fcEnd hO (Lv.L.bcPr μ g) :=
  ModelCode.imageMap_imgι _ _ _ _ _ _

lemma imgEnd_comp (g g' : (Lv.L.baseChange μ).H) :
    Lv.imgEnd hO μ g ≫ Lv.imgEnd hO μ g' = Lv.imgEnd hO μ (g' * g) := by
  rw [← cancel_mono ((Lv.fcC hO).imgι (Lv.fcJ hO μ)), Category.assoc, imgEnd_imgι,
    imgEnd_imgι_assoc, imgEnd_imgι, fcEnd_comp, map_mul]

lemma imgEnd_one : Lv.imgEnd hO μ 1 = 𝟙 _ := by
  rw [← cancel_mono ((Lv.fcC hO).imgι (Lv.fcJ hO μ)), imgEnd_imgι, map_one, fcEnd_one,
    Category.comp_id, Category.id_comp]

/-- **The action of `H'` on the image.** -/
def imgAct : (Lv.L.baseChange μ).H →* Aut (Lv.fcI hO μ).scheme :=
  MonoidHom.mk' (fun g =>
    { hom := Lv.imgEnd hO μ g
      inv := Lv.imgEnd hO μ g⁻¹
      hom_inv_id := by rw [imgEnd_comp, inv_mul_cancel, imgEnd_one]
      inv_hom_id := by rw [imgEnd_comp, mul_inv_cancel, imgEnd_one] })
    fun g g' => by
      ext1
      simp only [Aut.Aut_mul_def, Iso.trans_hom]
      exact (Lv.imgEnd_comp hO μ g' g).symm

lemma imgAct_hom (g : (Lv.L.baseChange μ).H) : (Lv.imgAct hO μ g).hom = Lv.imgEnd hO μ g := rfl

lemma imgEnd_toSpec (g : (Lv.L.baseChange μ).H) :
    Lv.imgEnd hO μ g ≫ (Lv.fcI hO μ).toSpec = (Lv.fcI hO μ).toSpec := by
  rw [← ModelCode.imgι_toSpec, imgEnd_imgι_assoc, fcEnd_toSpec]

/-- **The level with model over `(K', O')`**: the base-changed level, the scheme-theoretic
image of `Spec (R' ⊗_R B)` in `𝒯 ×_O O'`. -/
def fieldChange : Level O' R' A' where
  L := Lv.L.baseChange μ
  c := Lv.fcI hO μ
  j := (Lv.fcC hO).toImg (Lv.fcJ hO μ)
  j_toSpec := by
    rw [← ModelCode.imgι_toSpec, ModelCode.toImg_imgι_assoc, fcJ_toSpec]
  ρ := Lv.imgAct hO μ
  ρ_toSpec g := Lv.imgEnd_toSpec hO μ g
  ρ_j g := (ModelCode.toImg_imageMap _ _ _ _ _ (Lv.fcJ_fcEnd hO μ g)).symm

instance : IsSchemeTheoreticallyDominant (Lv.fieldChange hO μ).j := by
  change IsSchemeTheoreticallyDominant ((Lv.fcC hO).toImg (Lv.fcJ hO μ))
  infer_instance


/-- The map of special fibres `|𝒯''_s| → |𝒯_s|` (through `𝒯'' ⊆ 𝒯 ×_O O' ⟶ 𝒯`). -/
def fcS (z : (Lv.fieldChange hO μ).Z) : Lv.Z :=
  Lv.c.bcFstS (valMap hO) (specialFibreMap ((Lv.fcC hO).imgι (Lv.fcJ hO μ))
    ((Lv.fcC hO).imgι_toSpec (Lv.fcJ hO μ)) z)

lemma fcS_coe (z : (Lv.fieldChange hO μ).Z) :
    (Lv.fcS hO μ z).1 = Lv.c.bcFst (valMap hO) ((Lv.fcC hO).imgι (Lv.fcJ hO μ) z.1) := rfl

lemma continuous_fcS : Continuous (Lv.fcS hO μ) :=
  (Lv.c.continuous_bcFstS (valMap hO)).comp (continuous_specialFibreMap _ _)

lemma fcS_ρs (g : (Lv.fieldChange hO μ).L.H) (z : (Lv.fieldChange hO μ).Z) :
    Lv.fcS hO μ ((Lv.fieldChange hO μ).ρs g z) = Lv.ρs (Lv.L.bcPr μ g) (Lv.fcS hO μ z) := by
  have key : Lv.imgEnd hO μ g ≫ (Lv.fcC hO).imgι (Lv.fcJ hO μ) ≫ Lv.c.bcFst (valMap hO) =
      (Lv.fcC hO).imgι (Lv.fcJ hO μ) ≫ Lv.c.bcFst (valMap hO) ≫ (Lv.ρ (Lv.L.bcPr μ g)).hom := by
    rw [imgEnd_imgι_assoc, fcEnd_fst]
  apply Subtype.ext
  calc (Lv.fcS hO μ ((Lv.fieldChange hO μ).ρs g z)).1
      = Lv.c.bcFst (valMap hO) ((Lv.fcC hO).imgι (Lv.fcJ hO μ)
          ((Lv.fieldChange hO μ).ρs g z).1) := Lv.fcS_coe hO μ _
    _ = Lv.c.bcFst (valMap hO) ((Lv.fcC hO).imgι (Lv.fcJ hO μ)
          (((Lv.fieldChange hO μ).ρ g).hom z.1)) := by rw [Level.ρs_apply]
    _ = (Lv.imgEnd hO μ g ≫ (Lv.fcC hO).imgι (Lv.fcJ hO μ) ≫ Lv.c.bcFst (valMap hO)) z.1 := by
        simp only [Scheme.Hom.comp_apply]
        rfl
    _ = ((Lv.fcC hO).imgι (Lv.fcJ hO μ) ≫ Lv.c.bcFst (valMap hO) ≫
          (Lv.ρ (Lv.L.bcPr μ g)).hom) z.1 := by rw [key]
    _ = (Lv.ρ (Lv.L.bcPr μ g)).hom (Lv.fcS hO μ z).1 := by
        simp only [Scheme.Hom.comp_apply]
        rfl
    _ = (Lv.ρs (Lv.L.bcPr μ g) (Lv.fcS hO μ z)).1 := (Level.ρs_apply _ _ _).symm

end Level

namespace TempObj

/-- **The tempered covering over `(K', O')`**: the level with model `Level.fieldChange`, and the
pullback of the covering space along `|𝒯''_s| → |𝒯_s|`. -/
def fieldChange (X : TempObj O R A) : TempObj O' R' A' where
  Lv := X.Lv.fieldChange hO μ
  P := X.P.pullback (X.Lv.L.bcPr μ) (X.Lv.fcS_ρs hO μ) (X.Lv.continuous_fcS hO μ)

section Hom

variable {X Y : TempObj O R A} (m : X ⟶ Y)

/-- The morphism `𝒯_X ×_O O' ⟶ 𝒯_Y ×_O O'`. -/
def fcψ0 : (X.Lv.fcC hO).scheme ⟶ (Y.Lv.fcC hO).scheme :=
  Y.Lv.c.bcLift (valMap hO) (X.Lv.c.bcFst (valMap hO) ≫ m.ψ) (X.Lv.fcC hO).toSpec (by
    rw [Category.assoc, m.ψ_toSpec, ModelCode.bcFst_toSpec])

@[reassoc]
lemma fcψ0_fst : fcψ0 hO m ≫ Y.Lv.c.bcFst (valMap hO) = X.Lv.c.bcFst (valMap hO) ≫ m.ψ :=
  ModelCode.bcLift_fst _ _ _ _ _

@[reassoc]
lemma fcψ0_toSpec : fcψ0 hO m ≫ (Y.Lv.fcC hO).toSpec = (X.Lv.fcC hO).toSpec :=
  ModelCode.bcLift_toSpec _ _ _ _ _

lemma fcJ_fcψ0 : X.Lv.fcJ hO μ ≫ fcψ0 hO m =
    Spec.map (CommRingCat.ofHom ((FiniteLevel.bcMap μ m.φ).f :
      (Y.Lv.L.baseChange μ).B →+* (X.Lv.L.baseChange μ).B)) ≫ Y.Lv.fcJ hO μ := by
  refine Y.Lv.c.bc_hom_ext (valMap hO) ?_ ?_
  · simp only [Category.assoc]
    rw [fcψ0_fst, ← Category.assoc, Level.fcJ_fst, Level.fcJ_fst, Category.assoc, m.j_ψ,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun y => (FiniteLevel.bcMap_f_bcι m.φ y).symm
  · simp only [Category.assoc]
    rw [fcψ0_toSpec, Level.fcJ_toSpec, Level.fcJ_toSpec]
    exact spec_levelStructureMap O' R' A' (FiniteLevel.bcMap μ m.φ)

/-- The model map `𝒯''_X ⟶ 𝒯''_Y`. -/
def fcψ : (X.Lv.fcI hO μ).scheme ⟶ (Y.Lv.fcI hO μ).scheme :=
  (X.Lv.fcC hO).imageMap (X.Lv.fcJ hO μ) (Y.Lv.fcJ hO μ) (fcψ0 hO m) _ (fcJ_fcψ0 hO μ m)

@[reassoc]
lemma fcψ_imgι : fcψ hO μ m ≫ (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO μ) =
    (X.Lv.fcC hO).imgι (X.Lv.fcJ hO μ) ≫ fcψ0 hO m :=
  ModelCode.imageMap_imgι _ _ _ _ _ _

lemma fcψ_toSpec : fcψ hO μ m ≫ (Y.Lv.fcI hO μ).toSpec = (X.Lv.fcI hO μ).toSpec := by
  rw [← ModelCode.imgι_toSpec, fcψ_imgι_assoc, fcψ0_toSpec, ModelCode.imgι_toSpec]

end Hom


section Hom2

variable {X Y : TempObj O R A} (m : X ⟶ Y)

/-- **Equivariance of the model map** (automatic, since `j'` is scheme-theoretically dominant in
the image and the models are separated). -/
lemma imgEnd_fcψ (g : (X.Lv.L.baseChange μ).H) :
    X.Lv.imgEnd hO μ g ≫ fcψ hO μ m =
      fcψ hO μ m ≫ Y.Lv.imgEnd hO μ ((FiniteLevel.bcMap μ m.φ).r g) := by
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated (Y.Lv.fcI hO μ).toSpec ?_
    ((X.Lv.fcC hO).toImg (X.Lv.fcJ hO μ)) ?_
  · rw [Category.assoc, Category.assoc, fcψ_toSpec, X.Lv.imgEnd_toSpec, Y.Lv.imgEnd_toSpec,
      fcψ_toSpec]
  · have a1 := (X.Lv.fcC hO).toImg_imageMap (X.Lv.fcJ hO μ) (X.Lv.fcJ hO μ)
      (X.Lv.fcEnd hO (X.Lv.L.bcPr μ g)) _ (X.Lv.fcJ_fcEnd hO μ g)
    have a2 := (X.Lv.fcC hO).toImg_imageMap (X.Lv.fcJ hO μ) (Y.Lv.fcJ hO μ) (fcψ0 hO m) _
      (fcJ_fcψ0 hO μ m)
    have a3 := (Y.Lv.fcC hO).toImg_imageMap (Y.Lv.fcJ hO μ) (Y.Lv.fcJ hO μ)
      (Y.Lv.fcEnd hO (Y.Lv.L.bcPr μ ((FiniteLevel.bcMap μ m.φ).r g))) _
      (Y.Lv.fcJ_fcEnd hO μ ((FiniteLevel.bcMap μ m.φ).r g))
    change _ ≫ (X.Lv.fcC hO).imageMap _ _ _ _ _ ≫ (X.Lv.fcC hO).imageMap _ _ _ _ _ =
      _ ≫ (X.Lv.fcC hO).imageMap _ _ _ _ _ ≫ (Y.Lv.fcC hO).imageMap _ _ _ _ _
    rw [reassoc_of% a1, a2, reassoc_of% a2, a3, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    refine RingHom.ext fun y => ?_
    apply (g : SemilinearAut R' A' (X.Lv.L.baseChange μ).B).σ.injective
    change (g : SemilinearAut R' A' _).σ ((g : SemilinearAut R' A' _).σ.symm
      ((FiniteLevel.bcMap μ m.φ).f y)) = (g : SemilinearAut R' A' _).σ
        ((FiniteLevel.bcMap μ m.φ).f (((FiniteLevel.bcMap μ m.φ).r g :
          SemilinearAut R' A' (Y.Lv.L.baseChange μ).B).σ.symm y))
    rw [RingEquiv.apply_symm_apply, ← (FiniteLevel.bcMap μ m.φ).f_σ, RingEquiv.apply_symm_apply]

/-- The map of special fibres of the models over `O'`. -/
def fcψS : (X.Lv.fieldChange hO μ).Z → (Y.Lv.fieldChange hO μ).Z :=
  specialFibreMap (fcψ hO μ m) (fcψ_toSpec hO μ m)

lemma fcψS_coe (z : (X.Lv.fieldChange hO μ).Z) : (fcψS hO μ m z).1 = fcψ hO μ m z.1 := rfl

lemma fcS_fcψS (z : (X.Lv.fieldChange hO μ).Z) :
    Y.Lv.fcS hO μ (fcψS hO μ m z) = specialFibreMap m.ψ m.ψ_toSpec (X.Lv.fcS hO μ z) := by
  have e : fcψ hO μ m ≫ (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO μ) ≫ Y.Lv.c.bcFst (valMap hO) =
      (X.Lv.fcC hO).imgι (X.Lv.fcJ hO μ) ≫ X.Lv.c.bcFst (valMap hO) ≫ m.ψ := by
    rw [fcψ_imgι_assoc, fcψ0_fst]
  apply Subtype.ext
  change (fcψ hO μ m ≫ (Y.Lv.fcC hO).imgι (Y.Lv.fcJ hO μ) ≫ Y.Lv.c.bcFst (valMap hO)) z.1 =
    ((X.Lv.fcC hO).imgι (X.Lv.fcJ hO μ) ≫ X.Lv.c.bcFst (valMap hO) ≫ m.ψ) z.1
  rw [e]

lemma fcH_aux (q : (X.fieldChange hO μ).P.carrier) :
    (m.h (CoveringCode.pullbackPt X.P (X.Lv.fcS hO μ) q)).1.1 =
      Y.Lv.fcS hO μ (fcψS hO μ m q.1.1) := by
  rw [fcS_fcψS]
  apply Subtype.ext
  rw [m.fst_h]
  rfl

/-- The map of covering spaces. -/
def fcH : (X.fieldChange hO μ).P.carrier → (Y.fieldChange hO μ).P.carrier :=
  CoveringCode.pullbackLiftFun Y.P (ψ := Y.Lv.fcS hO μ) (fun q => fcψS hO μ m q.1.1)
    (fun q => m.h (CoveringCode.pullbackPt X.P (X.Lv.fcS hO μ) q)) (fcH_aux hO μ m)

lemma pullbackPt_fcH (q : (X.fieldChange hO μ).P.carrier) :
    CoveringCode.pullbackPt Y.P (Y.Lv.fcS hO μ) (fcH hO μ m q) =
      m.h (CoveringCode.pullbackPt X.P (X.Lv.fcS hO μ) q) :=
  CoveringCode.pullbackPt_liftFun _ _ _ _ _

/-- **Change of the valued field of a morphism.** -/
def fcHom : X.fieldChange hO μ ⟶ Y.fieldChange hO μ where
  φ := FiniteLevel.bcMap μ m.φ
  ψ := fcψ hO μ m
  ψ_toSpec := fcψ_toSpec hO μ m
  j_ψ := (X.Lv.fcC hO).toImg_imageMap (X.Lv.fcJ hO μ) (Y.Lv.fcJ hO μ) _ _ (fcJ_fcψ0 hO μ m)
  h := fcH hO μ m
  continuous_h := CoveringCode.continuous_pullbackLiftFun Y.P (fcH_aux hO μ m)
    ((continuous_specialFibreMap _ _).comp (X.fieldChange hO μ).P.continuous_proj)
    (m.continuous_h.comp (CoveringCode.continuous_pullbackPt X.P))
  fst_h q := rfl
  h_act g q := by
    refine CoveringCode.pullback_ext Y.P (Y.Lv.fcS hO μ) (Subtype.ext ?_) ?_
    · change fcψ hO μ m (X.Lv.imgEnd hO μ g q.1.1.1) =
        Y.Lv.imgEnd hO μ ((FiniteLevel.bcMap μ m.φ).r g) (fcψ hO μ m q.1.1.1)
      rw [← Scheme.Hom.comp_apply, imgEnd_fcψ, Scheme.Hom.comp_apply]
    · change (m.h (CoveringCode.pullbackPt X.P (X.Lv.fcS hO μ)
          (CoveringCode.pullbackActFun X.P (X.Lv.L.bcPr μ) (X.Lv.fcS_ρs hO μ) g q))).1.2 =
        (Y.P.act (Y.Lv.L.bcPr μ ((FiniteLevel.bcMap μ m.φ).r g))
          (CoveringCode.pullbackPt Y.P (Y.Lv.fcS hO μ) (fcH hO μ m q))).1.2
      rw [CoveringCode.pullbackPt_actFun, m.h_act, FiniteLevel.bcPr_bcMap, fcH,
        CoveringCode.pullbackPt_liftFun]

end Hom2


section Functor

lemma fcψ0_id (X : TempObj O R A) : fcψ0 hO (𝟙 X) = 𝟙 _ :=
  X.Lv.c.bc_hom_ext (valMap hO) (by rw [fcψ0_fst, Category.id_comp]; exact Category.comp_id _)
    (by rw [fcψ0_toSpec, Category.id_comp])

lemma fcψ_id (X : TempObj O R A) : fcψ hO μ (𝟙 X) = 𝟙 _ := by
  rw [← cancel_mono ((X.Lv.fcC hO).imgι (X.Lv.fcJ hO μ)), fcψ_imgι, fcψ0_id, Category.comp_id,
    Category.id_comp]

lemma fcψ0_comp {X Y Z : TempObj O R A} (m : X ⟶ Y) (n : Y ⟶ Z) :
    fcψ0 hO (m ≫ n) = fcψ0 hO m ≫ fcψ0 hO n :=
  Z.Lv.c.bc_hom_ext (valMap hO)
    (by rw [fcψ0_fst, Category.assoc, fcψ0_fst, fcψ0_fst_assoc, TempObj.comp_ψ])
    (by rw [fcψ0_toSpec, Category.assoc, fcψ0_toSpec, fcψ0_toSpec])

lemma fcψ_comp {X Y Z : TempObj O R A} (m : X ⟶ Y) (n : Y ⟶ Z) :
    fcψ hO μ (m ≫ n) = fcψ hO μ m ≫ fcψ hO μ n := by
  rw [← cancel_mono ((Z.Lv.fcC hO).imgι (Z.Lv.fcJ hO μ)), fcψ_imgι, Category.assoc, fcψ_imgι,
    fcψ_imgι_assoc, fcψ0_comp]

variable (O O') in
/-- **Change of the valued field** as a functor `TempObj O R A ⥤ TempObj O' R' A'`. -/
def fcFunctor : TempObj O R A ⥤ TempObj O' R' A' where
  obj X := X.fieldChange hO μ
  map m := fcHom hO μ m
  map_id X := by
    refine Hom.ext ((FiniteLevel.bcFunctor μ).map_id X.Lv.L) (fcψ_id hO μ X) (funext fun q => ?_)
    refine CoveringCode.pullback_ext X.P (X.Lv.fcS hO μ) (Subtype.ext ?_) rfl
    change fcψ hO μ (𝟙 X) q.1.1.1 = q.1.1.1
    rw [fcψ_id]
    rfl
  map_comp m n := by
    refine Hom.ext ((FiniteLevel.bcFunctor μ).map_comp m.φ n.φ) (fcψ_comp hO μ m n)
      (funext fun q => ?_)
    refine CoveringCode.pullback_ext _ _ (Subtype.ext ?_) ?_
    · change fcψ hO μ (m ≫ n) q.1.1.1 = fcψ hO μ n (fcψ hO μ m q.1.1.1)
      rw [fcψ_comp, Scheme.Hom.comp_apply]
    · change (n.h (m.h (CoveringCode.pullbackPt _ _ q))).1.2 =
        (n.h (CoveringCode.pullbackPt _ _ (fcH hO μ m q))).1.2
      exact congrArg (fun p => (n.h p).1.2) (pullbackPt_fcH hO μ m q).symm

end Functor


section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower R R' Ω] (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

include hO hV' in
lemma comap_eq : V.comap (algebraMap K Ω) = O := by
  rw [IsScalarTower.algebraMap_eq K K' Ω, ← ValuationSubring.comap_comap, hV', hO]

lemma valToVal_valMap :
    (valToVal O' V hV').comp (valMap hO) = valToVal O V (comap_eq hO V hV') := by
  ext o
  change (algebraMap K' Ω (algebraMap K K' o)) = algebraMap K Ω o
  rw [← IsScalarTower.algebraMap_apply]

/-- **Specialization commutes with the change of the valued field.** -/
lemma sp_bcFst (c : ModelCode O) (x : Spec (CommRingCat.of Ω) ⟶ (c.baseChange (valMap hO)).scheme)
    (hx : x ≫ (c.baseChange (valMap hO)).toSpec = Spec.map (CommRingCat.ofHom (valToField O')))
    (hx' : (x ≫ c.bcFst (valMap hO)) ≫ c.toSpec =
      Spec.map (CommRingCat.ofHom (valToField O))) :
    (sp c.toSpec V (comap_eq hO V hV') (x ≫ c.bcFst (valMap hO)) hx' : c.scheme) =
      c.bcFst (valMap hO) (sp (c.baseChange (valMap hO)).toSpec V hV' x hx : _) := by
  rw [sp_eq_of_lift (x ≫ c.bcFst (valMap hO)) hx'
    ((spLift (hV := hV') x hx).l ≫ c.bcFst (valMap hO))
    (by rw [← Category.assoc, spLift_fac_left])
    (by
      rw [Category.assoc, ModelCode.bcFst_toSpec, ← Category.assoc]
      erw [spLift_fac_right]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, valToVal_valMap])]
  rfl


lemma sp_congr' {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of O)} [UniversallyClosed f]
    [IsSeparated f] {x y : Spec (CommRingCat.of Ω) ⟶ X} (h : x = y) (hx) (hy) :
    sp f V (comap_eq hO V hV') x hx = sp f V (comap_eq hO V hV') y hy := by
  subst h
  rfl

lemma point_fc (X : TempObj O R A) (t : (X.Lv.fieldChange hO μ).L.B →ₐ[R'] Ω) :
    ((X.Lv.fieldChange hO μ).point t ≫ (X.Lv.fcC hO).imgι (X.Lv.fcJ hO μ)) ≫
      X.Lv.c.bcFst (valMap hO) = X.Lv.point (X.Lv.L.bcRes μ t) := by
  rw [Level.point, Level.point, Category.assoc, Category.assoc]
  change Spec.map _ ≫ (X.Lv.fcC hO).toImg (X.Lv.fcJ hO μ) ≫ _ ≫ _ = _
  rw [ModelCode.toImg_imgι_assoc, Level.fcJ_fst, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- **The specializations agree.** -/
lemma fcS_sp (X : TempObj O R A) (t : (X.Lv.fieldChange hO μ).L.B →ₐ[R'] Ω) :
    X.Lv.fcS hO μ ((X.Lv.fieldChange hO μ).sp V hV' t) =
      X.Lv.sp V (comap_eq hO V hV') (X.Lv.L.bcRes μ t) := by
  apply Subtype.ext
  rw [Level.fcS_coe]
  have h1 := coe_sp_comp (hV := hV') ((X.Lv.fcC hO).imgι (X.Lv.fcJ hO μ))
    ((X.Lv.fcC hO).imgι_toSpec (X.Lv.fcJ hO μ)) ((X.Lv.fieldChange hO μ).point t)
    ((X.Lv.fieldChange hO μ).point_toSpec t)
  have h2 := sp_bcFst hO V hV' X.Lv.c _ ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((X.Lv.fcC hO).imgι_toSpec (X.Lv.fcJ hO μ))).trans
        ((X.Lv.fieldChange hO μ).point_toSpec t)))
    ((congrArg (· ≫ X.Lv.c.toSpec) (point_fc hO μ X t)).trans (X.Lv.point_toSpec _))
  refine (congrArg (X.Lv.c.bcFst (valMap hO)) h1.symm).trans (h2.symm.trans ?_)
  exact congrArg Subtype.val (sp_congr' hO V hV' (point_fc hO μ X t) _ _)


section FibreEquiv

variable (X : TempObj O R A)

lemma sp_eq (q : PreFibre Ω V hV' (X.fieldChange hO μ)) :
    q.1.2.1.1 = (X.Lv.fieldChange hO μ).sp V hV' q.1.1 := Subtype.ext q.2

/-- Restriction of pairs `(t', p')`. -/
def fcPreRes (q : PreFibre Ω V hV' (X.fieldChange hO μ)) :
    PreFibre Ω V (comap_eq hO V hV') X :=
  ⟨(X.Lv.L.bcRes μ q.1.1, CoveringCode.pullbackPt X.P (X.Lv.fcS hO μ) q.1.2), by
    change (X.Lv.fcS hO μ q.1.2.1.1).1 = _
    rw [sp_eq hO μ V hV' X q, fcS_sp]⟩

/-- Extension of pairs `(t, p)`. -/
def fcPreExt (q : PreFibre Ω V (comap_eq hO V hV') X) :
    PreFibre Ω V hV' (X.fieldChange hO μ) :=
  ⟨(X.Lv.L.bcExt μ q.1.1, ⟨((X.Lv.fieldChange hO μ).sp V hV' (X.Lv.L.bcExt μ q.1.1), q.1.2.1.2),
    by
      change (X.Lv.fcS hO μ ((X.Lv.fieldChange hO μ).sp V hV' (X.Lv.L.bcExt μ q.1.1)),
        q.1.2.1.2) ∈ X.P.carrier
      rw [fcS_sp, FiniteLevel.bcRes_bcExt, ← Subtype.ext q.2]
      exact q.1.2.2⟩), rfl⟩

lemma fcPreRes_ext (q : PreFibre Ω V (comap_eq hO V hV') X) :
    fcPreRes hO μ V hV' X (fcPreExt hO μ V hV' X q) = q := by
  refine Subtype.ext (Prod.ext (FiniteLevel.bcRes_bcExt μ _ _) ?_)
  refine Subtype.ext (Prod.ext ?_ rfl)
  change X.Lv.fcS hO μ ((X.Lv.fieldChange hO μ).sp V hV' (X.Lv.L.bcExt μ q.1.1)) = q.1.2.1.1
  rw [fcS_sp, FiniteLevel.bcRes_bcExt, ← Subtype.ext q.2]

lemma fcPreExt_res (q : PreFibre Ω V hV' (X.fieldChange hO μ)) :
    fcPreExt hO μ V hV' X (fcPreRes hO μ V hV' X q) = q := by
  refine Subtype.ext (Prod.ext (FiniteLevel.bcExt_bcRes μ _ _) ?_)
  refine CoveringCode.pullback_ext X.P (X.Lv.fcS hO μ) ?_ rfl
  change (X.Lv.fieldChange hO μ).sp V hV' (X.Lv.L.bcExt μ (X.Lv.L.bcRes μ q.1.1)) = q.1.2.1.1
  rw [FiniteLevel.bcExt_bcRes, sp_eq hO μ V hV' X q]

lemma fcPreRes_smul (g : (X.fieldChange hO μ).Lv.L.H0) (q : PreFibre Ω V hV' (X.fieldChange hO μ)) :
    fcPreRes hO μ V hV' X (g • q) =
      (⟨X.Lv.L.bcPr μ g.1, FiniteLevel.bcPr_mem_H0 μ X.Lv.L g.2⟩ : X.Lv.L.H0) •
        fcPreRes hO μ V hV' X q := by
  apply Subtype.ext
  refine Prod.ext (FiniteLevel.bcRes_fibreAct μ X.Lv.L g q.1.1) ?_
  exact CoveringCode.pullbackPt_actFun X.P (X.Lv.L.bcPr μ) (X.Lv.fcS_ρs hO μ) g.1 q.1.2

lemma fcPreExt_smul (h : X.Lv.L.H0) (q : PreFibre Ω V (comap_eq hO V hV') X) :
    fcPreExt hO μ V hV' X (h • q) =
      (show (X.fieldChange hO μ).Lv.L.H0 from X.Lv.L.bcH0 μ h) • fcPreExt hO μ V hV' X q := by
  have := fcPreRes_smul hO μ V hV' X (X.Lv.L.bcH0 μ h) (fcPreExt hO μ V hV' X q)
  rw [fcPreRes_ext] at this
  have hh : (⟨X.Lv.L.bcPr μ (X.Lv.L.bcH0 μ h : (X.Lv.L.baseChange μ).H),
      FiniteLevel.bcPr_mem_H0 μ X.Lv.L (X.Lv.L.bcH0 μ h).2⟩ : X.Lv.L.H0) = h :=
    Subtype.ext (FiniteLevel.bcPr_bcH0 μ X.Lv.L h)
  rw [hh] at this
  rw [← this, fcPreExt_res]

/-- **The fibre after changing the valued field** is the fibre of the given covering. -/
def fcFibreEquiv : Fibre Ω V hV' (X.fieldChange hO μ) ≃ Fibre Ω V (comap_eq hO V hV') X where
  toFun := Quotient.map (fcPreRes hO μ V hV' X) fun q q' ⟨g, hg⟩ => by
    rw [← hg, fcPreRes_smul]
    exact ⟨_, rfl⟩
  invFun := Quotient.map (fcPreExt hO μ V hV' X) fun q q' ⟨g, hg⟩ => by
    rw [← hg, fcPreExt_smul]
    exact ⟨_, rfl⟩
  left_inv x := by
    induction x using Quotient.inductionOn
    exact congrArg Quotient.mk'' (fcPreExt_res hO μ V hV' X _)
  right_inv x := by
    induction x using Quotient.inductionOn
    exact congrArg Quotient.mk'' (fcPreRes_ext hO μ V hV' X _)

end FibreEquiv


lemma fcPreRes_natural {X Y : TempObj O R A} (m : X ⟶ Y)
    (q : PreFibre Ω V hV' (X.fieldChange hO μ)) :
    fcPreRes hO μ V hV' Y (preMap V hV' (fcHom hO μ m) q) =
      preMap V (comap_eq hO V hV') m (fcPreRes hO μ V hV' X q) :=
  Subtype.ext (Prod.ext (FiniteLevel.bcRes_bcMap μ m.φ _) (pullbackPt_fcH hO μ m q.1.2))

variable (O O') in
/-- **Changing the valued field commutes with the fibre functors.** -/
def fcFibreIso : fcFunctor O O' hO μ ⋙ tempFibre O' R' A' V hV' ≅
    tempFibre O R A V (comap_eq hO V hV') :=
  NatIso.ofComponents (fun X => (fcFibreEquiv hO μ V hV' X).toIso) fun {X Y} m => by
    ext x
    induction x using Quotient.inductionOn with
    | h q => exact congrArg Quotient.mk'' (fcPreRes_natural hO μ V hV' m q)

end Fibre

end TempObj

section Map

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower R R' Ω] (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- **F8: change of the valued field.** For an extension of valued fields `(K, O) → (K', O')`
and a map of orbifolds `μ : OrbMap R A R' A'` (`R'` a `K'`-algebra), restriction along the base
change of tempered coverings `TempObj.fcFunctor` is a continuous homomorphism
`temperedPi1 O' R' A' →* temperedPi1 O R A`. -/
def temperedPi1FieldMap :
    temperedPi1 O' R' A' V hV' →* temperedPi1 O R A V (TempObj.comap_eq hO V hV') :=
  FibreAut.restrict (TempObj.fcFunctor O O' hO μ) (TempObj.fcFibreIso O O' hO μ V hV')

lemma continuous_temperedPi1FieldMap : Continuous (temperedPi1FieldMap hO μ V hV') :=
  FibreAut.continuous_restrict _ _

end Map

end

end TemperedFundamentalGroups
