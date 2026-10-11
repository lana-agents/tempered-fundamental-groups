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
is base-changed as in F1, the model is base-changed to `O'` (`ModelCode.baseChange`, the fibre
product `𝒯 ×_O O'`), and the covering space is pulled back along `|𝒯'_s| → |𝒯_s|`. Its fibre at a
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

instance fcJ_qc : QuasiCompact (Lv.fcJ hO μ) := quasiCompact_of_compactSpace _

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

end TempObj

end

end TemperedFundamentalGroups
