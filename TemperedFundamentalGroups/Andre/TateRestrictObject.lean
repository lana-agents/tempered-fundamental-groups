/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictLevel
import TemperedFundamentalGroups.Andre.TateCoveringEq
import TemperedFundamentalGroups.Andre.TateNodePoints
import TemperedFundamentalGroups.SemistableReduction.SemistableFibreDim
import TemperedFundamentalGroups.FibreFunctor.Character

/-!
# The special fibre of the restricted Tate model (Blueprint §10.3.8, `v(q) = 1`, B3f)

The special fibre over `O` of the restricted model `modelR` (the Tate model over `O'` with
`π = √ϖ`, presented over `O`) is homeomorphic to the special fibre over `O'` of the Tate model
`TateModel.model √ϖ b₄ b₆` (`ΦR`): `O → O'` is an injective local map of DVRs.

The decomposition `C ∪ E'` (line and conic meeting in `p`, `q`) pulls back along `ΦR`
(`decompR`), and the action of `H = ⟨σ⟩` preserves it (`preserves_ρs`): `σ` acts on the
coordinates by `u ↦ -u`, `v ↦ -v`, `w ↦ w`, so it preserves the loci `w = 0`, `v = 0`,
`u + v = 0` (`mem_imageι_ρ'_X_iff`, `mem_imageι_ρ'_X01_iff`). This is proved, not assumed.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing SemistableReduction.ProjScheme Pi1.Orbifold

namespace TemperedFundamentalGroups

/-- **Special fibres along an injective local map of DVRs**: for `f : X ⟶ Spec O'`, an
isomorphism `e : Y ≅ X` and `fY = e.hom ≫ f ≫ Spec φ`, the special fibres of `fY` and `f` are
homeomorphic via `e`. -/
def specialFibreHomeomorphDvr {O O' : Type u} [CommRing O] [CommRing O']
    [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
    (φ : O →+* O') (hφ : Function.Injective φ) [IsLocalHom φ] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of O')) (fY : Y ⟶ Spec (CommRingCat.of O)) (e : Y ≅ X)
    (he : e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom φ) = fY) :
    specialFibre fY ≃ₜ specialFibre f where
  toFun y := ⟨e.hom y.1, mem_specialFibre_of_comp_dvr φ hφ f e (by rw [he]; exact y.2)⟩
  invFun z := ⟨e.inv z.1, by
    have hz := z.2
    rw [mem_specialFibre] at hz ⊢
    rw [← he]
    have h1 : e.hom (e.inv z.1) = z.1 := by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
    change Spec.map (CommRingCat.ofHom φ) (f (e.hom (e.inv z.1))) = _
    rw [h1, hz]
    exact IsLocalRing.comap_closedPoint φ⟩
  left_inv y := Subtype.ext (by
    change e.inv (e.hom y.1) = y.1
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl)
  right_inv z := Subtype.ext (by
    change e.hom (e.inv z.1) = z.1
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact e.hom.continuous.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact e.inv.continuous.comp continuous_subtype_val

@[simp] lemma coe_specialFibreHomeomorphDvr {O O' : Type u} [CommRing O] [CommRing O']
    [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
    (φ : O →+* O') (hφ : Function.Injective φ) [IsLocalHom φ] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of O')) (fY : Y ⟶ Spec (CommRingCat.of O)) (e : Y ≅ X)
    (he : e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom φ) = fY) (y : specialFibre fY) :
    (specialFibreHomeomorphDvr φ hφ f fY e he y : X) = e.hom y.1 :=
  rfl

namespace TateRestrict

open RamifiedQuadratic SemistableReduction.W10Apply Pi1.Orbifold

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

lemma algebraMap_O'_injective : Function.Injective (algebraMap O (O' ϖ)) :=
  fun _ _ hab ↦ Subtype.ext ((algebraMap K (K' ϖ)).injective (congrArg Subtype.val hab))

instance isLocalHom_O' : IsLocalHom (algebraMap O (O' ϖ)) := by
  haveI : Algebra.IsIntegral O (O' ϖ) := IsIntegralClosure.isIntegral_algebra O (K' ϖ)
  haveI : FaithfulSMul O (O' ϖ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 algebraMap_O'_injective
  exact Algebra.IsIntegral.isLocalHom O (O' ϖ)

variable [CharZero K] (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄)
  (algebraMap O (O' ϖ) b₆)))]

/-- The Tate model over `O'` with `π = √ϖ`. -/
abbrev modelT : ModelCode (O' ϖ) :=
  TateModel.model (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)

/-- The isomorphism of `modelR` with the Tate model over `O'`. -/
def isoT : (modelR hϖ b₄ b₆).scheme ≅ (modelT b₄ b₆ (ϖ := ϖ)).scheme :=
  isoR hϖ b₄ b₆ ≪≫ (TateNormal.modelIso (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)).symm

lemma isoT_toSpec : (isoT hϖ b₄ b₆).hom ≫ (modelT b₄ b₆ (ϖ := ϖ)).toSpec ≫
    Spec.map (CommRingCat.ofHom (algebraMap O (O' ϖ))) = (modelR hϖ b₄ b₆).toSpec := by
  rw [isoT, Iso.trans_hom, Iso.symm_hom,
    ← TateNormal.modelIso_hom_toSpec (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)
      (sO_ne_zero hϖ)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact modelIsoO_toSpec O _ _ _ _ _ _ _ _

/-- **The special fibre of the restricted model is that of the Tate model over `O'`.** -/
def ΦR : specialFibre (modelR hϖ b₄ b₆).toSpec ≃ₜ specialFibre (modelT b₄ b₆ (ϖ := ϖ)).toSpec :=
  specialFibreHomeomorphDvr _ algebraMap_O'_injective _ _ (isoT hϖ b₄ b₆) (isoT_toSpec hϖ b₄ b₆)

lemma isoT_hom : (isoT hϖ b₄ b₆).hom = (isoR hϖ b₄ b₆).hom ≫
    (TateNormal.modelIso (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)
      (sO_ne_zero hϖ)).inv :=
  rfl

lemma isoT_hom_ι : (isoT hϖ b₄ b₆).hom ≫
    TateModel.ι (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) = (isoR hϖ b₄ b₆).hom ≫
    (toProj (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
        (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι := by
  rw [isoT_hom, Category.assoc, ← TateNormal.modelIso_hom_imageι (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)]
  exact congrArg _ (Iso.inv_hom_id_assoc (TateNormal.modelIso (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)) _)


lemma coe_ΦR (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    (ΦR hϖ b₄ b₆ z : (modelT b₄ b₆ (ϖ := ϖ)).scheme) = (isoT hϖ b₄ b₆).hom z.1 := by
  unfold ΦR
  rw [coe_specialFibreHomeomorphDvr]

lemma ι_ΦR (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    TateModel.ι _ _ _ (ΦR hϖ b₄ b₆ z : (modelT b₄ b₆ (ϖ := ϖ)).scheme) =
      (toProj (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
        (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι ((isoR hϖ b₄ b₆).hom z.1) := by
  rw [coe_ΦR]
  have h := congrArg (fun φ ↦ φ z.1) (isoT_hom_ι hϖ b₄ b₆)
  simp only [Scheme.Hom.comp_apply] at h
  exact h

lemma ρσ_isoT_ι : (ρσ hϖ b₄ b₆).hom ≫ (isoT hϖ b₄ b₆).hom ≫
    TateModel.ι (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) =
      (isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ ≫
        (toProj (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
          (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι := by
  rw [isoT_hom_ι]
  change ((isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ ≫ (isoR hϖ b₄ b₆).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

lemma coe_ρσs (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    ((specialFibreHomeomorph (ρσ hϖ b₄ b₆) (ρσ_toSpec hϖ b₄ b₆) z :
      specialFibre (modelR hϖ b₄ b₆).toSpec) : (modelR hϖ b₄ b₆).scheme) =
      (ρσ hϖ b₄ b₆).hom z.1 :=
  coe_specialFibreHomeomorph _ _ _

lemma ρσ_isoR : (ρσ hϖ b₄ b₆).hom ≫ (isoR hϖ b₄ b₆).hom =
    (isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ := by
  change ((isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ ≫ (isoR hϖ b₄ b₆).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma ι_ΦR_of_eq {z z' : specialFibre (modelR hϖ b₄ b₆).toSpec}
    (hz : z'.1 = (ρσ hϖ b₄ b₆).hom z.1) :
    TateModel.ι _ _ _ (ΦR hϖ b₄ b₆ z' : (modelT b₄ b₆ (ϖ := ϖ)).scheme) =
      (toProj (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
        (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        (ρR' hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom z.1)) := by
  rw [ι_ΦR]
  refine (congrArg (fun w ↦ (toProj (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι ((isoR hϖ b₄ b₆).hom w)) hz).trans ?_
  have h2 := congrArg (fun φ ↦ φ z.1) (ρσ_isoR hϖ b₄ b₆)
  simp only [Scheme.Hom.comp_apply] at h2
  exact congrArg _ h2

include hϖ in
lemma sO_mem : sO ϖ ∈ maximalIdeal (O' ϖ) :=
  (mem_maximalIdeal _).2 (irreducible_sqrt hϖ).not_isUnit

/-- **The decomposition of the special fibre of the restricted model.** -/
def decompR : TateCovering.Decomp (specialFibre (modelR hϖ b₄ b₆).toSpec) :=
  (TateModel.decomp (b₄ := algebraMap O (O' ϖ) b₄) (b₆ := algebraMap O (O' ϖ) b₆)
    (sO_mem hϖ)).comap (ΦR hϖ b₄ b₆)

lemma mem_C_iff (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    z ∈ (decompR hϖ b₄ b₆).C ↔ MvPolynomial.X 2 ∈
      (TateModel.ι _ _ _ (ΦR hϖ b₄ b₆ z : (modelT b₄ b₆ (ϖ := ϖ)).scheme)).asHomogeneousIdeal := by
  unfold decompR TateCovering.Decomp.comap
  rw [Set.mem_preimage]
  unfold TateModel.decomp
  dsimp only
  unfold TateModel.Cset TateModel.ιZ
  rw [Set.mem_setOf_eq]

lemma mem_Cp_iff (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    z ∈ (decompR hϖ b₄ b₆).Cp ↔ MvPolynomial.X 2 ∈
      (TateModel.ι _ _ _ (ΦR hϖ b₄ b₆ z : (modelT b₄ b₆ (ϖ := ϖ)).scheme)).asHomogeneousIdeal ∧
      MvPolynomial.X 1 ∈
      (TateModel.ι _ _ _ (ΦR hϖ b₄ b₆ z : (modelT b₄ b₆ (ϖ := ϖ)).scheme)).asHomogeneousIdeal := by
  unfold decompR TateCovering.Decomp.comap
  rw [Set.mem_preimage]
  unfold TateModel.decomp
  dsimp only
  unfold TateModel.Cp TateModel.ιZ
  rw [Set.mem_setOf_eq]

lemma mem_Cq_iff (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    z ∈ (decompR hϖ b₄ b₆).Cq ↔ MvPolynomial.X 2 ∈
      (TateModel.ι _ _ _ (ΦR hϖ b₄ b₆ z : (modelT b₄ b₆ (ϖ := ϖ)).scheme)).asHomogeneousIdeal ∧
      MvPolynomial.X 0 + MvPolynomial.X 1 ∈
      (TateModel.ι _ _ _ (ΦR hϖ b₄ b₆ z : (modelT b₄ b₆ (ϖ := ϖ)).scheme)).asHomogeneousIdeal := by
  unfold decompR TateCovering.Decomp.comap
  rw [Set.mem_preimage]
  unfold TateModel.decomp
  dsimp only
  unfold TateModel.Cq TateModel.ιZ
  rw [Set.mem_setOf_eq]

lemma mem_C_iff' (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    z ∈ (decompR hϖ b₄ b₆).C ↔
      MvPolynomial.X 2 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        ((isoR hϖ b₄ b₆).hom z.1)).asHomogeneousIdeal := by
  refine (mem_C_iff hϖ b₄ b₆ z).trans ?_
  rw [ι_ΦR hϖ b₄ b₆ z]

lemma mem_C_iff_ρσ (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    specialFibreHomeomorph (ρσ hϖ b₄ b₆) (ρσ_toSpec hϖ b₄ b₆) z ∈ (decompR hϖ b₄ b₆).C ↔
      MvPolynomial.X 2 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        (ρR' hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom z.1))).asHomogeneousIdeal := by
  refine (mem_C_iff hϖ b₄ b₆ _).trans ?_
  rw [ι_ΦR_of_eq hϖ b₄ b₆ (coe_ρσs hϖ b₄ b₆ z)]

lemma mem_Cp_iff' (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    z ∈ (decompR hϖ b₄ b₆).Cp ↔
      MvPolynomial.X 2 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        ((isoR hϖ b₄ b₆).hom z.1)).asHomogeneousIdeal ∧
      MvPolynomial.X 1 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        ((isoR hϖ b₄ b₆).hom z.1)).asHomogeneousIdeal := by
  refine (mem_Cp_iff hϖ b₄ b₆ z).trans ?_
  rw [ι_ΦR hϖ b₄ b₆ z]

lemma mem_Cp_iff_ρσ (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    specialFibreHomeomorph (ρσ hϖ b₄ b₆) (ρσ_toSpec hϖ b₄ b₆) z ∈ (decompR hϖ b₄ b₆).Cp ↔
      MvPolynomial.X 2 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        (ρR' hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom z.1))).asHomogeneousIdeal ∧
      MvPolynomial.X 1 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        (ρR' hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom z.1))).asHomogeneousIdeal := by
  refine (mem_Cp_iff hϖ b₄ b₆ _).trans ?_
  simp only [ι_ΦR_of_eq hϖ b₄ b₆ (coe_ρσs hϖ b₄ b₆ z)]

lemma mem_Cq_iff' (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    z ∈ (decompR hϖ b₄ b₆).Cq ↔
      MvPolynomial.X 2 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        ((isoR hϖ b₄ b₆).hom z.1)).asHomogeneousIdeal ∧
      MvPolynomial.X 0 + MvPolynomial.X 1 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        ((isoR hϖ b₄ b₆).hom z.1)).asHomogeneousIdeal := by
  refine (mem_Cq_iff hϖ b₄ b₆ z).trans ?_
  rw [ι_ΦR hϖ b₄ b₆ z]

lemma mem_Cq_iff_ρσ (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    specialFibreHomeomorph (ρσ hϖ b₄ b₆) (ρσ_toSpec hϖ b₄ b₆) z ∈ (decompR hϖ b₄ b₆).Cq ↔
      MvPolynomial.X 2 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        (ρR' hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom z.1))).asHomogeneousIdeal ∧
      MvPolynomial.X 0 + MvPolynomial.X 1 ∈ ((toProj (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).imageι
        (ρR' hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom z.1))).asHomogeneousIdeal := by
  refine (mem_Cq_iff hϖ b₄ b₆ _).trans ?_
  simp only [ι_ΦR_of_eq hϖ b₄ b₆ (coe_ρσs hϖ b₄ b₆ z)]

/-- **`ρ(σ)` preserves the decomposition** (proved from the action on coordinates). -/
lemma preserves_ρσ : (decompR hϖ b₄ b₆).Preserves
    (specialFibreHomeomorph (ρσ hϖ b₄ b₆) (ρσ_toSpec hϖ b₄ b₆)) := fun z ↦ by
  have hX := fun i ↦ mem_imageι_ρ'_X_iff (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (σO hϖ) (σO_sO hϖ) (σO_algebraMap hϖ b₄) (σO_algebraMap hϖ b₆)
    (σO_σO hϖ) (sO_ne_zero hϖ) i ((isoR hϖ b₄ b₆).hom z.1)
  have h01 := mem_imageι_ρ'_X01_iff (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (σO hϖ) (σO_sO hϖ) (σO_algebraMap hϖ b₄) (σO_algebraMap hϖ b₆)
    (σO_σO hϖ) (sO_ne_zero hϖ) ((isoR hϖ b₄ b₆).hom z.1)
  exact ⟨(mem_C_iff_ρσ hϖ b₄ b₆ z).trans ((hX 2).trans (mem_C_iff' hϖ b₄ b₆ z).symm),
    (mem_Cp_iff_ρσ hϖ b₄ b₆ z).trans ((and_congr (hX 2) (hX 1)).trans
      (mem_Cp_iff' hϖ b₄ b₆ z).symm),
    (mem_Cq_iff_ρσ hϖ b₄ b₆ z).trans ((and_congr (hX 2) h01).trans
      (mem_Cq_iff' hϖ b₄ b₆ z).symm)⟩

lemma Preserves.of_eq {Z : Type u} [TopologicalSpace Z] {D : TateCovering.Decomp Z}
    {h h' : Z ≃ₜ Z} (hh : D.Preserves h) (e : ∀ z, h' z = h z) : D.Preserves h' := fun z ↦ by
  rw [e]
  exact hh z

/-! ### The object `X₀'` -/

variable (R : Type u) [CommRing R] [Algebra K R] {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A]

/-- **The action of `H = ⟨σ⟩` preserves the decomposition.** -/
lemma preserves_ρs (g : (levelM hϖ R b₄ b₆ heqR A).L.H) :
    (decompR hϖ b₄ b₆).Preserves ((levelM hϖ R b₄ b₆ heqR A).ρs g) := by
  classical
  have key : ∀ z, ((levelM hϖ R b₄ b₆ heqR A).ρs g z).1 =
      (ρfun hϖ R b₄ b₆ A g.1).hom z.1 := fun z ↦ Level.ρs_apply _ g z
  unfold ρfun at key
  split_ifs at key
  · exact Preserves.of_eq (h := Homeomorph.refl _) (fun _ ↦ ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩)
      fun z ↦ Subtype.ext (key z)
  · exact Preserves.of_eq (preserves_ρσ hϖ b₄ b₆) fun z ↦
      Subtype.ext ((key z).trans (coe_ρσs hϖ b₄ b₆ z).symm)

/-- **The object `X₀'`**: the `ℤ`-covering of the special fibre `C ∪ E'` of the restricted model,
with the lifted action of `H = ⟨σ⟩`. -/
def X₀' : TempObj O R A where
  Lv := levelM hϖ R b₄ b₆ heqR A
  P := (decompR hϖ b₄ b₆).toCodeEq (levelM hϖ R b₄ b₆ heqR A).ρs (preserves_ρs hϖ b₄ b₆ R heqR A)

/-- **The covering space `X₀'` is connected.** -/
lemma connectedSpace_X₀' : ConnectedSpace (X₀' hϖ b₄ b₆ R heqR A).P.carrier :=
  (decompR hϖ b₄ b₆).connectedSpace_toCodeEq _ (preserves_ρs hϖ b₄ b₆ R heqR A)
    (TateCovering.Decomp.isPreconnected_comap_C _ (TateModel.isPreconnected_C (sO_mem hϖ)))
    (TateCovering.Decomp.isPreconnected_comap_E _ (TateModel.isPreconnected_E (sO_mem hϖ)))
    (TateCovering.Decomp.nonempty_comap_Cp _
      (by
        dsimp only [TateModel.decomp]
        rw [TateModel.Cp_eq (sO_mem hϖ)]
        exact Set.singleton_nonempty _))
    (TateCovering.Decomp.nonempty_comap_Cq _
      (by
        dsimp only [TateModel.decomp]
        rw [TateModel.Cq_eq (sO_mem hϖ)]
        exact Set.singleton_nonempty _))

/-! ### The deck action -/

/-- The deck transformation of `X₀'` by `d ∈ ℤ`, as a morphism. -/
def deckHom' (d : Multiplicative ℤ) : X₀' hϖ b₄ b₆ R heqR A ⟶ X₀' hϖ b₄ b₆ R heqR A where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by rw [TempObj.spec_map_id_f, Category.comp_id, Category.id_comp]
  h := (decompR hϖ b₄ b₆).deckCodeEq _ (preserves_ρs hϖ b₄ b₆ R heqR A) d
  continuous_h := ((decompR hϖ b₄ b₆).deckCodeEq _ (preserves_ρs hϖ b₄ b₆ R heqR A) d).continuous
  fst_h _ := rfl
  h_act g x := (decompR hϖ b₄ b₆).deckCodeEq_act _ (preserves_ρs hϖ b₄ b₆ R heqR A) d g x

lemma deckHom'_h (d : Multiplicative ℤ) :
    (deckHom' hϖ b₄ b₆ R heqR A d).h =
      (decompR hϖ b₄ b₆).deckCodeEq _ (preserves_ρs hϖ b₄ b₆ R heqR A) d :=
  rfl

lemma deckHom'_mul (d e : Multiplicative ℤ) :
    deckHom' hϖ b₄ b₆ R heqR A e ≫ deckHom' hϖ b₄ b₆ R heqR A d =
      deckHom' hϖ b₄ b₆ R heqR A (d * e) :=
  TempObj.Hom.ext (Category.id_comp _) (Category.id_comp _) (by
    rw [TempObj.comp_h, deckHom'_h, deckHom'_h, deckHom'_h, map_mul]
    rfl)

lemma deckHom'_one : deckHom' hϖ b₄ b₆ R heqR A 1 = 𝟙 _ :=
  TempObj.Hom.ext rfl rfl (by
    rw [deckHom'_h, map_one, TempObj.id_h]
    rfl)

/-- **The deck action** `ℤ →* Aut X₀'`. -/
def deck' : Multiplicative ℤ →* Aut (X₀' hϖ b₄ b₆ R heqR A) where
  toFun d :=
    { hom := deckHom' hϖ b₄ b₆ R heqR A d
      inv := deckHom' hϖ b₄ b₆ R heqR A d⁻¹
      hom_inv_id := by rw [deckHom'_mul, inv_mul_cancel, deckHom'_one]
      inv_hom_id := by rw [deckHom'_mul, mul_inv_cancel, deckHom'_one] }
  map_one' := by
    ext1
    exact deckHom'_one hϖ b₄ b₆ R heqR A
  map_mul' d e := by
    ext1
    rw [Aut.Aut_mul_def, Iso.trans_hom]
    exact (deckHom'_mul hϖ b₄ b₆ R heqR A d e).symm

/-! ### The deck group acts simply transitively on the fibre -/

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

omit [IsAdicComplete (maximalIdeal O) O] [IsDiscreteValuationRing O] in
include K in
lemma two_ne_zero_Ω : (2 : Ω) ≠ 0 := by
  have h := (algebraMap K Ω).injective.ne (two_ne_zero (α := K))
  rwa [map_ofNat, map_zero] at h

omit [IsAdicComplete (maximalIdeal O) O] [IsDiscreteValuationRing O] [CharZero K] in
include hϖ in
lemma cR_ne_zero_Ω : algebraMap R Ω (cR (ϖ := ϖ) R) ≠ 0 := by
  rw [cR, ← IsScalarTower.algebraMap_apply]
  exact (map_ne_zero _).2 fun h ↦ hϖ.ne_zero (Subtype.ext h)

/-- **The deck group `ℤ` acts simply transitively on the fibre of `X₀'`.** The action of
`H⁰ = ⟨σ⟩` on the two geometric points is simply transitive (`exists_fibreAct_eq`,
`eq_one_of_fibreAct_eq`) and commutes with the deck transformations. -/
theorem isDeckTorsor' :
    FibreAut.IsDeckTorsor (F := tempFibre O R A V hV) (X₀' hϖ b₄ b₆ R heqR A)
      (deck' hϖ b₄ b₆ R heqR A) := by
  intro x y
  induction x using Quotient.inductionOn with | h q => ?_
  induction y using Quotient.inductionOn with | h q' => ?_
  obtain ⟨g, hg⟩ : ∃ g : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.H0,
      FiniteLevel.fibreAct Ω (X₀' hϖ b₄ b₆ R heqR A).Lv.L g q.1.1 = q'.1.1 :=
    QuadraticLevel.exists_fibreAct_eq (isUnit_two (K := K) R) (isUnit_cR hϖ R) A q.1.1 q'.1.1
  have hfst : (g • q).1.2.1.1 = q'.1.2.1.1 := Subtype.ext ((g • q).2.trans
    ((congrArg (fun t ↦ ((X₀' hϖ b₄ b₆ R heqR A).Lv.sp V hV t :
      (X₀' hϖ b₄ b₆ R heqR A).Lv.c.scheme)) hg).trans q'.2.symm))
  obtain ⟨d, hd, hu⟩ := (decompR hϖ b₄ b₆).existsUnique_deckCodeEq _
    (preserves_ρs hϖ b₄ b₆ R heqR A) hfst
  have key : ∀ e : Multiplicative ℤ, FibreAut.deckAct (F := tempFibre O R A V hV)
      (X₀' hϖ b₄ b₆ R heqR A) (deck' hϖ b₄ b₆ R heqR A) e
      (⟦q⟧ : (tempFibre O R A V hV).obj (X₀' hϖ b₄ b₆ R heqR A)) =
      (⟦(⟨(q.1.1, (decompR hϖ b₄ b₆).deckCodeEq _ (preserves_ρs hϖ b₄ b₆ R heqR A) e q.1.2),
        q.2⟩ : TempObj.PreFibre Ω V hV (X₀' hϖ b₄ b₆ R heqR A))⟧ :
          (tempFibre O R A V hV).obj (X₀' hϖ b₄ b₆ R heqR A)) := fun e ↦ rfl
  have hact := fun (e : Multiplicative ℤ) (h : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.H) p ↦
    (decompR hϖ b₄ b₆).deckCodeEq_act _ (preserves_ρs hϖ b₄ b₆ R heqR A) e h p
  refine ⟨d, (key d).trans ?_, fun e he ↦ hu e ?_⟩
  · refine Eq.symm (Quotient.sound ⟨g, Subtype.ext (Prod.ext hg ?_)⟩)
    change (X₀' hϖ b₄ b₆ R heqR A).P.act g ((decompR hϖ b₄ b₆).deckCodeEq _
      (preserves_ρs hϖ b₄ b₆ R heqR A) d q.1.2) = q'.1.2
    exact (hact d g q.1.2).symm.trans hd
  · obtain ⟨g', hg'⟩ := Quotient.exact ((key e).symm.trans he)
    have h1 := congrArg (fun r : TempObj.PreFibre Ω V hV (X₀' hϖ b₄ b₆ R heqR A) ↦ r.1.1) hg'
    have h2 := congrArg (fun r : TempObj.PreFibre Ω V hV (X₀' hϖ b₄ b₆ R heqR A) ↦ r.1.2) hg'
    simp only [TempObj.smul_val] at h1 h2
    have hgg : g' * g = 1 := QuadraticLevel.eq_one_of_fibreAct_eq (isUnit_two (K := K) R)
      (isUnit_cR hϖ R) A (two_ne_zero_Ω (K := K)) (cR_ne_zero_Ω hϖ R) (g := g' * g) (t := q.1.1)
      (by
        change FiniteLevel.fibreAct Ω (X₀' hϖ b₄ b₆ R heqR A).Lv.L g'
          (FiniteLevel.fibreAct Ω (X₀' hϖ b₄ b₆ R heqR A).Lv.L g q.1.1) = q.1.1
        rw [hg, h1])
    have hg'' : g' = g⁻¹ := eq_inv_of_mul_eq_one_left hgg
    subst hg''
    have h3 : ∀ p, (X₀' hϖ b₄ b₆ R heqR A).P.act (g : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.H)
        ((X₀' hϖ b₄ b₆ R heqR A).P.act ((g⁻¹ : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.H0) :
          (X₀' hϖ b₄ b₆ R heqR A).Lv.L.H) p) = p := fun p ↦ by
      rw [← Homeomorph.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, map_one]
      rfl
    exact (hact e g q.1.2).trans ((congrArg _ h2.symm).trans (h3 q'.1.2))

/-! ### The character -/

variable [IsAlgClosed Ω]

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero K]
  [Algebra K Ω] [IsScalarTower K R Ω] in
lemma exists_sqrt_Ω : ∃ z : Ω, z ^ 2 = algebraMap R Ω (cR (ϖ := ϖ) R) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (algebraMap R Ω (cR (ϖ := ϖ) R))
  exact ⟨z, by rw [hz, sq]⟩

/-- A geometric point `B → Ω`: `t ↦ √ϖ`. -/
def pointΩ : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.B →ₐ[R] Ω :=
  QuadraticLevel.lift (cR (ϖ := ϖ) R) (exists_sqrt_Ω (ϖ := ϖ) R).choose (by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C,
      (exists_sqrt_Ω (ϖ := ϖ) R).choose_spec, sub_self])

/-- A point of the fibre of `X₀'`. -/
def basePoint' : (tempFibre O R A V hV).obj (X₀' hϖ b₄ b₆ R heqR A) :=
  Quotient.mk _ ⟨(pointΩ hϖ b₄ b₆ R heqR A,
    ⟨((X₀' hϖ b₄ b₆ R heqR A).Lv.sp V hV (pointΩ hϖ b₄ b₆ R heqR A), 0), Set.mem_univ _⟩), rfl⟩

/-- **The character `temperedPi1 → ℤ`** defined by the deck torsor `X₀'` (`v(q) = 1`). -/
def character' : temperedPi1 O R A V hV →* Multiplicative ℤ :=
  FibreAut.deckCharacter (X₀' hϖ b₄ b₆ R heqR A) (deck' hϖ b₄ b₆ R heqR A)
    (basePoint' hϖ b₄ b₆ R heqR A V hV) (isDeckTorsor' hϖ b₄ b₆ R heqR A V hV)

/-- The character is continuous. -/
theorem continuous_character' : Continuous (character' hϖ b₄ b₆ R heqR A V hV) :=
  FibreAut.continuous_deckCharacter _ _ _ _

end

end TateRestrict

end TemperedFundamentalGroups
