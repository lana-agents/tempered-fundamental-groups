/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.BaseChange
import TemperedFundamentalGroups.Models.Projective
import TemperedFundamentalGroups.Models.Specialization

/-!
# Base change of model codes (Blueprint §11, F8)

For a ring map `f : R₀ →+* R₁` and a model code `c` over `R₀` (a closed subscheme of `ℙᵐ_{R₀}`),
the base change `c.baseChange f` is the closed subscheme `c ×_{ℙᵐ_{R₀}} ℙᵐ_{R₁}` of `ℙᵐ_{R₁}`
(the image of the base change of the closed immersion, `Scheme.Hom.ker`). Since
`ℙᵐ_{R₁} = ℙᵐ_{R₀} ×_{Spec R₀} Spec R₁` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`, in
oka), it is the fibre product `c ×_{Spec R₀} Spec R₁` (`ModelCode.isPullback_baseChange`), with
projection `ModelCode.bcFst f c : (c.baseChange f).scheme ⟶ c.scheme`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace TemperedFundamentalGroups

namespace ModelCode

variable {R₀ R₁ : Type u} [CommRing R₀] [CommRing R₁] (f : R₀ →+* R₁) (c : ModelCode R₀)

/-- The map `ℙᵐ_{R₁} ⟶ ℙᵐ_{R₀}`. -/
noncomputable def pmap (m : ℕ) : projSpace R₁ m ⟶ projSpace R₀ m := ProjectiveSpace.map (n := m) f

lemma isPullback_pmap (m : ℕ) : IsPullback (pmap f m) (projSpace.toSpec R₁ m)
    (projSpace.toSpec R₀ m) (Spec.map (CommRingCat.ofHom f)) :=
  ProjectiveSpace.isPullback_map (n := m) f

/-- The base change of the closed immersion `c ⟶ ℙᵐ_{R₀}` along `ℙᵐ_{R₁} ⟶ ℙᵐ_{R₀}`. -/
noncomputable abbrev bcSnd : pullback c.I.subschemeι (pmap f c.m) ⟶ projSpace R₁ c.m :=
  pullback.snd _ _

instance : IsClosedImmersion (bcSnd f c) := by
  unfold bcSnd
  infer_instance

/-- **The base change of a model code** along `f : R₀ →+* R₁`. -/
noncomputable def baseChange : ModelCode R₁ :=
  ⟨c.m, (bcSnd f c).ker⟩

/-- The base change code is the fibre product `c ×_{ℙᵐ_{R₀}} ℙᵐ_{R₁}`. -/
noncomputable def bcIso :
    pullback c.I.subschemeι (pmap f c.m) ≅ (c.baseChange f).scheme :=
  @asIso _ _ _ _ (bcSnd f c).toImage (IsClosedImmersion.instIsIsoSchemeToImage (bcSnd f c))

/-- The projection `c ×_{R₀} R₁ ⟶ c`. -/
noncomputable def bcFst : (c.baseChange f).scheme ⟶ c.scheme :=
  (c.bcIso f).inv ≫ pullback.fst _ _

lemma bcIso_hom_subschemeι :
    (c.bcIso f).hom ≫ (c.baseChange f).I.subschemeι = bcSnd f c :=
  Scheme.Hom.toImage_imageι _

lemma bcIso_inv_snd : (c.bcIso f).inv ≫ bcSnd f c = (c.baseChange f).I.subschemeι := by
  rw [← bcIso_hom_subschemeι]
  exact Iso.inv_hom_id_assoc _ _

/-- **Base change of model codes is a fibre product** `c ×_{Spec R₀} Spec R₁`. -/
theorem isPullback_baseChange :
    IsPullback (c.bcFst f) (c.baseChange f).toSpec c.toSpec
      (Spec.map (CommRingCat.ofHom f)) := by
  have h₁ : IsPullback (pullback.fst c.I.subschemeι (pmap f c.m))
      (bcSnd f c) c.I.subschemeι (pmap f c.m) := IsPullback.of_hasPullback _ _
  have h := h₁.paste_vert (isPullback_pmap f c.m)
  refine IsPullback.of_iso h (c.bcIso f) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change pullback.fst _ _ ≫ 𝟙 _ = (c.bcIso f).hom ≫ (c.bcIso f).inv ≫ pullback.fst _ _
    rw [Iso.hom_inv_id_assoc]
    exact Category.comp_id _
  · change (bcSnd f c ≫ projSpace.toSpec R₁ c.m) ≫ 𝟙 _ =
      (c.bcIso f).hom ≫ (c.baseChange f).I.subschemeι ≫ projSpace.toSpec R₁ c.m
    rw [← Category.assoc, bcIso_hom_subschemeι]
    exact Category.comp_id _
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

lemma bcFst_toSpec :
    c.bcFst f ≫ c.toSpec = (c.baseChange f).toSpec ≫ Spec.map (CommRingCat.ofHom f) :=
  (c.isPullback_baseChange f).w

/-- Morphisms into the base change are determined by their projections. -/
lemma bc_hom_ext {T : Scheme.{u}} {a b : T ⟶ (c.baseChange f).scheme}
    (h₁ : a ≫ c.bcFst f = b ≫ c.bcFst f)
    (h₂ : a ≫ (c.baseChange f).toSpec = b ≫ (c.baseChange f).toSpec) : a = b :=
  (c.isPullback_baseChange f).hom_ext h₁ h₂

/-- The universal property of the base change. -/
noncomputable def bcLift {T : Scheme.{u}} (a : T ⟶ c.scheme) (b : T ⟶ Spec (CommRingCat.of R₁))
    (w : a ≫ c.toSpec = b ≫ Spec.map (CommRingCat.ofHom f)) : T ⟶ (c.baseChange f).scheme :=
  (c.isPullback_baseChange f).lift a b w

@[reassoc (attr := simp)]
lemma bcLift_fst {T : Scheme.{u}} (a : T ⟶ c.scheme) (b : T ⟶ Spec (CommRingCat.of R₁))
    (w : a ≫ c.toSpec = b ≫ Spec.map (CommRingCat.ofHom f)) :
    c.bcLift f a b w ≫ c.bcFst f = a :=
  (c.isPullback_baseChange f).lift_fst a b w

@[reassoc (attr := simp)]
lemma bcLift_toSpec {T : Scheme.{u}} (a : T ⟶ c.scheme) (b : T ⟶ Spec (CommRingCat.of R₁))
    (w : a ≫ c.toSpec = b ≫ Spec.map (CommRingCat.ofHom f)) :
    c.bcLift f a b w ≫ (c.baseChange f).toSpec = b :=
  (c.isPullback_baseChange f).lift_snd a b w

section Local

variable [IsLocalRing R₀] [IsLocalRing R₁] [IsLocalHom f]

lemma bcFst_mem_specialFibre (z : specialFibre (c.baseChange f).toSpec) :
    c.bcFst f z.1 ∈ specialFibre c.toSpec := by
  rw [mem_specialFibre, ← Scheme.Hom.comp_apply, bcFst_toSpec, Scheme.Hom.comp_apply,
    (mem_specialFibre _ _).1 z.2]
  exact Spec_closedPoint (f := CommRingCat.ofHom f)

/-- The projection of special fibres `|(c ×_{R₀} R₁)_s| → |c_s|`. -/
noncomputable def bcFstS : specialFibre (c.baseChange f).toSpec → specialFibre c.toSpec :=
  fun z => ⟨c.bcFst f z.1, c.bcFst_mem_specialFibre f z⟩

lemma continuous_bcFstS : Continuous (c.bcFstS f) :=
  ((c.bcFst f).continuous.comp continuous_subtype_val).subtype_mk _

end Local

end ModelCode

end TemperedFundamentalGroups
