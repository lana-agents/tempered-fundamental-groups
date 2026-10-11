/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TemperedFundamentalGroups.Models.Projective

/-!
# Scheme-theoretic images in model codes (Blueprint §11, F8)

For a model code `c` and a quasi-compact morphism `j : T ⟶ c`, the scheme-theoretic image of `j`
is again a model code `c.image j` (a closed subscheme of the same `ℙᵐ`), with the closed immersion
`c.imgι j : c.image j ⟶ c` and the scheme-theoretically dominant `c.toImg j : T ⟶ c.image j`.
Images are functorial for commutative squares (`ModelCode.imageMap`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

/-- The factorization through the scheme-theoretic image is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : Y.affineOpens => (⟨f.imageι ⁻¹ᵁ V.1, V.2.preimage f.imageι⟩ : f.image.affineOpens))
    ?_ fun V => ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top Y, Scheme.Hom.preimage_top]
  · rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    exact (f.toImage_app_injective (U := V)) (hx.trans (map_zero _).symm)

namespace ModelCode

variable {R : Type u} [CommRing R] (c : ModelCode R)

/-- The closed immersion `c ⟶ ℙᵐ_R`. -/
noncomputable def ι : c.scheme ⟶ projSpace R c.m := c.I.subschemeι

instance : IsClosedImmersion c.ι :=
  inferInstanceAs (IsClosedImmersion c.I.subschemeι)

lemma ι_toSpec : c.ι ≫ projSpace.toSpec R c.m = c.toSpec := rfl

instance : QuasiSeparatedSpace c.scheme :=
  quasiSeparatedSpace_of_quasiSeparated c.toSpec

variable {T : Scheme.{u}} (j : T ⟶ c.scheme) [QuasiCompact j]

/-- **The scheme-theoretic image** of `j : T ⟶ c`, as a model code. -/
noncomputable abbrev image : ModelCode R := ⟨c.m, (j ≫ c.ι).ker⟩

/-- The factorization `T ⟶ image`. -/
noncomputable def toImg : T ⟶ (c.image j).scheme := (j ≫ c.ι).toImage

instance : IsSchemeTheoreticallyDominant (c.toImg j) :=
  isSchemeTheoreticallyDominant_toImage _

lemma toImg_ι : c.toImg j ≫ (c.image j).ι = j ≫ c.ι :=
  Scheme.Hom.toImage_imageι _

lemma ker_le : c.ι.ker ≤ (c.image j).ι.ker := by
  change _ ≤ (j ≫ c.ι).ker.subschemeι.ker
  exact (Scheme.Hom.le_ker_comp j c.ι).trans (Scheme.IdealSheafData.ker_subschemeι _).ge

/-- The closed immersion `image ⟶ c`. -/
noncomputable def imgι : (c.image j).scheme ⟶ c.scheme :=
  IsClosedImmersion.lift c.ι (c.image j).ι (c.ker_le j)

@[reassoc (attr := simp)]
lemma imgι_ι : c.imgι j ≫ c.ι = (c.image j).ι :=
  IsClosedImmersion.lift_fac _ _ _

instance : IsClosedImmersion (c.imgι j) := by
  have : IsClosedImmersion (c.imgι j ≫ c.ι) := by
    rw [imgι_ι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ c.ι

@[reassoc (attr := simp)]
lemma toImg_imgι : c.toImg j ≫ c.imgι j = j := by
  rw [← cancel_mono c.ι, Category.assoc, imgι_ι, toImg_ι]

@[reassoc]
lemma imgι_toSpec : c.imgι j ≫ c.toSpec = (c.image j).toSpec := by
  rw [← ι_toSpec, ← ι_toSpec, imgι_ι_assoc]

variable {d : ModelCode R} {T' : Scheme.{u}} (j' : T' ⟶ d.scheme) [QuasiCompact j']
  (g : c.scheme ⟶ d.scheme) (a : T ⟶ T') (h : j ≫ g = a ≫ j')

include h in
lemma imageMap_ker_le : (d.image j').ι.ker ≤ (c.imgι j ≫ g ≫ d.ι).ker := by
  change (j' ≫ d.ι).ker.subschemeι.ker ≤ _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  have h1 : (c.toImg j ≫ c.imgι j ≫ g ≫ d.ι).ker = (c.imgι j ≫ g ≫ d.ι).ker := by
    rw [Scheme.Hom.ker_comp, (c.toImg j).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rw [← h1, toImg_imgι_assoc, ← Category.assoc, h, Category.assoc]
  exact Scheme.Hom.le_ker_comp _ _

/-- **Functoriality of images**: a commutative square `j ≫ g = a ≫ j'` induces
`image j ⟶ image j'`. -/
noncomputable def imageMap : (c.image j).scheme ⟶ (d.image j').scheme :=
  IsClosedImmersion.lift (d.image j').ι (c.imgι j ≫ g ≫ d.ι) (c.imageMap_ker_le j j' g a h)

@[reassoc (attr := simp)]
lemma imageMap_imgι : c.imageMap j j' g a h ≫ d.imgι j' = c.imgι j ≫ g := by
  rw [← cancel_mono d.ι, Category.assoc, imgι_ι, imageMap, IsClosedImmersion.lift_fac,
    Category.assoc]

@[reassoc (attr := simp)]
lemma toImg_imageMap : c.toImg j ≫ c.imageMap j j' g a h = a ≫ d.toImg j' := by
  rw [← cancel_mono (d.imgι j'), Category.assoc, imageMap_imgι, toImg_imgι_assoc, h,
    Category.assoc, toImg_imgι]

end ModelCode

end TemperedFundamentalGroups
