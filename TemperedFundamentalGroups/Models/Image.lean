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

variable {R : Type u} [CommRing R] (c : ModelCode R) {T : Scheme.{u}} (j : T ⟶ c.I.subscheme)
  [QuasiCompact j]

/-- **The scheme-theoretic image** of `j : T ⟶ c`, as a model code. -/
noncomputable abbrev image : ModelCode R := ⟨c.m, (j ≫ c.I.subschemeι).ker⟩

/-- The factorization `T ⟶ image`. -/
noncomputable def toImg : T ⟶ (c.image j).I.subscheme := (j ≫ c.I.subschemeι).toImage

instance : IsSchemeTheoreticallyDominant (c.toImg j) :=
  isSchemeTheoreticallyDominant_toImage _

lemma toImg_subschemeι : c.toImg j ≫ (c.image j).I.subschemeι = j ≫ c.I.subschemeι :=
  Scheme.Hom.toImage_imageι _

lemma ker_le : c.I.subschemeι.ker ≤ (c.image j).I.subschemeι.ker := by
  change _ ≤ (j ≫ c.I.subschemeι).ker.subschemeι.ker
  exact (Scheme.Hom.le_ker_comp j c.I.subschemeι).trans
    (Scheme.IdealSheafData.ker_subschemeι _).ge

/-- The closed immersion `image ⟶ c`. -/
noncomputable def imgι : (c.image j).I.subscheme ⟶ c.I.subscheme :=
  IsClosedImmersion.lift c.I.subschemeι (c.image j).I.subschemeι (c.ker_le j)

@[reassoc (attr := simp)]
lemma imgι_subschemeι : c.imgι j ≫ c.I.subschemeι = (c.image j).I.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

instance : IsClosedImmersion (c.imgι j) := by
  have : IsClosedImmersion (c.imgι j ≫ c.I.subschemeι) := by
    rw [imgι_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ c.I.subschemeι

@[reassoc (attr := simp)]
lemma toImg_imgι : c.toImg j ≫ c.imgι j = j := by
  rw [← cancel_mono c.I.subschemeι, Category.assoc, imgι_subschemeι, toImg_subschemeι]

@[reassoc]
lemma imgι_toSpec : c.imgι j ≫ c.toSpec = (c.image j).toSpec := by
  change c.imgι j ≫ c.I.subschemeι ≫ projSpace.toSpec R c.m =
    (c.image j).I.subschemeι ≫ projSpace.toSpec R c.m
  rw [← Category.assoc, imgι_subschemeι]

variable {d : ModelCode R} {T' : Scheme.{u}} (j' : T' ⟶ d.I.subscheme) [QuasiCompact j']
  (g : c.I.subscheme ⟶ d.I.subscheme) (a : T ⟶ T') (h : j ≫ g = a ≫ j')

include h in
lemma imageMap_ker_le :
    (d.image j').I.subschemeι.ker ≤ (c.imgι j ≫ g ≫ d.I.subschemeι).ker := by
  change (j' ≫ d.I.subschemeι).ker.subschemeι.ker ≤ _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  have h1 : (c.toImg j ≫ c.imgι j ≫ g ≫ d.I.subschemeι).ker =
      (c.imgι j ≫ g ≫ d.I.subschemeι).ker := by
    rw [Scheme.Hom.ker_comp, (c.toImg j).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rw [← h1, toImg_imgι_assoc, ← Category.assoc, h, Category.assoc]
  exact Scheme.Hom.le_ker_comp _ _

/-- **Functoriality of images**: a commutative square `j ≫ g = a ≫ j'` induces
`image j ⟶ image j'`. -/
noncomputable def imageMap : (c.image j).I.subscheme ⟶ (d.image j').I.subscheme :=
  IsClosedImmersion.lift (d.image j').I.subschemeι (c.imgι j ≫ g ≫ d.I.subschemeι)
    (c.imageMap_ker_le j j' g a h)

@[reassoc (attr := simp)]
lemma imageMap_imgι : c.imageMap j j' g a h ≫ d.imgι j' = c.imgι j ≫ g := by
  rw [← cancel_mono d.I.subschemeι, Category.assoc, imgι_subschemeι, imageMap,
    IsClosedImmersion.lift_fac, Category.assoc]

@[reassoc (attr := simp)]
lemma toImg_imageMap : c.toImg j ≫ c.imageMap j j' g a h = a ≫ d.toImg j' := by
  rw [← cancel_mono (d.imgι j'), Category.assoc, imageMap_imgι, toImg_imgι_assoc, h,
    Category.assoc, toImg_imgι]

end ModelCode

end TemperedFundamentalGroups
