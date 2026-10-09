/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Sigma

/-!
# Semistability along open immersions and of finite unions

Blueprint §9.7 (W10 assembly).

* `isSemistable_of_isOpenImmersion_cover`: if model codes `c k` map to a model code `d` over `O`
  by open immersions whose images cover `d`, and every `c k` is semistable, then `d` is
  semistable. The affine neighbourhood of `f x` is the image of an affine neighbourhood of `x`;
  the sections are identified by `Scheme.Hom.appIso`, and the primes of the points correspond
  (`IsAffineOpen.comap_primeIdealOf_appLE`).
* `ModelCode.isSemistable_sigma`: a finite disjoint union of semistable model codes is
  semistable.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

namespace ModelCode

variable {O : Type u} [CommRing O]

/-- **Semistability at the image of a point under an open immersion over `O`.** -/
theorem isSemistableAt_image {c d : TemperedFundamentalGroups.ModelCode O} (ϖ : O)
    (f : c.scheme ⟶ d.scheme) [IsOpenImmersion f] (hf : f ≫ d.toSpec = c.toSpec)
    {x : c.scheme} {U : c.scheme.Opens} (hU : IsAffineOpen U) (hx : x ∈ U)
    (h : letI := sectionsAlgebra c U
      _root_.SemistableReduction.IsSemistableAt ϖ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V : d.scheme.Opens) (hV : IsAffineOpen V) (hfx : f x ∈ V),
      letI := sectionsAlgebra d V
      _root_.SemistableReduction.IsSemistableAt ϖ (hV.primeIdealOf ⟨f x, hfx⟩).asIdeal := by
  have hV : IsAffineOpen (f ''ᵁ U) := hU.image_of_isOpenImmersion f
  have hfx : f x ∈ f ''ᵁ U := ⟨x, hx, rfl⟩
  refine ⟨f ''ᵁ U, hV, hfx, ?_⟩
  letI := sectionsAlgebra c U
  letI := sectionsAlgebra d (f ''ᵁ U)
  have hle : U ≤ f ⁻¹ᵁ (f ''ᵁ U) := (Scheme.Hom.preimage_image_eq f U).ge
  let φr : Γ(d.scheme, f ''ᵁ U) ⟶ Γ(c.scheme, U) := f.appLE (f ''ᵁ U) U hle
  have hφbij : Function.Bijective φr.hom := by
    have : φr = (f.appIso U).hom := (f.appIso_hom' U).symm
    rw [this]
    exact (ConcreteCategory.bijective_of_isIso (f.appIso U).hom)
  let φ : Γ(d.scheme, f ''ᵁ U) →ₐ[O] Γ(c.scheme, U) :=
    { φr.hom with
      commutes' := fun o => by
        change (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ d.toSpec.appTop ≫
            d.scheme.presheaf.map (homOfLE le_top).op) ≫ φr).hom o =
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ c.toSpec.appTop ≫
            c.scheme.presheaf.map (homOfLE le_top).op).hom o
        congr 2
        simp only [Category.assoc, φr]
        rw [← hf, Scheme.Hom.comp_appTop, Category.assoc]
        congr 1
        rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        congr 1 }
  have hcomap := IsAffineOpen.comap_primeIdealOf_appLE (f := f) (f ''ᵁ U) hV U hU hle hx
  have := _root_.SemistableReduction.IsSemistableAt.of_etale_of_comap φ
    (RingHom.Etale.of_bijective hφbij) h
  have heq : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.comap φ.toRingHom =
      (hV.primeIdealOf ⟨f x, hfx⟩).asIdeal := congrArg PrimeSpectrum.asIdeal hcomap
  rwa [heq] at this

/-- **Semistability from an open cover by semistable model codes.** -/
theorem isSemistable_of_isOpenImmersion_cover {ι : Type*}
    {c : ι → TemperedFundamentalGroups.ModelCode O}
    {d : TemperedFundamentalGroups.ModelCode O} (ϖ : O) (f : ∀ k, (c k).scheme ⟶ d.scheme)
    [∀ k, IsOpenImmersion (f k)] (hf : ∀ k, f k ≫ d.toSpec = (c k).toSpec)
    (hcov : ∀ y : d.scheme, ∃ k, ∃ x, f k x = y) (hc : ∀ k, IsSemistable ϖ (c k)) :
    IsSemistable ϖ d := by
  intro y
  obtain ⟨k, x, rfl⟩ := hcov y
  obtain ⟨U, hU, hx, h⟩ := hc k x
  exact isSemistableAt_image ϖ (f k) (hf k) hU hx h

/-- **A finite disjoint union of semistable model codes is semistable.** -/
theorem isSemistable_sigma {ι : Type u} [Fintype ι]
    (c : ι → TemperedFundamentalGroups.ModelCode O)
    (ϖ : O) (hc : ∀ k, IsSemistable ϖ (c k)) :
    IsSemistable ϖ (_root_.SemistableReduction.ModelCode.sigma c) := by
  refine isSemistable_of_isOpenImmersion_cover ϖ (_root_.SemistableReduction.ModelCode.sigmaι c)
    (_root_.SemistableReduction.ModelCode.sigmaι_toSpec c) (fun y => ?_) hc
  obtain ⟨y', rfl⟩ :
      ∃ y', (_root_.SemistableReduction.ModelCode.sigmaIso c).hom y' = y :=
    ⟨(_root_.SemistableReduction.ModelCode.sigmaIso c).inv y, by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
  obtain ⟨z, hz⟩ := (sigmaOpenCover (fun k ↦ (c k).scheme)).covers y'
  refine ⟨(sigmaOpenCover (fun k ↦ (c k).scheme)).idx y', z, ?_⟩
  change ((sigmaOpenCover (fun k ↦ (c k).scheme)).f _ ≫
    (_root_.SemistableReduction.ModelCode.sigmaIso c).hom) z = _
  rw [Scheme.Hom.comp_apply, hz]

end ModelCode

end TemperedFundamentalGroups.SemistableReduction
