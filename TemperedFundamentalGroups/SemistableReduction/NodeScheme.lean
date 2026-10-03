/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeSmooth
import TemperedFundamentalGroups.SemistableReduction.Statement

/-!
# Thickness of node points of models (W8′, H3 for schemes)

Blueprint §9.7. For a projective `O`-model `c` over a discrete valuation ring:
* `IsNodeAt` ascends and descends along étale maps (`IsNodeAt.of_etale`,
  `IsNodeAt.of_etale_of_comap`);
* it moves between affine neighbourhoods of a point (through a common basic open,
  `ModelCode.isNodeAt_transfer`);
* hence the thickness of a node point is well defined (`ModelCode.IsNodeOfThickness.unique`), and
  every node point of a semistable model has a thickness `≥ 1`
  (`ModelCode.exists_isNodeOfThickness`): the first four clauses of `ModelCode.IsHarmonic`.
-/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace SemistableReduction

variable {O : Type u} [CommRing O] {ϖ : O} {n : ℕ} {A A' : Type u} [CommRing A] [Algebra O A]
  [CommRing A'] [Algebra O A']

/-- `IsNodeAt` descends from étale neighbourhoods. -/
theorem IsNodeAt.of_etale_of_comap (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) {𝔭' : Ideal A'}
    (h : IsNodeAt ϖ n 𝔭') : IsNodeAt ϖ n (𝔭'.comap φ.toRingHom) := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp, hu, hv⟩ := h
  refine ⟨C, inferInstance, g.comp φ.toRingHom, f, 𝔮,
    RingHom.Etale.stableUnderComposition _ _ hφ hg, hf, h𝔮, by rw [← Ideal.comap_comap, hcomap],
    ?_, hu, hv⟩
  rw [hcomp, RingHom.comp_assoc]
  exact congrArg g.comp (AlgHom.comp_algebraMap φ).symm

/-- `IsNodeAt` ascends along étale maps. -/
theorem IsNodeAt.of_etale (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) (𝔭' : Ideal A') [𝔭'.IsPrime]
    (h : IsNodeAt ϖ n (𝔭'.comap φ.toRingHom)) : IsNodeAt ϖ n 𝔭' := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp, hu, hv⟩ := h
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  letI : Algebra A C := g.toAlgebra
  obtain ⟨R, hR, hR₁, hR₂⟩ := exists_isPrime_tensorProduct (A := A) 𝔭' 𝔮 hcomap.symm
  have hl : (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] C).Etale :=
    RingHom.Etale.isStableUnderBaseChange.tensorProduct A' hg
  have hr : (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom.Etale :=
    etale_includeRight hφ
  refine ⟨A' ⊗[A] C, inferInstance, Algebra.TensorProduct.includeLeftRingHom,
    (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom.comp f, R, hl,
    RingHom.Etale.stableUnderComposition f _ hf hr, hR, hR₁, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hcomp, ← RingHom.comp_assoc]
    ext o
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
    change 1 ⊗ₜ[A] (algebraMap A C (algebraMap O A o)) = _
    rw [← AlgHom.commutes φ o]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap O A o)).symm
  · rw [← hR₂] at hu; exact hu
  · rw [← hR₂] at hv; exact hv

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction

variable {O : Type u} [CommRing O] (c : TemperedFundamentalGroups.ModelCode O)

/-- The restriction of sections, as an `O`-algebra map. -/
noncomputable def restrictAlgHom {U V : c.scheme.Opens} (h : V ≤ U) :
    letI := sectionsAlgebra c U
    letI := sectionsAlgebra c V
    Γ(c.scheme, U) →ₐ[O] Γ(c.scheme, V) :=
  letI := sectionsAlgebra c U
  letI := sectionsAlgebra c V
  { (c.scheme.presheaf.map (homOfLE h).op).hom with
    commutes' := fun o ↦ by
      change (c.scheme.presheaf.map (homOfLE h).op).hom
          (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ c.toSpec.appTop ≫
            c.scheme.presheaf.map (homOfLE le_top).op).hom o) =
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ c.toSpec.appTop ≫
            c.scheme.presheaf.map (homOfLE le_top).op).hom o
      rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc, ← Functor.map_comp]
      rfl }

lemma restrictAlgHom_toRingHom {U V : c.scheme.Opens} (h : V ≤ U) :
    letI := sectionsAlgebra c U
    letI := sectionsAlgebra c V
    (restrictAlgHom c h).toRingHom = (c.scheme.presheaf.map (homOfLE h).op).hom :=
  rfl

variable {c}

/-- Restriction to a basic open is étale. -/
lemma restrict_etale {U V : c.scheme.Opens} (hU : IsAffineOpen U) (g : Γ(c.scheme, U))
    (hV : V = c.scheme.basicOpen g) (h : V ≤ U) :
    (c.scheme.presheaf.map (homOfLE h).op).hom.Etale := by
  subst hV
  haveI := hU.isLocalization_basicOpen g
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway g)

/-- Restriction maps the prime of a point to the prime of the point. -/
lemma comap_primeIdealOf_restrict {U V : c.scheme.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U) {x : c.scheme} (hx : x ∈ V) :
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (c.scheme.presheaf.map (homOfLE h).op).hom =
      (hU.primeIdealOf ⟨x, h hx⟩).asIdeal := by
  have := IsAffineOpen.comap_primeIdealOf_appLE (f := 𝟙 c.scheme) U hU V hV h hx
  have e : Scheme.Hom.appLE (𝟙 c.scheme) U V h = c.scheme.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
    exact Category.id_comp _
  rw [e] at this
  exact congrArg PrimeSpectrum.asIdeal this

/-- **`IsNodeAt` does not depend on the affine neighbourhood.** -/
theorem isNodeAt_transfer {ϖ : O} {n : ℕ} {x : c.scheme} {U U' : c.scheme.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hx : x ∈ U) (hx' : x ∈ U')
    (h : letI := sectionsAlgebra c U
      IsNodeAt ϖ n (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    letI := sectionsAlgebra c U'
    IsNodeAt ϖ n (hU'.primeIdealOf ⟨x, hx'⟩).asIdeal := by
  obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hU hU' x ⟨hx, hx'⟩
  set V := c.scheme.basicOpen f
  have hV : IsAffineOpen V := hU.basicOpen f
  have hVU : V ≤ U := c.scheme.basicOpen_le f
  have hVU' : V ≤ U' := e ▸ c.scheme.basicOpen_le g
  letI := sectionsAlgebra c U
  letI := sectionsAlgebra c U'
  letI := sectionsAlgebra c V
  have h₁ : IsNodeAt ϖ n (hV.primeIdealOf ⟨x, hxf⟩).asIdeal := by
    refine IsNodeAt.of_etale (restrictAlgHom c hVU) (restrict_etale hU f rfl hVU) _ ?_
    rw [restrictAlgHom_toRingHom, comap_primeIdealOf_restrict hU hV hVU hxf]
    exact h
  have h₂ := IsNodeAt.of_etale_of_comap (restrictAlgHom c hVU') (restrict_etale hU' g e hVU') h₁
  rw [restrictAlgHom_toRingHom, comap_primeIdealOf_restrict hU' hV hVU' hxf] at h₂
  exact h₂

/-- A node point of thickness `n` is `IsNodeAt` in every affine neighbourhood. -/
theorem IsNodeOfThickness.isNodeAt [IsLocalRing O] {ϖ : O} {n : ℕ} {x : c.scheme}
    (h : IsNodeOfThickness ϖ c x n) {U : c.scheme.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    letI := sectionsAlgebra c U
    IsNodeAt ϖ n (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  obtain ⟨⟨-, hns⟩, U₀, hU₀, hx₀, hloc⟩ := h
  refine isNodeAt_transfer hU₀ hU hx₀ hx ?_
  letI := sectionsAlgebra c U₀
  exact isNodeAt_of_not_smooth hloc fun hs ↦ hns ⟨U₀, hU₀, hx₀, hs⟩

/-- **The thickness of a node point is well defined.** -/
theorem IsNodeOfThickness.unique [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {n m : ℕ} {x : c.scheme} (hn : IsNodeOfThickness ϖ c x n)
    (hm : IsNodeOfThickness ϖ c x m) : n = m := by
  obtain ⟨-, U, hU, hx, -⟩ := id hn
  letI := sectionsAlgebra c U
  exact (hn.isNodeAt hU hx).unique hϖ (hm.isNodeAt hU hx)

/-- **Every node point of a semistable model has a thickness `n ≥ 1`.** -/
theorem exists_isNodeOfThickness [IsLocalRing O] {ϖ : O}
    (hc : TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ c) {x : c.scheme}
    (hx : IsNodePt c x) : ∃ n, 1 ≤ n ∧ IsNodeOfThickness ϖ c x n := by
  obtain ⟨U, hU, hxU, hs⟩ := hc x
  letI := sectionsAlgebra c U
  rcases hs with ⟨n, hn⟩ | hpoly
  · have hnode : IsNodeAt ϖ n (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
      isNodeAt_of_not_smooth hn fun hs ↦ hx.2 ⟨U, hU, hxU, hs⟩
    exact ⟨n, hnode.pos, hx, U, hU, hxU, hn⟩
  · exact absurd ⟨U, hU, hxU, hpoly⟩ hx.2

end TemperedFundamentalGroups.SemistableReduction.ModelCode
