/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.WCentre
import TemperedFundamentalGroups.SemistableReduction.CrossingSource

/-!
# The centre determines the valuation at generic points of components of W-models

The analogue of `WData.centreDetermines` (`Andre/WCentre.lean`) for `ModelCode.IsWModel`: at the
generic point of a component of the special fibre of a W-model, the local ring of a projective
chart is a valuation subring of `L` (`localSubring_props`, `LocalSubring.ofPrime_mem_or_inv_mem`),
so at most one valuation subring has this centre (`centreDetermines_gp`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open ValuativeCentre ModelCode

variable {K' L : Type u} [Field K'] [Field L] [Algebra K' L] {O' : ValuationSubring K'}
  [IsDiscreteValuationRing O'] [Algebra O' L] [IsScalarTower O' K' L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O'} {j : Spec (CommRingCat.of L) ⟶ c.scheme}

/-- **The centre determines the valuation at generic points of components.** -/
theorem centreDetermines_gp (hW : IsWModel O' L x c j) {ϖ : O'} (hϖ : Irreducible ϖ)
    {v : Set c.scheme} (hv : v ∈ components c) : CentreDetermines j (gp hv) := by
  obtain ⟨hx, ι, _, _, a, b, halg, hb, n, g, hg, hpts, E, he₁, he₂⟩ := hW
  letI := _root_.TemperedFundamentalGroups.SemistableReduction.xLineAlgebra L hx
  haveI : IsScalarTower K' (RatFunc K') L := IsScalarTower.of_algebraMap_eq fun k ↦ by
    change algebraMap K' L k = RatFunc.liftAlgHom _ _ (algebraMap K' (RatFunc K') k)
    rw [AlgHom.commutes]
  let R₀ := _root_.SemistableReduction.baseRing L O'.valuation.valuationSubring
  have hR : (algebraMap O' L).range = R₀ :=
    _root_.TemperedFundamentalGroups.SemistableReduction.ModelCode.range_algebraMap_eq_baseRing'
  set ζ := gp hv
  obtain ⟨i, hi⟩ := _root_.SemistableReduction.ProjScheme.exists_mem_chartOpen hg (E.hom ζ)
  rw [← _root_.SemistableReduction.ProjScheme.opensRange_chartι R₀ hR hg i] at hi
  obtain ⟨p, hp⟩ := hi
  let ch := _root_.SemistableReduction.ProjScheme.chartι R₀ hR hg i
  let Ach := _root_.SemistableReduction.projChart R₀ g i
  haveI : IsNoetherianRing Ach := isNoetherianRing_projChart hR g i
  letI := _root_.SemistableReduction.ProjScheme.projChartAlgebra (f := g) R₀ hR i
  let ϖa : Ach := algebraMap O' Ach ϖ
  have hϖa : (ϖa : L) ≠ 0 := by
    change algebraMap O' L ϖ ≠ 0
    rw [IsScalarTower.algebraMap_apply O' K' L]
    exact (map_ne_zero _).2 fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hspec : ∀ q : Spec (CommRingCat.of Ach),
      (_root_.SemistableReduction.ProjScheme.projModelCode O' hg).toSpec (ch q) =
        closedPoint O' ↔ ϖa ∈ q.asIdeal := by
    intro q
    rw [← Scheme.Hom.comp_apply, _root_.SemistableReduction.ProjScheme.chartι_toSpec R₀ hR hg i]
    constructor
    · intro h
      have hm : ϖ ∈ (closedPoint O').asIdeal := hϖ.not_isUnit
      have h' := congrArg PrimeSpectrum.asIdeal h
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal] at h'
      rw [← h'] at hm
      exact hm
    · intro h
      apply PrimeSpectrum.ext
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
      have hle : maximalIdeal O' ≤
          q.asIdeal.comap (CommRingCat.ofHom (algebraMap O' Ach)).hom := by
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ]
        exact (Ideal.span_singleton_le_iff_mem _).2 h
      exact ((maximalIdeal.isMaximal O').eq_of_le (Ideal.comap_isPrime _ _).ne_top hle).symm
  have hZ : ∀ y, E.inv y ∈ Z c ↔
      (_root_.SemistableReduction.ProjScheme.projModelCode O' hg).toSpec y = closedPoint O' := by
    intro y
    change c.toSpec (E.inv y) = _ ↔ _
    rw [← he₁, ← Scheme.Hom.comp_apply, ← Category.assoc, E.inv_hom_id, Category.id_comp]
  have hinv : E.inv (ch p) = ζ := by
    change E.inv (_root_.SemistableReduction.ProjScheme.chartι R₀ hR hg i p) = ζ
    rw [hp, ← Scheme.Hom.comp_apply, E.hom_inv_id]
    rfl
  have hζZ : ζ ∈ Z c := hv.2.1 (gp_mem hv)
  have hap : ϖa ∈ p.asIdeal := (hspec p).1 ((hZ _).1 (hinv ▸ hζZ))
  have hmin : p.asIdeal ∈ (Ideal.span {ϖa}).minimalPrimes := by
    refine ⟨⟨p.2, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q ⟨hq, hqa⟩ hqp ↦ ?_⟩
    let q' : Spec (CommRingCat.of Ach) := ⟨q, hq⟩
    have hsp : q' ⤳ p := (PrimeSpectrum.le_iff_specializes q' p).1 hqp
    have hmemZ : E.inv (ch q') ∈ Z c :=
      (hZ _).2 ((hspec q').2 ((Ideal.span_singleton_le_iff_mem _).1 hqa))
    have hz : E.inv (ch q') ⤳ ζ := by
      rw [← hinv]
      exact (hsp.map ch.continuous).map E.inv.continuous
    -- `E.inv (ch q')` is the generic point of `v`
    have hsub : v ⊆ closure {E.inv (ch q')} := by
      rw [← closure_gp hv]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hz))
        isClosed_closure
    have hcl := hv.2.2 _ isIrreducible_singleton.closure
      (closure_minimal (Set.singleton_subset_iff.2 hmemZ) (isClosed_Z c)) hsub
    have h1 : E.inv (ch q') = ζ := by
      have e1 : IsGenericPoint (E.inv (ch q')) v := by rw [IsGenericPoint, hcl]
      have e2 : IsGenericPoint ζ v := closure_gp hv
      exact e1.eq e2
    have h2 : ch q' = ch p := by
      have key : ∀ y, E.hom (E.inv y) = y := fun y ↦ by
        rw [← Scheme.Hom.comp_apply, E.inv_hom_id]; rfl
      have := congrArg E.hom (h1.trans hinv.symm)
      rwa [key, key] at this
    have h3 : q' = p := ch.isOpenEmbedding.injective h2
    exact (congrArg PrimeSpectrum.asIdeal h3).ge
  obtain ⟨hint, hfrac⟩ := localSubring_props O' a b hb g hpts i p.asIdeal
  have hvalL := LocalSubring.ofPrime_mem_or_inv_mem Ach p.asIdeal hϖa hmin hint hfrac
  have hmemS : ∀ y : L, y ∈ (LocalSubring.ofPrime Ach p.asIdeal).toSubring →
      ∃ a : Ach, ∃ s ∉ p.asIdeal, y * s = a := by
    intro y hy
    obtain ⟨⟨a', s'⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl
      (⟨y, hy⟩ : (LocalSubring.ofPrime Ach p.asIdeal).toSubring)
    exact ⟨a', s', s'.2, congrArg Subtype.val h⟩
  let f : CommRingCat.of Ach ⟶ CommRingCat.of L := CommRingCat.ofHom Ach.subtype
  have hval : ∀ y : L, (∃ a, ∃ s ∉ p.asIdeal, y * f s = f a) ∨
      (∃ a, ∃ s ∉ p.asIdeal, y⁻¹ * f s = f a) := by
    intro y
    rcases hvalL y with h | h
    · exact .inl (hmemS _ h)
    · exact .inr (hmemS _ h)
  have hgen : j ≫ E.hom = Spec.map f ≫ ch := by
    rw [he₂, _root_.SemistableReduction.ProjScheme.toImage_eq_SpecMap_comp_chartι R₀ hR hg i]
  refine CentreDetermines.of_comp E.hom ?_
  rw [hgen, ← hp]
  exact centreDetermines_of_openImmersion ch f p hval

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
