/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjChartGerms
import TemperedFundamentalGroups.SemistableReduction.CentreGerms
import TemperedFundamentalGroups.SemistableReduction.WModelGerm
import TemperedFundamentalGroups.SemistableReduction.XHarmonic

/-!
# The specialization on the Gauss tree lies in the germs (Blueprint §9.7, XL6)

Let `c` be the W-model of Gauss data `(a, b)` (`ModelCode.IsWModelOf`), `y` a point of `c` and
`V` a valuation subring of `L` dominating the germs at `y`. Then the specialization of
`V ∩ K'(x)` on the join model `gaussJoinModel O' a b` consists of germs at `y`
(`center_subset_germs`): the germs are the local ring `R[g / g i]_Q` of a projective chart
(`ProjScheme.germs_chartι`), hence a point of the normalization of the join model, so they contain
a chart `A` of the join model in which `V` has the specialization `localAt A V`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace SemistableReduction

/-- **Local rings of a subring of `P` at a valuation dominating `P` lie in `P`.** -/
lemma localAt_le_of_dominates {F : Type*} [Field F] {A P : Subring F} {V : ValuationSubring F}
    (hdom : ∀ f ∈ P, (∀ w ∈ P, f * w ≠ 1) → V.valuation f < 1) (hAP : A ≤ P) :
    localAt A V ≤ P := by
  intro f hf
  obtain ⟨s, hs, hsV, hfs⟩ := mem_localAt.1 hf
  by_cases h : ∀ w ∈ P, s * w ≠ 1
  · exact absurd hsV (hdom s (hAP hs) h).ne
  push Not at h
  obtain ⟨w, hw, hsw⟩ := h
  have : f = f * s * w := by rw [mul_assoc, hsw, mul_one]
  rw [this]
  exact mul_mem (hAP hfs) hw

/-- The same along a field extension. -/
lemma localAt_comap_le_of_dominates {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    {A : Subring F} {P : Subring F'} {V : ValuationSubring F'}
    (hdom : ∀ f ∈ P, (∀ w ∈ P, f * w ≠ 1) → V.valuation f < 1)
    (hAP : ∀ a ∈ A, algebraMap F F' a ∈ P) :
    ∀ f ∈ localAt A (V.comap (algebraMap F F')), algebraMap F F' f ∈ P := by
  intro f hf
  obtain ⟨s, hs, hsV, hfs⟩ := mem_localAt.1 hf
  rw [valuation_comap_eq_one_iff] at hsV
  by_cases h : ∀ w ∈ P, algebraMap F F' s * w ≠ 1
  · exact absurd hsV (hdom _ (hAP s hs) h).ne
  push Not at h
  obtain ⟨w, hw, hsw⟩ := h
  have : algebraMap F F' f = algebraMap F F' (f * s) * w := by
    rw [map_mul, mul_assoc, hsw, mul_one]
  rw [this]
  exact mul_mem (hAP _ hfs) hw

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction

variable {K' L : Type u} [Field K'] [Field L] [Algebra K' L] {O' : ValuationSubring K'}
  [Algebra O' L] [IsScalarTower O' K' L]

/-- **The specialization on the Gauss tree lies in the germs** (XL6). -/
theorem center_subset_germs {x : L} (hx : Transcendental K' x) {ι : Type} [Fintype ι]
    {a b : ι → K'} {c : TemperedFundamentalGroups.ModelCode O'}
    {j : Spec (CommRingCat.of L) ⟶ c.scheme} (hW : IsWModelOf O' L x hx a b c j)
    {y : c.scheme} {P : Subring L} (hP : (P : Set L) = germs c j y) {V : ValuationSubring L}
    (hdom : CentreGerms.Dominates V (germs c j y)) :
    letI := xLineAlgebra L hx
    ∃ hV : baseRing (RatFunc K') O'.valuation.valuationSubring ≤
        (V.comap (algebraMap (RatFunc K') L)).toSubring,
      ∀ f ∈ (gaussJoinModel O'.valuation a b).center gaussJoinModel_isProper _ hV,
        algebraMap (RatFunc K') L f ∈ P := by
  letI := xLineAlgebra L hx
  haveI : IsScalarTower K' (RatFunc K') L := IsScalarTower.of_algebraMap_eq fun k ↦ by
    change algebraMap K' L k = RatFunc.liftAlgHom _ _ (algebraMap K' (RatFunc K') k)
    rw [AlgHom.commutes]
  obtain ⟨-, -, n, g, hg, hpts, e, -, he₂⟩ := hW
  set R := baseRing L O'.valuation.valuationSubring
  have hR : (algebraMap O' L).range = R := range_algebraMap_eq_baseRing'
  obtain ⟨i, hi⟩ := ProjScheme.exists_mem_chartOpen hg (e.hom y)
  rw [← ProjScheme.opensRange_chartι R hR hg i] at hi
  obtain ⟨Q, hQ⟩ := hi
  have hgerms : germs c j y = (locAt (projChart R g i) Q.asIdeal : Set L) := by
    rw [← germs_iso e j y, he₂, ← hQ]
    exact ProjScheme.germs_chartι R hR hg i Q
  rw [← hP] at hdom
  have hdom' : ∀ f ∈ P, (∀ w ∈ P, f * w ≠ 1) → V.valuation f < 1 := hdom.2
  have hPV : ∀ f ∈ P, f ∈ V := fun f hf ↦ hdom.1 hf
  have hchart : projChart R g i ≤ P := fun f hf ↦ by
    rw [← SetLike.mem_coe, hP, hgerms]
    exact ⟨⟨f, hf⟩, 1, fun h ↦ Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hchV : projChart R g i ≤ V.toSubring := fun f hf ↦ hPV f (hchart hf)
  have hpt : localAt (projChart R g i) V ∈ (ZariskiModel.projModel R g).points :=
    ⟨_, ZariskiModel.mem_projModel_charts.2 ⟨i, rfl⟩, V, hchV, rfl⟩
  rw [hpts] at hpt
  obtain ⟨C, hC, W', hCW', hCeq⟩ := hpt
  obtain ⟨A, hA, rfl⟩ := ZariskiModel.mem_normalization_charts.1 hC
  have hAP : ∀ a ∈ A, algebraMap (RatFunc K') L a ∈ P := fun a ha ↦
    localAt_le_of_dominates hdom' hchart
      (hCeq ▸ le_localAt (map_le_normChart A ⟨a, ha, rfl⟩))
  have hAV : A ≤ (V.comap (algebraMap (RatFunc K') L)).toSubring := fun a ha ↦ hPV _ (hAP a ha)
  have hV : baseRing (RatFunc K') O'.valuation.valuationSubring ≤
      (V.comap (algebraMap (RatFunc K') L)).toSubring :=
    ((gaussJoinModel O'.valuation a b).le_chart A hA).trans hAV
  refine ⟨hV, ?_⟩
  rw [ZariskiModel.center_eq gaussJoinModel_isProper gaussJoinModel_isSeparated hV hA hAV]
  exact localAt_comap_le_of_dominates hdom' hAP

end TemperedFundamentalGroups.SemistableReduction.ModelCode
