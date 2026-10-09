/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartLocalization
import TemperedFundamentalGroups.SemistableReduction.SplitNodeGen

/-!
# Split nodes transfer between charts with the same local ring

Blueprint §10.3.8 (split nodes). The split forms of `isEtaleLocallyAt_of_localAt_eq`
(`ChartLocalization`):

* `isSplitNodePt_awayChart`: a split node at the center of `W` on `B` stays one on `B[1/u]`
  (`u` a `W`-unit; the residue field is unchanged, `residue_of_isLocalization_away`);
* `isSplitNodePt_of_localAt_eq`, `isSplitSemistableAt_of_localAt_eq`: if the charts `B, C` (of
  finite type over the base) have the same local ring at the center of `W`, a split node (resp.
  split semistability) at the center on `B` gives one on `C`.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} [Algebra v.valuationSubring F]
  [IsScalarTower v.valuationSubring K F] {ϖ : v.valuationSubring}
  {W : ValuationSubring F} {B C : Subring F} [Algebra v.valuationSubring B]
  [Algebra v.valuationSubring C]

omit [Algebra K F] [IsScalarTower v.valuationSubring K F] in
/-- A split node at the center of `W` on `B` stays one on `B[1/u]`, `u` a `W`-unit. -/
theorem isSplitNodePt_awayChart (hϖ : maximalIdeal v.valuationSubring ≤ Ideal.span {ϖ})
    {D : Subring F} [Algebra v.valuationSubring D] {u : F} (hu : u ∈ B) (hu0 : u ≠ 0)
    (hD : D = awayChart B hu) (hBD : B ≤ D)
    (hBc : ∀ o, ((algebraMap v.valuationSubring B o : B) : F) = algebraMap v.valuationSubring F o)
    (hDc : ∀ o, ((algebraMap v.valuationSubring D o : D) : F) = algebraMap v.valuationSubring F o)
    (hBW : B ≤ W.toSubring) (hDW : D ≤ W.toSubring)
    (h : IsSplitNodePt ϖ (centerIdeal B W hBW)) : IsSplitNodePt ϖ (centerIdeal D W hDW) := by
  subst hD
  letI : Algebra B (awayChart B hu) := (Subring.inclusion hBD).toAlgebra
  haveI : IsScalarTower v.valuationSubring B (awayChart B hu) :=
    IsScalarTower.of_algebraMap_eq fun o ↦ Subtype.ext ((hDc o).trans (hBc o).symm)
  haveI : IsLocalization.Away (⟨u, hu⟩ : B) (awayChart B hu) := isLocalization_awayChart hu hu0
  have hcomap : (centerIdeal (awayChart B hu) W hDW).comap (algebraMap B (awayChart B hu)) =
      centerIdeal B W hBW := comap_centerIdeal hBD hDW
  have hres := residue_of_isLocalization_away hϖ (⟨u, hu⟩ : B) (centerIdeal (awayChart B hu) W hDW)
    (by rw [hcomap]; exact h.algebraMap_mem) (by rw [hcomap]; exact h.residue)
  have hetB : (Subring.inclusion hBD).Etale := etale_inclusion_awayChart hu hu0
  exact IsSplitNodePt.of_etale (chartIncl hBD hBc hDc) hetB _ hres h

/-- **Split nodes transfer between charts with the same local ring.** -/
theorem isSplitNodePt_of_localAt_eq (hϖ : maximalIdeal v.valuationSubring ≤ Ideal.span {ϖ})
    (hBc : ∀ o, ((algebraMap v.valuationSubring B o : B) : F) = algebraMap v.valuationSubring F o)
    (hCc : ∀ o, ((algebraMap v.valuationSubring C o : C) : F) = algebraMap v.valuationSubring F o)
    (hRB : baseRing F v.valuationSubring ≤ B) (hRC : baseRing F v.valuationSubring ≤ C)
    (sB sC : Finset F)
    (hB : B = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sB))
    (hC : C = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sC))
    (hBW : B ≤ W.toSubring) (hCW : C ≤ W.toSubring) (hloc : localAt C W = localAt B W)
    (h : IsSplitNodePt ϖ (centerIdeal B W hBW)) : IsSplitNodePt ϖ (centerIdeal C W hCW) := by
  obtain ⟨u, hu, u', hu', huW, hu'W, hD⟩ := exists_awayChart_eq hRB hRC sB sC hB hC hloc
  have hu0 : u ≠ 0 := by rintro rfl; simp at huW
  have hu'0 : u' ≠ 0 := by rintro rfl; simp at hu'W
  set D := awayChart C hu'
  have hDW : D ≤ W.toSubring := awayChart_le hu' hCW hu'W
  have hRD : baseRing F v.valuationSubring ≤ D := hRC.trans (le_awayChart hu')
  letI : Algebra v.valuationSubring D := ZariskiModel.chartAlgebra hRD
  have hDc : ∀ o, ((algebraMap v.valuationSubring D o : D) : F) =
      algebraMap v.valuationSubring F o := fun _ ↦ rfl
  have hBD : B ≤ D := hD ▸ le_awayChart hu
  have hCD : C ≤ D := le_awayChart hu'
  have hetC : (Subring.inclusion hCD).Etale := etale_inclusion_awayChart hu' hu'0
  have h₁ : IsSplitNodePt ϖ (centerIdeal D W hDW) :=
    isSplitNodePt_awayChart hϖ hu hu0 hD.symm hBD hBc hDc hBW hDW h
  exact IsSplitNodePt.of_etale_of_comap (chartIncl hCD hCc hDc) hetC h₁

/-- Split semistability at the center transfers between charts with the same local ring. -/
theorem isSplitSemistableAt_of_localAt_eq
    (hϖ : maximalIdeal v.valuationSubring ≤ Ideal.span {ϖ})
    (hBc : ∀ o, ((algebraMap v.valuationSubring B o : B) : F) = algebraMap v.valuationSubring F o)
    (hCc : ∀ o, ((algebraMap v.valuationSubring C o : C) : F) = algebraMap v.valuationSubring F o)
    (hRB : baseRing F v.valuationSubring ≤ B) (hRC : baseRing F v.valuationSubring ≤ C)
    (sB sC : Finset F)
    (hB : B = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sB))
    (hC : C = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sC))
    (hBW : B ≤ W.toSubring) (hCW : C ≤ W.toSubring) (hloc : localAt C W = localAt B W)
    (h : IsSplitSemistableAt ϖ (centerIdeal B W hBW)) :
    IsSplitSemistableAt ϖ (centerIdeal C W hCW) := by
  rcases h with h | h
  · exact .inl (isEtaleLocallyAt_of_localAt_eq hBc hCc hRB hRC sB sC hB hC hBW hCW hloc h)
  · exact .inr (isSplitNodePt_of_localAt_eq hϖ hBc hCc hRB hRC sB sC hB hC hBW hCW hloc h)

end SemistableReduction
