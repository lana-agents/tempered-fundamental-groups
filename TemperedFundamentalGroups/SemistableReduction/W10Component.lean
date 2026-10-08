/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Root
import TemperedFundamentalGroups.SemistableReduction.GaussTreeFinite
import TemperedFundamentalGroups.SemistableReduction.ProjNormalizationCode
import TemperedFundamentalGroups.SemistableReduction.GaussDescent

/-!
# The semistable model of one component

Blueprint §9.7a, step 4. For a convex reduced Gauss tree over a discretely valued `E` and a
finite separable `F₀ / E(X)` whose normalized tree model has semistable charts,
`exists_component_model` gives homogeneous coordinates `g` with

* `projModel g` having the points of the normalized tree model;
* `projModelCode g` semistable;
* the root chart locally dominating (into any `D ⊆ F₀` containing what is integral over `E[X]`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel ProjScheme

variable {E : Type u} [Field E] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation E Γ₀} [IsDiscreteValuationRing v.valuationSubring]
  {F₀ : Type u} [Field F₀] [Algebra E F₀] [Algebra (RatFunc E) F₀]
  [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀] [Algebra v.valuationSubring F₀]
  [IsScalarTower v.valuationSubring E F₀] [Algebra E[X] F₀] [IsScalarTower E[X] (RatFunc E) F₀]
  {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → E}

theorem exists_component_model (hc : ∀ i, c i ≠ 0) (hconv : GaussTree.IsConvex v a c)
    (hred : GaussTree.IsReduced v a c) (ϖ : v.valuationSubring)
    (hcharts : ∀ Cc ∈ ((gaussJoinModel v a c).normalization F₀).charts,
      ∀ [Algebra v.valuationSubring Cc], (∀ o, ((algebraMap v.valuationSubring Cc o : Cc) : F₀) =
        algebraMap v.valuationSubring F₀ o) → IsSemistable ϖ Cc)
    (D : Subring F₀) (hD : ∀ z : F₀, IsIntegral E[X] z → z ∈ D)
    (hRD : (algebraMap v.valuationSubring F₀).range ≤ D) :
    ∃ (n : ℕ) (g : Fin (n + 1) → F₀) (hg : ∀ l, g l ≠ 0),
      (projModel (algebraMap v.valuationSubring F₀).range g).points =
        ((gaussJoinModel v a c).normalization F₀).points ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ
        (projModelCode v.valuationSubring hg) ∧
      LocallyDominates (algebraMap v.valuationSubring F₀).range (RingHom.id F₀) D.subtype g := by
  classical
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
  have hfin := gaussJoinModel_normalization_isFiniteType (F' := F₀) hc hconv hred
    (eq_or_eq_top_of_le hϖ₀)
  have hcz : ∀ i, gaussCoord (a i) (c i) ≠ 0 := fun i ↦ gaussCoord_ne_zero (hc i)
  rw [gaussJoinModel_eq_projModel (v := v) hc] at hfin hcharts ⊢
  obtain ⟨n, g, hg, hch, hpts, hss⟩ := exists_projModelCode_normalization
    (F := RatFunc E) (f := segre fun i ↦ gaussCoord (a i) (c i)) (segre_ne_zero hcz) hfin
  have hR := range_algebraMap_eq_baseRing (v := v) (F' := F₀)
  refine ⟨n, g, hg, ?_, hss ϖ hcharts, ?_⟩
  · rw [hR]; exact hpts
  · -- the root chart: the normalization of the Segre chart at `σ = false`
    set A := projChart (baseRing (RatFunc E) v.valuationSubring)
      (segre fun i ↦ gaussCoord (a i) (c i)) (fun _ ↦ false) with hAdef
    have hAeq : A = segreChart v (fun i ↦ gaussCoord (a i) (c i)) (fun _ ↦ false) :=
      projChart_segre hcz _
    have hA : normChart F₀ A ∈
        ((projModel (baseRing (RatFunc E) v.valuationSubring)
          (segre fun i ↦ gaussCoord (a i) (c i))).normalization F₀).charts :=
      mem_normalization_charts.2 ⟨A, mem_projModel_charts.2 ⟨_, rfl⟩, rfl⟩
    obtain ⟨l, hl⟩ := mem_projModel_charts.1 (hch hA)
    refine locallyDominates_root D hD hRD (A := A) (fun t ht ↦ ?_) (l := l) ?_
    · rw [hAeq] at ht
      exact mem_range_of_mem_segreChart (fun i ↦ ⟨gaussLin (a i) (c i), rfl⟩) ht
    · rw [hR]; exact hl

end SemistableReduction
