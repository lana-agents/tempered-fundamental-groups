/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjNormalizationSplit

/-!
# Split nodes and germs of projective models with given points

Blueprint §10.3.8. The scheme-level outputs of `exists_component_model_split` (split nodes and
the germ bridge) hold for **any** homogeneous coordinates `g` whose projective model has the points
of a model `M` of finite type (`hpts`), not only for the coordinates constructed there:

* `exists_localAt_eq_of_mem_points`: a local ring `localAt A W` which is a point of `N` is the
  local ring of a chart of `N` at the same `W`;
* `projModelCode_split_of_points`: if the charts of `M` are split semistable at every prime, the
  model code `projModelCode O hg` has split nodes; and the germs at every point `y` are the local
  ring `localAt B W` of a chart `B` of `M` at a valuation `W ⊇ B`, such that `y` is smooth if
  `B` is étale-locally `O[X]` at the center of `W`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

namespace SemistableReduction

open ZariskiModel ProjScheme

section Points

variable {F : Type*} [Field F]

/-- For `x ∈ localAt C V`: `x⁻¹ ∈ localAt C V` iff `x` is a `V`-unit. -/
lemma inv_mem_localAt_iff {C : Subring F} {V : ValuationSubring F} (hCV : C ≤ V.toSubring)
    {x : F} (hx : x ∈ localAt C V) (hx0 : x ≠ 0) : x⁻¹ ∈ localAt C V ↔ V.valuation x = 1 := by
  constructor
  · intro h
    exact (valuation_eq_one_iff_mem_and_inv_mem V).2 ⟨hx0, localAt_le hCV hx, localAt_le hCV h⟩
  · intro h
    obtain ⟨s, hs, hsV, hxs⟩ := hx
    refine ⟨x * s, hxs, by rw [map_mul, h, hsV, one_mul], ?_⟩
    rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
    exact hs

/-- A local ring `localAt A W` which is a point of `N` is the local ring of a chart of `N` at the
same `W`. -/
theorem exists_localAt_eq_of_mem_points {R : Subring F} {N : ZariskiModel R} {A : Subring F}
    {W : ValuationSubring F} (hAW : A ≤ W.toSubring) (h : localAt A W ∈ N.points) :
    ∃ B ∈ N.charts, B ≤ W.toSubring ∧ localAt B W = localAt A W := by
  obtain ⟨B, hB, W', hBW', hloc⟩ := h
  have hBP : B ≤ localAt A W := hloc ▸ le_localAt
  have hBW : B ≤ W.toSubring := hBP.trans (localAt_le hAW)
  have hcen : centerIdeal B W' hBW' = centerIdeal B W hBW := by
    ext z
    rw [mem_centerIdeal_iff, mem_centerIdeal_iff]
    by_cases hz : (z : F) = 0
    · simp [hz]
    have e₁ := inv_mem_localAt_iff hBW' (le_localAt z.2) hz
    have e₂ := inv_mem_localAt_iff hAW (hBP z.2) hz
    rw [← hloc] at e₂
    have h₁ : W'.valuation (z : F) ≤ 1 := (W'.valuation_le_one_iff _).2 (hBW' z.2)
    have h₂ : W.valuation (z : F) ≤ 1 := (W.valuation_le_one_iff _).2 (hBW z.2)
    have e : W'.valuation (z : F) = 1 ↔ W.valuation (z : F) = 1 := e₁.symm.trans e₂
    rw [lt_iff_le_and_ne, lt_iff_le_and_ne, ne_eq, ne_eq, e]
    simp [h₁, h₂]
  refine ⟨B, hB, hBW, ?_⟩
  rw [← locAt_centerIdeal B W hBW, locAt_eq_localAt hcen, hloc]

end Points

section Proj

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {F' : Type u} [Field F'] [Algebra K F'] [Algebra v.valuationSubring F']
  [IsScalarTower v.valuationSubring K F']

/-- **Split nodes and germs for any coordinates with the points of `M`.** -/
theorem projModelCode_split_of_points {n : ℕ} {g : Fin (n + 1) → F'} (hg : ∀ l, g l ≠ 0)
    (M : ZariskiModel (baseRing F' v.valuationSubring)) (hfin : M.IsFiniteType)
    (hpts : (projModel (algebraMap v.valuationSubring F').range g).points = M.points) :
    (∀ ϖ : v.valuationSubring, maximalIdeal v.valuationSubring ≤ Ideal.span {ϖ} →
      (∀ C ∈ M.charts, ∀ [Algebra v.valuationSubring C],
        (∀ o, ((algebraMap v.valuationSubring C o : C) : F') = algebraMap v.valuationSubring F' o) →
          ∀ 𝔭 : Ideal C, 𝔭.IsPrime → IsSplitSemistableAt ϖ 𝔭) →
      TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ
        (projModelCode v.valuationSubring hg)) ∧
    ∀ y : (projModelCode v.valuationSubring hg).scheme,
      ∃ B ∈ M.charts, ∃ (W : ValuationSubring F') (hBW : B ≤ W.toSubring),
        TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
            (projModelCode v.valuationSubring hg) (genericPt v.valuationSubring hg) y =
          (localAt B W : Set F') ∧
        ∀ [Algebra v.valuationSubring B], (∀ o, ((algebraMap v.valuationSubring B o : B) : F') =
          algebraMap v.valuationSubring F' o) →
          IsEtaleLocallyAt v.valuationSubring v.valuationSubring[X] (centerIdeal B W hBW) →
          TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSmoothPt
            (projModelCode v.valuationSubring hg) y := by
  have hR' : (algebraMap v.valuationSubring F').range = baseRing F' v.valuationSubring := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      rw [IsScalarTower.algebraMap_apply v.valuationSubring K F']
      exact ⟨o, o.2, rfl⟩
    · rintro ⟨o, ho, rfl⟩
      refine ⟨⟨o, ho⟩, ?_⟩
      rw [IsScalarTower.algebraMap_apply v.valuationSubring K F']
      rfl
  rw [hR'] at hpts
  -- the local ring of a chart of `projModel g` at `W` is that of a chart of `M`
  have hloc : ∀ (l : Fin (n + 1)) (W : ValuationSubring F')
      (hCW : projChart (baseRing F' v.valuationSubring) g l ≤ W.toSubring),
      ∃ B ∈ M.charts, B ≤ W.toSubring ∧
        localAt B W = localAt (projChart (baseRing F' v.valuationSubring) g l) W := by
    intro l W hCW
    refine exists_localAt_eq_of_mem_points hCW ?_
    rw [← hpts]
    exact ⟨_, mem_projModel_charts.2 ⟨l, rfl⟩, W, hCW, rfl⟩
  refine ⟨fun ϖ hϖ hsp ↦ ?_, fun y ↦ ?_⟩
  · refine projModelCode_hasSplitNodes _ hR' hg ϖ fun l ↦ ?_
    letI := projChartAlgebra (f := g) (baseRing F' v.valuationSubring) hR' l
    intro 𝔭 _
    obtain ⟨W, hCW, rfl⟩ := exists_centerIdeal_eq _ 𝔭
    obtain ⟨B, hB, hBW, he⟩ := hloc l W hCW
    have hRB := M.le_chart B hB
    letI : Algebra v.valuationSubring B := chartAlgebra hRB
    obtain ⟨sB, hsB⟩ := hfin B hB
    obtain ⟨sC, hsC⟩ := projModel_isFiniteType (R := baseRing F' v.valuationSubring) (f := g) _
      (mem_projModel_charts.2 ⟨l, rfl⟩)
    exact isSplitSemistableAt_of_localAt_eq hϖ (fun _ ↦ rfl) (fun _ ↦ rfl) hRB
      (base_le_projChart l) sB sC hsB hsC hBW hCW he.symm (hsp B hB (fun _ ↦ rfl) _ inferInstance)
  · obtain ⟨i, hi⟩ := exists_mem_chartOpen (O := v.valuationSubring) hg y
    rw [← opensRange_chartι (baseRing F' v.valuationSubring) hR' hg i] at hi
    obtain ⟨Q, rfl⟩ := hi
    obtain ⟨W, hCW, hcen⟩ := exists_centerIdeal_eq (projChart (baseRing F' v.valuationSubring) g i)
      Q.asIdeal
    obtain ⟨B, hB, hBW, he⟩ := hloc i W hCW
    refine ⟨B, hB, W, hBW, ?_, ?_⟩
    · rw [germs_chartι (baseRing F' v.valuationSubring) hR' hg i Q, locAt_eq_localAt hcen, he]
    · intro _ hBc hsm
      letI := projChartAlgebra (f := g) (baseRing F' v.valuationSubring) hR' i
      obtain ⟨sB, hsB⟩ := hfin B hB
      obtain ⟨sC, hsC⟩ := projModel_isFiniteType (R := baseRing F' v.valuationSubring) (f := g) _
        (mem_projModel_charts.2 ⟨i, rfl⟩)
      have h1 := isEtaleLocallyAt_of_localAt_eq hBc (fun _ ↦ rfl) (M.le_chart B hB)
        (base_le_projChart i) sB sC hsB hsC hBW hCW he.symm hsm
      rw [hcen] at h1
      letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
        (projModelCode v.valuationSubring hg) (chartOpen v.valuationSubring hg i)
      have hU := isAffineOpen_chartOpen (O := v.valuationSubring) hg i
      have hy : chartι (baseRing F' v.valuationSubring) hR' hg i Q ∈
          chartOpen v.valuationSubring hg i := by
        rw [← opensRange_chartι (baseRing F' v.valuationSubring) hR' hg i]; exact ⟨Q, rfl⟩
      refine ⟨chartOpen v.valuationSubring hg i, hU, hy, ?_⟩
      let e := chartEquiv (baseRing F' v.valuationSubring) hR' hg i
      have hprime : hU.primeIdealOf ⟨_, hy⟩ = Spec.map e.toRingEquiv.toCommRingCatIso.hom Q := by
        apply hU.fromSpec.isOpenEmbedding.injective
        rw [IsAffineOpen.fromSpec_primeIdealOf]
        change chartι (baseRing F' v.valuationSubring) hR' hg i Q = _
        rw [chartι, Scheme.Hom.comp_apply]
      have h2 := IsEtaleLocallyAt.of_etale_of_comap e.toAlgHom
        (RingHom.Etale.of_bijective e.bijective) h1
      convert h2 using 1
      rw [hprime]
      ext b
      rw [Spec.map_apply]
      rfl

end Proj

end SemistableReduction
