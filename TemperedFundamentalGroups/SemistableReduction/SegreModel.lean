/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussModel
import TemperedFundamentalGroups.SemistableReduction.ProjModel

/-!
# Joins of lines are projective models (Segre families)

Blueprint §9.6 (W5), layer M9b (preparation of M9c). The join `lines v y` of the projective
lines with coordinates `y i ≠ 0` (charts `R ⊔ ⨆ i, O[y i ^ ±1]`) is the projective model of the
Segre family `segre y σ = ∏_{σ i} y i` (`σ : ι → Bool`): the chart at `σ` is `O[y i⁻¹ : σ i,
y i : ¬ σ i]` (`projChart_segre`), so `lines v y = projModel (segre y)` (`lines_eq_projModel`) and
in particular `gaussJoinModel v a c = projModel (segre (gaussCoord a c))`.
-/

namespace SemistableReduction

open ZariskiModel

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {F : Type*} [Field F] [Algebra K F] {ι : Type*} [Fintype ι]

/-- The **Segre family** of `y : ι → F`: the products `∏_{σ i} y i` for `σ : ι → Bool`. -/
def segre (y : ι → F) (σ : ι → Bool) : F :=
  ∏ i, if σ i then y i else 1

lemma segre_ne_zero {y : ι → F} (hy : ∀ i, y i ≠ 0) (σ : ι → Bool) : segre y σ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ ↦ by split_ifs <;> simp [hy i]

/-- The chart of the join of lines at the choice `σ` (`O[y i⁻¹]` for `σ i`, else `O[y i]`). -/
noncomputable def segreChart (v : Valuation K Γ₀) (y : ι → F) (σ : ι → Bool) : Subring F :=
  baseRing F v.valuationSubring ⊔
    ⨆ i, if σ i then polyChart v (y i)⁻¹ else polyChart v (y i)

omit [Fintype ι] in
lemma polyChart_le_segreChart (y : ι → F) (σ : ι → Bool) (i : ι) :
    (if σ i then polyChart v (y i)⁻¹ else polyChart v (y i)) ≤ segreChart v y σ :=
  le_sup_of_le_right (le_iSup (fun i ↦ if σ i then polyChart v (y i)⁻¹ else polyChart v (y i)) i)

lemma segre_div_segre (y : ι → F) (τ σ : ι → Bool) :
    segre y τ / segre y σ =
      ∏ i, (if τ i then y i else 1) / (if σ i then y i else 1) := by
  rw [segre, segre, Finset.prod_div_distrib]

/-- The chart of the Segre family at `σ` is the chart of the join of lines at `σ`. -/
theorem projChart_segre {y : ι → F} (hy : ∀ i, y i ≠ 0) (σ : ι → Bool) :
    projChart (baseRing F v.valuationSubring) (segre y) σ = segreChart v y σ := by
  classical
  apply le_antisymm
  · refine projChart_le le_sup_left fun τ ↦ ?_
    rw [segre_div_segre y]
    refine Subring.prod_mem _ fun i _ ↦ ?_
    have h := polyChart_le_segreChart (v := v) y σ i
    cases hτ : τ i <;> cases hσ : σ i <;>
      simp only [hσ, Bool.false_eq_true, ↓reduceIte] at h ⊢
    · simp
    · rw [one_div]
      exact h (Subring.subset_closure (Or.inr rfl))
    · rw [div_one]
      exact h (Subring.subset_closure (Or.inr rfl))
    · rw [div_self (hy i)]
      exact one_mem _
  · refine sup_le (base_le_projChart σ) (iSup_le fun i ↦ ?_)
    have key : (if σ i then (y i)⁻¹ else y i) =
        segre y (Function.update σ i (!σ i)) / segre y σ := by
      rw [segre_div_segre y, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        Finset.prod_eq_one (s := Finset.univ.erase i), mul_one]
      · cases hσ : σ i <;> simp
      · intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), div_self]
        split_ifs <;> simp [hy j]
    have hmem : (if σ i then (y i)⁻¹ else y i) ∈
        projChart (baseRing F v.valuationSubring) (segre y) σ := by
      rw [key]
      exact div_mem_projChart _ _
    cases hσ : σ i <;> simp only [hσ, Bool.false_eq_true, ↓reduceIte] at hmem ⊢ <;>
      exact Subring.closure_le.2 (Set.union_subset (base_le_projChart σ)
        (Set.singleton_subset_iff.2 hmem))

lemma ZariskiModel.ext_of_charts_eq {R : Subring F} {M N : ZariskiModel R}
    (h : M.charts = N.charts) :
    M = N := by
  cases M
  cases N
  cases h
  rfl

/-- **The join of lines is the projective model of the Segre family.** -/
theorem lines_eq_projModel [DecidableEq ι] {y : ι → F} (hy : ∀ i, y i ≠ 0) :
    lines v y = projModel (baseRing F v.valuationSubring) (segre y) := by
  classical
  refine ZariskiModel.ext_of_charts_eq (Finset.ext fun A ↦ ?_)
  rw [mem_projModel_charts, lines, mem_iJoin_charts]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i ↦ decide (c i = polyChart v (y i)⁻¹), ?_⟩
    rw [projChart_segre hy, segreChart]
    congr 1
    refine iSup_congr fun i ↦ ?_
    by_cases h' : c i = polyChart v (y i)⁻¹
    · simp [h']
    · rcases mem_line_charts.1 (hc i) with h | h
      · rw [h] at h' ⊢
        simp [h']
      · exact absurd h h'
  · rintro ⟨σ, rfl⟩
    refine ⟨fun i ↦ if σ i then polyChart v (y i)⁻¹ else polyChart v (y i), fun i ↦ ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact mem_line_charts.2 (.inr rfl)
      · exact mem_line_charts.2 (.inl rfl)
    · rw [projChart_segre hy]
      rfl

end SemistableReduction
