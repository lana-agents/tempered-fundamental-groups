/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTree
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization

/-!
# Gauss tree models only depend on the valuation subring

Blueprint §10.3.8 (StrongComponentA (a)). W10 works with the norm valuation `ν_E` of `E`, while
`ModelCode.IsUnfolded` is stated for `O'.valuation`, `O' = ν_E.valuationSubring`.

* `GaussTree.discLE_iff_of_isEquiv`, `isConvex_of_isEquiv`, `isReduced_of_isEquiv`: the
  combinatorics of discs only depends on the equivalence class of the valuation;
* `gaussJoinModel_charts_congr`: the charts of `gaussJoinModel v a c` only depend on
  `v.valuationSubring`; `ZariskiModel.points_eq_of_charts_eq`, `normalization_charts_eq`,
  `vertexSet_eq` transport points, normalizations and vertex sets.
-/

namespace SemistableReduction

section Equiv

variable {K : Type*} [Field K] {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ]
  [LinearOrderedCommGroupWithZero Γ'] {v : Valuation K Γ} {w : Valuation K Γ'}
  {ι : Type*} {a c : ι → K}

namespace GaussTree

lemma discLE_iff_of_isEquiv (h : v.IsEquiv w) (i j : ι) :
    DiscLE v a c i j ↔ DiscLE w a c i j :=
  and_congr (h (c i) (c j)) (h (a i - a j) (c j))

lemma isConvex_of_isEquiv (h : v.IsEquiv w) (hconv : IsConvex v a c) : IsConvex w a c := by
  intro i j
  obtain ⟨k, h1, h2, h3⟩ := hconv i j
  refine ⟨k, (discLE_iff_of_isEquiv h i k).1 h1, (discLE_iff_of_isEquiv h j k).1 h2, ?_⟩
  rcases le_max_iff.1 h3 with h3 | h3
  · rcases le_max_iff.1 h3 with h3 | h3
    · exact le_max_of_le_left (le_max_of_le_left ((h _ _).1 h3))
    · exact le_max_of_le_left (le_max_of_le_right ((h _ _).1 h3))
  · exact le_max_of_le_right ((h _ _).1 h3)

lemma isReduced_of_isEquiv (h : v.IsEquiv w) (hred : IsReduced v a c) : IsReduced w a c :=
  fun i j hij hji =>
    hred i j ((discLE_iff_of_isEquiv h i j).2 hij) ((discLE_iff_of_isEquiv h j i).2 hji)

end GaussTree

end Equiv

namespace ZariskiModel

variable {F : Type*} [Field F]

lemma points_eq_of_charts_eq {R R' : Subring F} (M : ZariskiModel R) (M' : ZariskiModel R')
    (h : (M.charts : Set (Subring F)) = M'.charts) : M.points = M'.points := by
  ext B
  simp only [points, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, rest⟩
    exact ⟨A, by rw [← Finset.mem_coe, ← h]; exact hA, rest⟩
  · rintro ⟨A, hA, rest⟩
    exact ⟨A, by rw [← Finset.mem_coe, h]; exact hA, rest⟩

variable {K F' : Type*} [Field K] [Algebra K F] [Field F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F']

lemma normalization_charts_eq {O O' : ValuationSubring K} (M : ZariskiModel (baseRing F O))
    (M' : ZariskiModel (baseRing F O')) (h : (M.charts : Set (Subring F)) = M'.charts) :
    ((M.normalization F').charts : Set (Subring F')) = (M'.normalization F').charts := by
  ext C
  simp only [Finset.mem_coe, mem_normalization_charts]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, by rw [← Finset.mem_coe, ← h]; exact hA, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, by rw [← Finset.mem_coe, h]; exact hA, rfl⟩

lemma vertexSet_eq {O O' : ValuationSubring K} (M : ZariskiModel (baseRing F O))
    (M' : ZariskiModel (baseRing F O')) (hO : O = O') (h : M.points = M'.points) :
    M.vertexSet = M'.vertexSet := by
  subst hO
  ext W
  simp only [vertexSet, Set.mem_setOf_eq, h]

end ZariskiModel

section Join

variable {K : Type*} [Field K] {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ]
  [LinearOrderedCommGroupWithZero Γ'] {ι : Type*} [Fintype ι]

lemma gaussJoinModel_charts_congr {v : Valuation K Γ} {w : Valuation K Γ'}
    (h : v.valuationSubring = w.valuationSubring) (a c : ι → K) :
    ((gaussJoinModel v a c).charts : Set (Subring (RatFunc K))) =
      (gaussJoinModel w a c).charts := by
  ext A
  simp only [Finset.mem_coe, gaussJoinModel, ZariskiModel.lines,
    ZariskiModel.mem_iJoin_charts, ZariskiModel.mem_line_charts, polyChart, h]

end Join

end SemistableReduction
