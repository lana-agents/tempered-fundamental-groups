/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTree
import TemperedFundamentalGroups.SemistableReduction.ChartLocalization

/-!
# The tree of projective lines is semistable

Blueprint §9.6 (W5), layer M7c. For a convex reduced nonempty finite family of Gauss valuations
`w_{a i, |c i|}` of `K(X)` over a valuation ring `O` of rank at most one with an element `ϖ` such
that all the thicknesses `c j / c m` (`D j ⊊ D m`) are powers of `ϖ` (e.g. a discrete valuation
ring with uniformizer `ϖ` and radii in `|ϖ|^ℤ`), every chart of `gaussJoinModel v a c` is
semistable in the sense of `LocalModel.lean` (`gaussJoinModel_isSemistable`): at every prime it is
étale-locally the affine line `O[X]` or a node `O[u, v] ⧸ (u v - ϖⁿ)`.

Proof: a prime of a chart is the center of a valuation subring `W` (Chevalley,
`exists_centerIdeal_eq`); the local ring there is that of a standard chart
(`gaussJoinModel_center_eq`), which is `O`-isomorphic to `O[X]` or to a node
(`polyChart_isSemistable`, `nodeChart_isSemistable`); charts of finite type with the same local
ring share a basic open neighbourhood, so semistability transfers
(`isSemistableAt_of_localAt_eq`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel GaussTree

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

lemma isGaussCoord_coord {a c : K} (hc : c ≠ 0) :
    IsGaussCoord v (gaussRat v a (Units.mk0 (v c) ((v.ne_zero_iff).2 hc)))
      (coord (RatFunc.X : RatFunc K) a c) := by
  rw [← gaussCoord_eq_coord hc]
  exact isGaussCoord_gaussCoord rfl

/-- Standard charts of a family with thicknesses powers of `ϖ` are semistable. -/
theorem IsStandardChart.isSemistable {ι : Type*} {a c : ι → K} (hc : ∀ i, c i ≠ 0)
    {ϖ : v.valuationSubring}
    (hthick : ∀ j m, DiscLE v a c j m → j ≠ m →
      ∃ n : ℕ, c j / c m = ((ϖ ^ n : v.valuationSubring) : K))
    {B : Subring (RatFunc K)} (hB : IsStandardChart v a c (RatFunc.X : RatFunc K) B)
    [Algebra v.valuationSubring B]
    (hcomp : ∀ o, ((algebraMap v.valuationSubring B o : B) : RatFunc K) =
      algebraMap v.valuationSubring (RatFunc K) o) :
    IsSemistable ϖ B := by
  rcases hB with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, m, hjm, hjne, rfl⟩
  · exact polyChart_isSemistable (isGaussCoord_coord (hc i)) hcomp
  · exact polyChart_isSemistable (isGaussCoord_coord (hc i)).inv hcomp
  · obtain ⟨n, hn⟩ := hthick j m hjm hjne
    exact nodeChart_isSemistable (isGaussCoord_coord (a := a j) (hc m)) hn
      (div_ne_zero (hc j) (hc m)) hcomp

/-- Standard charts contain the base ring. -/
lemma IsStandardChart.baseRing_le {ι : Type*} {a c : ι → K} {x : RatFunc K}
    {B : Subring (RatFunc K)} (hB : IsStandardChart v a c x B) :
    baseRing (RatFunc K) v.valuationSubring ≤ B := by
  rcases hB with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, m, -, -, rfl⟩
  · exact baseRing_le_polyChart _
  · exact baseRing_le_polyChart _
  · exact baseRing_le_nodeChart

/-- Standard charts are of finite type over the base. -/
lemma IsStandardChart.exists_finset {ι : Type*} {a c : ι → K} {x : RatFunc K}
    {B : Subring (RatFunc K)} (hB : IsStandardChart v a c x B) :
    ∃ s : Finset (RatFunc K),
      B = Subring.closure ((baseRing (RatFunc K) v.valuationSubring : Set (RatFunc K)) ∪ s) := by
  classical
  rcases hB with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, m, -, -, rfl⟩
  · exact ⟨{coord x (a i) (c i)}, by simp [polyChart]⟩
  · exact ⟨{(coord x (a i) (c i))⁻¹}, by simp [polyChart]⟩
  · exact ⟨{coord x (a j) (c m), algebraMap K (RatFunc K) (c j / c m) / coord x (a j) (c m)},
      by simp [nodeChart]⟩

/-- **(W5 (iii) + W8 base case) The tree of `ℙ¹`s is semistable.** For a convex reduced
nonempty finite family of Gauss valuations `w_{a i, |c i|}` of `K(X)` over a valuation ring `O` of
rank at most one, with all thicknesses `c j / c m` (`D j ⊊ D m`) powers of `ϖ ∈ O`, every chart
of the join model `gaussJoinModel v a c` (whose vertex set is the family), with any `O`-algebra
structure compatible with `K(X)`, is semistable. -/
theorem gaussJoinModel_isSemistable {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → K}
    (hc : ∀ i, c i ≠ 0) (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hrank : ∀ O' : ValuationSubring K, v.valuationSubring ≤ O' →
      O' = v.valuationSubring ∨ O' = ⊤)
    {ϖ : v.valuationSubring}
    (hthick : ∀ j m, DiscLE v a c j m → j ≠ m →
      ∃ n : ℕ, c j / c m = ((ϖ ^ n : v.valuationSubring) : K))
    {C : Subring (RatFunc K)} (hC : C ∈ (gaussJoinModel v a c).charts)
    [Algebra v.valuationSubring C]
    (hCc : ∀ o, ((algebraMap v.valuationSubring C o : C) : RatFunc K) =
      algebraMap v.valuationSubring (RatFunc K) o) :
    IsSemistable ϖ C := by
  intro 𝔭 _
  obtain ⟨W, hCW, hcen⟩ := exists_centerIdeal_eq C 𝔭
  have hRC : baseRing (RatFunc K) v.valuationSubring ≤ C := (gaussJoinModel v a c).le_chart C hC
  have hW : baseRing (RatFunc K) v.valuationSubring ≤ W.toSubring := hRC.trans hCW
  obtain ⟨B, hB, hBW, hcenter⟩ := gaussJoinModel_center_eq hc hconv hred hrank hW
  have hloc : localAt C W = localAt B W := by
    rw [← center_eq gaussJoinModel_isProper gaussJoinModel_isSeparated hW hC hCW, hcenter]
  have hRB : baseRing (RatFunc K) v.valuationSubring ≤ B := IsStandardChart.baseRing_le hB
  letI : Algebra v.valuationSubring B := chartAlgebra hRB
  have hBc : ∀ o, ((algebraMap v.valuationSubring B o : B) : RatFunc K) =
      algebraMap v.valuationSubring (RatFunc K) o := fun _ ↦ rfl
  obtain ⟨sB, hsB⟩ := IsStandardChart.exists_finset hB
  obtain ⟨sC, hsC⟩ := gaussJoinModel_isFiniteType C hC
  have hBs : IsSemistableAt ϖ (centerIdeal B W hBW) :=
    IsStandardChart.isSemistable hc hthick hB hBc _ inferInstance
  have := isSemistableAt_of_localAt_eq hBc hCc hRB hRC sB sC hsB hsC hBW hCW hloc hBs
  rwa [hcen] at this

end SemistableReduction
