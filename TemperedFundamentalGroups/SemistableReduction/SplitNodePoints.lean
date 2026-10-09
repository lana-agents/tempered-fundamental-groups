/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjNormalizationSplit
import TemperedFundamentalGroups.SemistableReduction.W10RouteSplitSpecial
import TemperedFundamentalGroups.SemistableReduction.SplitChart

/-!
# Node points of the component model lie over edges of the tree

Blueprint §10.3.8. `W10Route.exists_routedEdge_of_isNodePt`: let `g` be the coordinates of
`exists_component_model_split`, with its germ bridge `hbr`, and let every prime of every chart of
the normalized tree model be in `SplitClass` (G4′, `W10.TreeChartsSplit`). Then at every node point
`y` of `projModelCode O_E hg` (a point which is not étale-locally `O_E[X]`) the germs are the local
ring of a normalized edge chart `normChart F₀ S` of an edge of the tree (`RoutedEdge`) at a
valuation `W` centered over its node.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

open ZariskiModel ProjScheme

/-- `IsSplitNodePt` is `IsSplitNodeAt` (`SplitChart`) for some thickness. -/
theorem isSplitNodePt_iff {O : Type u} [CommRing O] {ϖ : O} {A : Type u} [CommRing A]
    [Algebra O A] {𝔭 : Ideal A} : IsSplitNodePt ϖ 𝔭 ↔ ∃ n, IsSplitNodeAt ϖ n 𝔭 :=
  Iff.rfl

namespace W10Route

variable {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] {F₀ : Type u} [Field F₀]
  [Algebra (RatFunc E) F₀] [Algebra E F₀] [IsScalarTower E (RatFunc E) F₀]
  [Algebra (NormedField.valuation (K := E)).valuationSubring F₀]
  [IsScalarTower (NormedField.valuation (K := E)).valuationSubring E F₀]
  {ι : Type*} [Fintype ι] {aE cE : ι → E} {ϖ : (NormedField.valuation (K := E)).valuationSubring}

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

set_option hygiene false in
local notation "O_E" => (NormedField.valuation (K := E)).valuationSubring

/-- **Node points lie over edges.** -/
theorem exists_routedEdge_of_isNodePt {n : ℕ} {g : Fin (n + 1) → F₀} (hg : ∀ l, g l ≠ 0)
    (hbr : ∀ y : (projModelCode O_E hg).scheme,
      ∃ B ∈ ((gaussJoinModel νE aE cE).normalization F₀).charts,
      ∃ (W : ValuationSubring F₀) (hBW : B ≤ W.toSubring),
        TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
            (projModelCode O_E hg) (genericPt O_E hg) y = (localAt B W : Set F₀) ∧
        ∀ [Algebra O_E B], (∀ o, ((algebraMap O_E B o : B) : F₀) = algebraMap O_E F₀ o) →
          IsEtaleLocallyAt O_E O_E[X] (centerIdeal B W hBW) →
          TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSmoothPt
            (projModelCode O_E hg) y)
    (hclass : ∀ Cc ∈ ((gaussJoinModel νE aE cE).normalization F₀).charts,
      ∀ [Algebra O_E Cc], (∀ o, ((algebraMap O_E Cc o : Cc) : F₀) = algebraMap O_E F₀ o) →
        ∀ 𝔭 : Ideal Cc, 𝔭.IsPrime → SplitClass aE cE ϖ Cc 𝔭)
    (y : (projModelCode O_E hg).scheme)
    (hy : TemperedFundamentalGroups.SemistableReduction.ModelCode.IsNodePt
      (projModelCode O_E hg) y) :
    ∃ (W : ValuationSubring F₀) (S : Subring (RatFunc E)),
      RoutedEdge νE aE cE (RatFunc.X : RatFunc E) (W.comap (algebraMap (RatFunc E) F₀)) S ∧
      normChart F₀ S ≤ W.toSubring ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
        (projModelCode O_E hg) (genericPt O_E hg) y = (localAt (normChart F₀ S) W : Set F₀) := by
  obtain ⟨B, hB, W, hBW, hgerm, hsm⟩ := hbr y
  letI : Algebra O_E B := chartAlgebra (((gaussJoinModel νE aE cE).normalization F₀).le_chart B hB)
  have hBc : ∀ o, ((algebraMap O_E B o : B) : F₀) = algebraMap O_E F₀ o := fun _ ↦ rfl
  rcases hclass B hB hBc (centerIdeal B W hBW) inferInstance with h | ⟨-, W', hBW', hcen, S, hE,
    hSW, hloc⟩
  · exact absurd (hsm hBc h) hy.2
  · refine ⟨W', S, hE, hSW, ?_⟩
    rw [hgerm, ← locAt_centerIdeal B W hBW, locAt_eq_localAt hcen, hloc]

end W10Route

end SemistableReduction
