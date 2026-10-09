/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteSplitSteps
import TemperedFundamentalGroups.SemistableReduction.W10RouteSpecial
import TemperedFundamentalGroups.SemistableReduction.ChartLocalizationSplit

/-!
# Routed charts over `E`, split form (G4′, part 3)

Blueprint §10.3.8 (split nodes). The split forms of `routedStep` and `chartsSemistable`
(`W10RouteSpecial`), with the classification of the points:

* `RoutedEdge`: the edge case of `Routed` (the center lies over the node of the edge chart
  `O[u, c'/u]`, `u = (x - a j)/c m`, `c' = c j / c m`, of an edge `(j, m)` of the tree);
* `SplitClass aE cE ϖ Cc 𝔭`: the chart `Cc` is étale-locally `O_E[X]` at `𝔭`, or has a split node
  there, and then `𝔭` is the center of a valuation `W` of `F₀` routed to an edge chart, with the
  same local ring as the normalized edge chart;
* `routedStepSplit`, `chartsSplit`: every prime of every chart of the normalized `E`-tree model is
  in `SplitClass`, given the smooth descent (smooth form) and the split node descent on the twists.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section Edge

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) {ι : Type*} (a c : ι → K) (x : F)
  (W : ValuationSubring F)

/-- The **edge case of `Routed`**: `B` is the edge chart `O[u, c'/u]` of an edge `(j, m)` of the
tree (`u = (x - a j)/c m`, `c' = c j / c m`), and the center of `W` lies over its node
(`u, c'/u ∈ 𝔪_W`). -/
def RoutedEdge (B : Subring F) : Prop :=
  ∃ j m, DiscLE v a c j m ∧ j ≠ m ∧
    (∀ k, DiscLE v a c j k → DiscLE v a c k m → k = j ∨ k = m) ∧
    B = nodeChart v (coord x (a j) (c m)) (c j / c m) ∧
    W.valuation (coord x (a j) (c m)) < 1 ∧
    W.valuation (algebraMap K F (c j / c m) / coord x (a j) (c m)) < 1

variable {v a c x W} in
lemma RoutedEdge.routed {B : Subring F} (h : RoutedEdge v a c x W B) : Routed v a c x W B :=
  Or.inr (Or.inl h)

end Edge

section Class

variable {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] {F₀ : Type u} [Field F₀]
  [Algebra (RatFunc E) F₀] {ι : Type*} (aE cE : ι → E)
  (ϖ : (NormedField.valuation (K := E)).valuationSubring)

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

set_option hygiene false in
local notation "O_E" => (NormedField.valuation (K := E)).valuationSubring

/-- **The classification of the points of a chart** of the normalized `E`-tree model: étale-locally
`O_E[X]`, or a split node which is the center of a valuation `W` routed to the normalized edge
chart `normChart F₀ S` of an edge, with the same local ring. -/
def SplitClass (Cc : Subring F₀) [Algebra O_E Cc] (𝔭 : Ideal Cc) : Prop :=
  IsEtaleLocallyAt O_E O_E[X] 𝔭 ∨
    (IsSplitNodePt ϖ 𝔭 ∧ ∃ (W : ValuationSubring F₀) (hCW : Cc ≤ W.toSubring),
      centerIdeal Cc W hCW = 𝔭 ∧ ∃ S : Subring (RatFunc E),
        RoutedEdge νE aE cE (RatFunc.X : RatFunc E) (W.comap (algebraMap (RatFunc E) F₀)) S ∧
        ∃ _ : normChart F₀ S ≤ W.toSubring, localAt Cc W = localAt (normChart F₀ S) W)

variable {aE cE ϖ} in
lemma SplitClass.isSplitSemistableAt {Cc : Subring F₀} [Algebra O_E Cc] {𝔭 : Ideal Cc}
    (h : SplitClass aE cE ϖ Cc 𝔭) : IsSplitSemistableAt ϖ 𝔭 :=
  h.imp id And.left

end Class

section Routed

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F' : Type u} [Field F'] [Algebra (RatFunc C) F']
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F₀ : Type u} [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀] [IsScalarTower E (RatFunc E) F₀]
  {χ : F₀ →+* F'} (hχ : DVRDescent.IsCompat φ χ)
  {ϖ : (NormedField.valuation (K := E)).valuationSubring}

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

set_option hygiene false in
local notation "O_E" => (NormedField.valuation (K := E)).valuationSubring

set_option hygiene false in
local notation "ψ" => algebraMap (RatFunc C) F'

variable {ι : Type*} {aE cE : ι → E}

include hφ hχ in
/-- **Routed charts over `E`, split form.** -/
theorem routedStepSplit [Finite ι] [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
    [IsDiscreteValuationRing O_E] (hϖ : Irreducible ϖ)
    (hcE : ∀ i, cE i ≠ 0) (hc : ∀ i, φ (cE i) ≠ 0) (hred : IsReduced νE aE cE)
    (hvert : ∀ m (β : C) (hβ : ‖β‖ ≤ 1),
      (∀ j, DiscLE νE aE cE j m → j ≠ m → ‖β - φ ((aE j - aE m) / cE m)‖ = 1) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F'))),
        P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1)
          (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F')))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff (aE m) (cE m) (hcE m) F₀)
        IsEtaleLocallyAt O_E O_E[X] (P'.comap (ιβ (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) hβ)))
    (hroot : ∀ ρ, (∀ i, DiscLE νE aE cE i ρ) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F')))), P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F'))))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E)
          (F₀ := Inv (1 : E) one_ne_zero (Aff (aE ρ) (cE ρ) (hcE ρ) F₀))
        IsEtaleLocallyAt O_E O_E[X] (P'.comap (ιβ (χInvAff χ (hcE ρ) (hc ρ)) hφ
          (isCompat_χInvAff (hcE ρ) (hc ρ) hχ rfl rfl) (by simp : ‖(0 : C)‖ ≤ 1))))
    (hedge : ∀ j m, DiscLE νE aE cE j m → j ≠ m →
      (∀ k, DiscLE νE aE cE j k → DiscLE νE aE cE k m → k = j ∨ k = m) →
      ∀ [Algebra O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀))],
      (∀ o, ((algebraMap O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) o :
        Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) : Aff (aE j) (cE m) (hcE m) F₀) =
          toAff (hcE m) (algebraMap E F₀ o)) →
      ∀ P' : Ideal (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F')),
        P'.IsMaximal →
        P'.comap (algebraMap (nodeRing (φ (cE j) / φ (cE m)))
          (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F'))) =
            tubeIdeal (φ (cE j) / φ (cE m)) →
        IsSplitNodePt ϖ (P'.comap (ιN (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) (map_div₀ φ (cE j) (cE m)))))
    (W' : ValuationSubring F') (hO : IsOverOC C W') {S : Subring (RatFunc E)}
    (hS : Routed νE aE cE (RatFunc.X : RatFunc E)
      ((W'.comap χ).comap (algebraMap (RatFunc E) F₀)) S)
    [Algebra O_E (normChart F₀ S)]
    (hBc : ∀ o, ((algebraMap O_E (normChart F₀ S) o : normChart F₀ S) : F₀) = algebraMap E F₀ o)
    (hSW : normChart F₀ S ≤ (W'.comap χ).toSubring) :
    IsEtaleLocallyAt O_E O_E[X] (centerIdeal _ (W'.comap χ) hSW) ∨
      (IsSplitNodePt ϖ (centerIdeal _ (W'.comap χ) hSW) ∧
        RoutedEdge νE aE cE (RatFunc.X : RatFunc E)
          ((W'.comap χ).comap (algebraMap (RatFunc E) F₀)) S) := by
  classical
  haveI := Fintype.ofFinite ι
  rcases hS with ⟨m, rfl, hm, hunit⟩ | ⟨j, m, hjm, hjne, hedg, rfl, hu, hcu⟩ | ⟨ρ, hρ, rfl, hρu⟩
  · -- a vertex chart
    set D : Finset C := (Finset.univ.filter fun j ↦ DiscLE νE aE cE j m ∧ j ≠ m).image
      fun j ↦ φ ((aE j - aE m) / cE m) with hDdef
    have hX : ψ (coord (RatFunc.X : RatFunc C) (φ (aE m)) (φ (cE m))) ∈ W' := by
      rw [← ratFuncMap_coord, ← mem_comap_iff' hχ]
      exact hm
    have hD : ∀ δ ∈ D, ‖δ‖ ≤ 1 ∧ W'.valuation (ψ (coord (RatFunc.X : RatFunc C) (φ (aE m))
        (φ (cE m))) - ψ (algebraMap C (RatFunc C) δ)) = 1 := by
      intro δ hδ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hδ
      obtain ⟨hjm, hjne⟩ := (Finset.mem_filter.1 hj).2
      refine ⟨?_, ?_⟩
      · rw [hφ, ← val_le_one_iff_norm]
        exact (hjm.div_le_one hcE).2
      · rw [← ratFuncMap_coord, ← ratFuncMap_algebraMap_C, ← map_sub, ← map_sub,
          ← val_comap_eq_one_iff hχ]
        exact hunit j hjm hjne
    exact .inl (vertexStepSplit hφ hχ (hcE m) (hc m) rfl rfl W' hO hX D hD
      (fun β hβ hfar ↦ hvert m β hβ fun j hjm hjne ↦ hfar _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hjm, hjne⟩))) hBc hSW)
  · -- an edge chart
    have hX : W'.valuation (ψ (coord (RatFunc.X : RatFunc C) (φ (aE j)) (φ (cE m)))) < 1 := by
      rw [← ratFuncMap_coord, ← val_comap_lt_one_iff hχ]
      exact hu
    have hcX : W'.valuation (ψ (algebraMap C (RatFunc C) (φ (cE j) / φ (cE m))) /
        ψ (coord (RatFunc.X : RatFunc C) (φ (aE j)) (φ (cE m)))) < 1 := by
      rw [← map_div₀ φ, ← ratFuncMap_algebraMap_C, ← ratFuncMap_coord, ← map_div₀, ← map_div₀,
        ← val_comap_lt_one_iff hχ]
      exact hcu
    have hc₀ : ‖φ (cE j) / φ (cE m)‖ < 1 := by
      rw [← map_div₀, hφ]
      exact norm_div_lt_one_of_edge hcE hred hjm hjne
    exact (edgeStepSplit hφ hχ hϖ (hcE m) (hc m) rfl rfl hc₀ (div_ne_zero (hc j) (hc m))
      (map_div₀ φ (cE j) (cE m)) W' hO hX hcX (hedge j m hjm hjne hedg) hBc hSW).imp_right
        fun h ↦ ⟨h, j, m, hjm, hjne, hedg, rfl, hu, hcu⟩
  · -- the chart at `∞` of the root
    have hX : W'.valuation (ψ (coord (RatFunc.X : RatFunc C) (φ (aE ρ)) (φ (cE ρ)))⁻¹) < 1 := by
      rw [← ratFuncMap_coord, ← map_inv₀, ← val_comap_lt_one_iff hχ]
      exact hρu
    exact .inl (rootStepSplit hφ hχ (hcE ρ) (hc ρ) rfl rfl W' hO hX (hroot ρ hρ) hBc hSW)

include hφ hχ in
/-- **The charts of the normalized `E`-tree model, split form**: every prime is in
`SplitClass`, given the smooth descent (smooth form) and the split node descent on the twists of
`F'`. -/
theorem chartsSplit [Fintype ι] [Nonempty ι] [IsAlgClosed C] [Algebra C F']
    [IsScalarTower C (RatFunc C) F'] [CompleteSpace E]
    (halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
    [IsDiscreteValuationRing O_E] (hϖ : Irreducible ϖ)
    [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀]
    [Algebra O_E F₀] [IsScalarTower O_E E F₀]
    (hcE : ∀ i, cE i ≠ 0) (hc : ∀ i, φ (cE i) ≠ 0) (hconv : IsConvex νE aE cE)
    (hred : IsReduced νE aE cE)
    (hvert : ∀ m (β : C) (hβ : ‖β‖ ≤ 1),
      (∀ j, DiscLE νE aE cE j m → j ≠ m → ‖β - φ ((aE j - aE m) / cE m)‖ = 1) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F'))),
        P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1)
          (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F')))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff (aE m) (cE m) (hcE m) F₀)
        IsEtaleLocallyAt O_E O_E[X] (P'.comap (ιβ (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) hβ)))
    (hroot : ∀ ρ, (∀ i, DiscLE νE aE cE i ρ) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F')))), P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F'))))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E)
          (F₀ := Inv (1 : E) one_ne_zero (Aff (aE ρ) (cE ρ) (hcE ρ) F₀))
        IsEtaleLocallyAt O_E O_E[X] (P'.comap (ιβ (χInvAff χ (hcE ρ) (hc ρ)) hφ
          (isCompat_χInvAff (hcE ρ) (hc ρ) hχ rfl rfl) (by simp : ‖(0 : C)‖ ≤ 1))))
    (hedge : ∀ j m, DiscLE νE aE cE j m → j ≠ m →
      (∀ k, DiscLE νE aE cE j k → DiscLE νE aE cE k m → k = j ∨ k = m) →
      ∀ [Algebra O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀))],
      (∀ o, ((algebraMap O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) o :
        Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) : Aff (aE j) (cE m) (hcE m) F₀) =
          toAff (hcE m) (algebraMap E F₀ o)) →
      ∀ P' : Ideal (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F')),
        P'.IsMaximal →
        P'.comap (algebraMap (nodeRing (φ (cE j) / φ (cE m)))
          (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F'))) =
            tubeIdeal (φ (cE j) / φ (cE m)) →
        IsSplitNodePt ϖ (P'.comap (ιN (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) (map_div₀ φ (cE j) (cE m)))))
    {Cc : Subring F₀} (hCc : Cc ∈ ((gaussJoinModel νE aE cE).normalization F₀).charts)
    [Algebra O_E Cc] (hCcc : ∀ o, ((algebraMap O_E Cc o : Cc) : F₀) = algebraMap O_E F₀ o) :
    ∀ 𝔭 : Ideal Cc, 𝔭.IsPrime → SplitClass aE cE ϖ Cc 𝔭 := by
  classical
  have hϖm : maximalIdeal O_E ≤ Ideal.span {ϖ} := hϖ.maximalIdeal_eq.le
  have hfin := gaussJoinModel_normalization_isFiniteType (F' := F₀) hcE hconv hred
    (eq_or_eq_top_of_le hϖ)
  have hproper := normalization_isProper (F' := F₀)
    (gaussJoinModel_isProper (v := νE) (a := aE) (c := cE))
  have hsep := normalization_isSeparated (F' := F₀)
    (gaussJoinModel_isSeparated (v := νE) (a := aE) (c := cE))
  -- the special fibre
  have hspecial : ∀ W : ValuationSubring F₀, W.comap (algebraMap E F₀) = O_E →
      ∀ B ∈ ((gaussJoinModel νE aE cE).normalization F₀).charts, ∀ [Algebra O_E B],
      (∀ o, ((algebraMap O_E B o : B) : F₀) = algebraMap O_E F₀ o) →
      ∀ hBW : B ≤ W.toSubring, IsEtaleLocallyAt O_E O_E[X] (centerIdeal B W hBW) ∨
        (IsSplitNodePt ϖ (centerIdeal B W hBW) ∧ ∃ S : Subring (RatFunc E),
          RoutedEdge νE aE cE (RatFunc.X : RatFunc E) (W.comap (algebraMap (RatFunc E) F₀)) S ∧
          ∃ _ : normChart F₀ S ≤ W.toSubring, localAt B W = localAt (normChart F₀ S) W) := by
    intro W hW B hB _ hBc hBW
    obtain ⟨W', rfl, hW'O⟩ := exists_lift hφ (χ_algebraMap_E hχ) halg W hW
    have hO : IsOverOC C W' := isOverOC_of_comap W' hW'O
    obtain ⟨S, hS, hSW, hloc⟩ := exists_routed_normChart hcE hconv hred hB hBW hW
    have hRS : baseRing F₀ O_E ≤ normChart F₀ S := by
      rw [← map_baseRing (F := RatFunc E)]
      exact (subring_map_mono (IsStandardChart.baseRing_le (Routed.isStandardChart hS)) _).trans
        (map_le_normChart S)
    letI : Algebra O_E (normChart F₀ S) := chartAlgebra hRS
    have hBcS : ∀ o, ((algebraMap O_E (normChart F₀ S) o : normChart F₀ S) : F₀) =
        algebraMap O_E F₀ o := fun _ ↦ rfl
    have h1 := routedStepSplit hφ hχ hϖ hcE hc hred hvert hroot hedge W' hO hS
      (fun o ↦ (hBcS o).trans (IsScalarTower.algebraMap_apply O_E E F₀ o)) hSW
    obtain ⟨sS, hsS⟩ := normChart_closure_of_isStandardChart (F' := F₀) hcE
      (Routed.isStandardChart hS)
    obtain ⟨sB, hsB⟩ := hfin B hB
    have hRB := ((gaussJoinModel νE aE cE).normalization F₀).le_chart B hB
    rcases h1 with h1 | ⟨h1, hE⟩
    · exact .inl (isEtaleLocallyAt_of_localAt_eq hBcS hBc hRS hRB sS sB hsS hsB hSW hBW hloc h1)
    · exact .inr ⟨isSplitNodePt_of_localAt_eq hϖm hBcS hBc hRS hRB sS sB hsS hsB hSW hBW hloc h1,
        S, hE, hSW, hloc⟩
  intro 𝔭 _
  obtain ⟨W, hCW, rfl⟩ := exists_centerIdeal_eq Cc 𝔭
  have hRC := ((gaussJoinModel νE aE cE).normalization F₀).le_chart Cc hCc
  have hOW : O_E ≤ W.comap (algebraMap E F₀) := baseRing_le_iff.1 (hRC.trans hCW)
  rcases eq_or_eq_top_of_le hϖ _ hOW with hW | hW
  · rcases hspecial W hW Cc hCc hCcc hCW with h | ⟨h, S, hE, hSW, hloc⟩
    · exact .inl h
    · exact .inr ⟨h, W, hCW, rfl, S, hE, hSW, hloc⟩
  -- the generic fibre
  have hWE : ∀ e : E, algebraMap E F₀ e ∈ W := fun e ↦ by
    have : e ∈ W.comap (algebraMap E F₀) := by rw [hW]; trivial
    exact this
  obtain ⟨W₂, hW₂W, hW₂⟩ := exists_le_special W hWE hϖ
  obtain ⟨B, hB, hBW₂⟩ := hproper W₂ (baseRing_le_iff.2 hW₂.ge)
  have hRB := ((gaussJoinModel νE aE cE).normalization F₀).le_chart B hB
  letI : Algebra O_E B := chartAlgebra hRB
  have hBc : ∀ o, ((algebraMap O_E B o : B) : F₀) = algebraMap O_E F₀ o := fun _ ↦ rfl
  have hBW : B ≤ W.toSubring := fun x hx ↦ hW₂W (hBW₂ hx)
  have h₂ : IsSplitSemistableAt ϖ (centerIdeal B W₂ hBW₂) := by
    rcases hspecial W₂ hW₂ B hB hBc hBW₂ with h | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  have hϖW : algebraMap O_E B ϖ ∉ centerIdeal B W hBW := by
    rw [mem_centerIdeal_iff, not_lt]
    have hc : ((algebraMap O_E B ϖ : B) : F₀) = algebraMap E F₀ (ϖ : E) := by
      rw [hBc, IsScalarTower.algebraMap_apply O_E E F₀]
      rfl
    rw [hc]
    have hϖ0 : (ϖ : E) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
    refine ((valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨?_, hWE _, ?_⟩).ge
    · exact (_root_.map_ne_zero _).2 hϖ0
    · rw [← map_inv₀]; exact hWE _
  have h3 : IsEtaleLocallyAt O_E O_E[X] (centerIdeal B W hBW) :=
    h₂.of_le_of_notMem hϖm (fun z hz ↦ by
      rw [mem_centerIdeal_iff] at hz ⊢
      exact val_lt_one_of_le hW₂W (hBW₂ z.2) hz) hϖW
  obtain ⟨sB, hsB⟩ := hfin B hB
  obtain ⟨sC, hsC⟩ := hfin Cc hCc
  exact .inl (isEtaleLocallyAt_of_localAt_eq hBc hCcc hRB hRC sB sC hsB hsC hBW hCW
    (hsep.localAt_eq hCc hB hCW hBW) h3)

end Routed

end W10Route

end SemistableReduction
