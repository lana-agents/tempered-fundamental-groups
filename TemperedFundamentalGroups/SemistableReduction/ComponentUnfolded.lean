/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10WModel
import TemperedFundamentalGroups.SemistableReduction.EdgeNodeClause
import TemperedFundamentalGroups.SemistableReduction.GaussCoordShift
import TemperedFundamentalGroups.SemistableReduction.GaussDescent

/-!
# The W10 component models are unfolded and have no loops (StrongComponentA (a))

`noLoops_isUnfolded_projModelCode`: let `projModelCode O' g` have the points of the normalization
in `L` of a convex reduced Gauss tree model `(a, b)` (for a valuation `v` with valuation subring
`O'`) and be semistable. Suppose that at every node point the germs are the normalized edge chart
of an edge `(j, m)` of the tree, localized at a valuation `W` centred on its node (the edge case of
the classification of the points, G4′). Then the model has no loops and is unfolded on the x-line
`X` (`ModelCode.IsUnfolded`): the node clause comes from the branch valuations over the two Gauss
vertices of the edge (`CrossingSource.edgeNode`).
-/

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace TemperedFundamentalGroups.SemistableReduction

open _root_.SemistableReduction _root_.SemistableReduction.ProjScheme
  _root_.SemistableReduction.ZariskiModel _root_.SemistableReduction.GaussTree

variable {E : Type u} [Field E] (O' : ValuationSubring E) [IsDiscreteValuationRing O']
  {L : Type u} [Field L] [Algebra E L]

local notation "⟪" k "⟫" => algebraMap E (RatFunc E) k

/-- **The W10 component models have no loops and are unfolded**, given the edge form of the node
points. -/
theorem noLoops_isUnfolded_projModelCode [inst : Algebra (RatFunc E) L]
    [IsScalarTower E (RatFunc E) L] [FiniteDimensional (RatFunc E) L] [Algebra O' L]
    [IsScalarTower O' E L] (hx : Transcendental E (algebraMap (RatFunc E) L RatFunc.X))
    {ι : Type} [Fintype ι] [Nonempty ι] (a b : ι → E) (hb : ∀ i, b i ≠ 0) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation E Γ) (hv : v.valuationSubring = O')
    (hconv : IsConvex v a b) (hred : IsReduced v a b) {n : ℕ} {g : Fin (n + 1) → L}
    (hg : ∀ i, g i ≠ 0)
    (hpts : (ZariskiModel.projModel (algebraMap O' L).range g).points =
      ((gaussJoinModel v a b).normalization L).points)
    {ϖ' : O'} (hϖ' : Irreducible ϖ') (hss : ModelCode.IsSemistable ϖ' (projModelCode O' hg))
    (hnode : ∀ y : (projModelCode O' hg).scheme, ModelCode.IsNodePt (projModelCode O' hg) y →
      ∃ (W : ValuationSubring L) (jj m : ι), DiscLE v a b jj m ∧
        normChart L (nodeChart v (coord (RatFunc.X : RatFunc E) (a jj) (b m)) (b jj / b m)) ≤
          W.toSubring ∧
        W.valuation (algebraMap (RatFunc E) L (coord (RatFunc.X : RatFunc E) (a jj) (b m))) < 1 ∧
        W.valuation (algebraMap (RatFunc E) L
          (⟪b jj / b m⟫ / coord (RatFunc.X : RatFunc E) (a jj) (b m))) < 1 ∧
        ModelCode.germs (projModelCode O' hg) (genericPt O' hg) y =
          (localAt (normChart L (nodeChart v (coord (RatFunc.X : RatFunc E) (a jj) (b m))
            (b jj / b m))) W : Set L)) :
    ModelCode.NoLoops (projModelCode O' hg) ∧
      ModelCode.IsUnfolded O' (algebraMap (RatFunc E) L RatFunc.X) (projModelCode O' hg)
        (genericPt O' hg) := by
  have hWM := isWModelOf_projModelCode O' hx a b hb v hv hg hpts
  have hW : ModelCode.IsWModel O' L (algebraMap (RatFunc E) L RatFunc.X) (projModelCode O' hg)
      (genericPt O' hg) := ⟨hx, ι, inferInstance, inferInstance, a, b, hWM⟩
  have hvO : v.valuationSubring = O'.valuation.valuationSubring := by
    rw [hv, ValuationSubring.valuationSubring_valuation]
  have hequiv : v.IsEquiv O'.valuation := (Valuation.isEquiv_iff_valuationSubring _ _).2 hvO
  haveI : IsDiscreteValuationRing v.valuationSubring := by rw [hv]; infer_instance
  obtain ⟨ϖv, hϖv⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
  -- the base of a node valuation
  have hbase : ∀ (W : ValuationSubring L) (jj m : ι),
      normChart L (nodeChart v (coord (RatFunc.X : RatFunc E) (a jj) (b m)) (b jj / b m)) ≤
        W.toSubring →
      W.valuation (algebraMap (RatFunc E) L (coord (RatFunc.X : RatFunc E) (a jj) (b m))) < 1 →
      W.valuation (algebraMap (RatFunc E) L
        (⟪b jj / b m⟫ / coord (RatFunc.X : RatFunc E) (a jj) (b m))) < 1 →
      (W.comap (algebraMap (RatFunc E) L)).comap (algebraMap E (RatFunc E)) =
        v.valuationSubring := by
    intro W jj m hTW hy hcy
    have hle : v.valuationSubring ≤
        (W.comap (algebraMap (RatFunc E) L)).comap (algebraMap E (RatFunc E)) := by
      intro o ho
      exact hTW (map_le_normChart _ ⟨⟪o⟫, baseRing_le_nodeChart ⟨o, ho, rfl⟩, rfl⟩)
    rcases eq_or_eq_top_of_le hϖv _ hle with h | h
    · exact h
    · exfalso
      set y := coord (RatFunc.X : RatFunc E) (a jj) (b m)
      have hy0 : y ≠ 0 := (isGaussCoord_coord (v := v) (a := a jj) (hb m)).ne_zero
      have hWc : W.valuation (algebraMap (RatFunc E) L ⟪b jj / b m⟫) < 1 := by
        have e : ⟪b jj / b m⟫ = y * (⟪b jj / b m⟫ / y) := by field_simp
        rw [e, map_mul, map_mul]
        exact mul_lt_one_of_lt_of_le hy hcy.le
      have hmem : (b jj / b m)⁻¹ ∈
          (W.comap (algebraMap (RatFunc E) L)).comap (algebraMap E (RatFunc E)) := by
        rw [h]; trivial
      have h1 := (W.valuation_le_one_iff _).2 hmem
      change W.valuation (algebraMap (RatFunc E) L ⟪(b jj / b m)⁻¹⟫) ≤ 1 at h1
      rw [map_inv₀, map_inv₀, map_inv₀] at h1
      have h0 : W.valuation (algebraMap (RatFunc E) L ⟪b jj / b m⟫) ≠ 0 := by
        simp [hb jj, hb m]
      exact absurd h1 (not_le.2 ((one_lt_inv₀ (pos_iff_ne_zero.2 h0)).2 hWc))
  -- vertices of the join model
  have hvert : ∀ i,
      (gaussRat v (a i) (Units.mk0 (v (b i)) ((v.ne_zero_iff).2 (hb i)))).valuationSubring ∈
        (gaussJoinModel O'.valuation a b).vertexSet := by
    intro i
    rw [← ZariskiModel.vertexSet_eq (gaussJoinModel v a b) _ hvO
      (ZariskiModel.points_eq_of_charts_eq _ _ (gaussJoinModel_charts_congr hvO a b)),
      gaussJoinModel_vertexSet (r := fun i ↦ Units.mk0 (v (b i)) ((v.ne_zero_iff).2 (hb i)))
        (fun i ↦ rfl)]
    exact ⟨i, rfl⟩
  have key : ∀ y, ModelCode.IsNodePt (projModelCode O' hg) y →
      (∃ v₁ ∈ ModelCode.components (projModelCode O' hg),
        ∃ w₁ ∈ ModelCode.components (projModelCode O' hg), v₁ ≠ w₁ ∧ y ∈ v₁ ∧ y ∈ w₁) ∧
      ∃ W₁ ∈ (gaussJoinModel O'.valuation a b).vertexSet,
      ∃ W₂ ∈ (gaussJoinModel O'.valuation a b).vertexSet, W₁ ≠ W₂ ∧
        ∀ f : RatFunc E, algebraMap (RatFunc E) L f ∈
          ModelCode.germs (projModelCode O' hg) (genericPt O' hg) y → f ∈ W₁ ∧ f ∈ W₂ := by
    intro y hy
    obtain ⟨W, jj, m, hdisc, hTW, hyW, hcyW, hgerm⟩ := hnode y hy
    obtain ⟨h1, h2, h3⟩ := CrossingSource.edgeNode (O := O') hW hv hϖ' hss (hb jj) (hb m) hTW
      (hbase W jj m hTW hyW hcyW) hyW hcyW hgerm
    have hGm := gaussRat_valuationSubring_eq_of_le (v := v) (a := a jj) (a' := a m) (hb m)
      hdisc.2
    refine ⟨h1, _, hvert m, _, hvert jj, hGm ▸ h3, fun f hf ↦ ?_⟩
    obtain ⟨hf1, hf2⟩ := h2 f hf
    exact ⟨hGm ▸ hf1, hf2⟩
  refine ⟨fun y hy ↦ (key y hy).1, hx, ι, inferInstance, inferInstance, a, b, hWM,
    isConvex_of_isEquiv hequiv hconv, isReduced_of_isEquiv hequiv hred, ?_⟩
  rw [xLineAlgebra_eq hx]
  exact fun y hy ↦ (key y hy).2

end TemperedFundamentalGroups.SemistableReduction
