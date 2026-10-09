/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10TreeUnfolded
import TemperedFundamentalGroups.SemistableReduction.ComponentUnfolded
import TemperedFundamentalGroups.SemistableReduction.W10MainC
import TemperedFundamentalGroups.SemistableReduction.W10RouteSplitTree
import TemperedFundamentalGroups.SemistableReduction.SplitNodePoints
import TemperedFundamentalGroups.SemistableReduction.ProjSplitPoints
import TemperedFundamentalGroups.SemistableReduction.GaussTreeFinite

/-!
# `W10.TreeComponentsUnfolded` from the geometric irreducibility of the components

`W10.treeComponentsUnfolded_of`: G4′ (`W10Route.treeChartsSplit`, split nodes and the edge form
of node points, `projModelCode_split_of_points`, `exists_routedEdge_of_isNodePt`) and
`noLoops_isUnfolded_projModelCode` give split nodes, no loops and unfoldedness of every component
model; the remaining part of `IsSplit`, the geometric irreducibility of the components, is the
targeted hypothesis `W10.TreeComponentsGeomIrred` (same data).
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10

open TemperedFundamentalGroups ProjScheme ZariskiModel GaussTree

/-- **The components of the component models over `E` are geometrically irreducible.** -/
def TreeComponentsGeomIrred : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ) (_ : p.Prime) (_ : ‖(p : C)‖ < 1)
    (F' : Type u) [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
    [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
    (ι : Type) [Fintype ι] [Nonempty ι] (a c : ι → C) (hc : ∀ i, c i ≠ 0)
    (_ : GaussTree.IsConvex (NormedField.valuation (K := C)) a c)
    (_ : GaussTree.IsReduced (NormedField.valuation (K := C)) a c)
    (_ : W7.IsSemistableTree a c hc F')
    (T : Finset F') (_ : Algebra.adjoin (RatFunc C) (T : Set F') = ⊤),
    ∃ S : Finset C, ∀ (E : Type u) [NontriviallyNormedField E] [IsUltrametricDist E]
      [CompleteSpace E] (φ : E →+* C) (_ : ∀ e, ‖φ e‖ = ‖e‖) (_ : (S : Set C) ⊆ Set.range φ)
      (_ : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
      [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
      [PerfectField (ResidueField (NormedField.valuation (K := E)).valuationSubring)]
      (aE cE : ι → E) (_ : ∀ i, φ (aE i) = a i) (_ : ∀ i, φ (cE i) = c i)
      (F₀ : Type u) [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀]
      [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
      [Algebra.IsSeparable (RatFunc E) F₀]
      [Algebra (NormedField.valuation (K := E)).valuationSubring F₀]
      [IsScalarTower (NormedField.valuation (K := E)).valuationSubring E F₀]
      (χ : F₀ →+* F')
      (_ : ∀ x, χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) F' (ratFuncMap φ x))
      (_ : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
      (_ : (T : Set F') ⊆ Set.range χ)
      (ϖ : (NormedField.valuation (K := E)).valuationSubring) (_ : Irreducible ϖ)
      (n : ℕ) (g : Fin (n + 1) → F₀) (hg : ∀ l, g l ≠ 0),
      (ZariskiModel.projModel
          (algebraMap (NormedField.valuation (K := E)).valuationSubring F₀).range g).points =
        ((gaussJoinModel (NormedField.valuation (K := E)) aE cE).normalization F₀).points →
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg) →
      TemperedFundamentalGroups.SemistableReduction.ModelCode.HasGeomIrreducibleComponents
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg)

lemma comap_valuation_lt_one_iff {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    (W : ValuationSubring F') {z : F} :
    (W.comap (algebraMap F F')).valuation z < 1 ↔ W.valuation (algebraMap F F' z) < 1 := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap, Ne, Ne,
    valuation_comap_eq_one_iff]

/-- **`TreeComponentsUnfolded` from `TreeComponentsGeomIrred`.** -/
theorem treeComponentsUnfolded_of (hG : TreeComponentsGeomIrred.{u}) :
    TreeComponentsUnfolded.{u} := by
  intro C _ _ _ _ p hp hp1 F' _ _ _ _ _ ι _ _ a c hc hconv hred hss T hT
  obtain ⟨S₁, hS₁⟩ := W10Route.treeChartsSplit C p hp hp1 F' ι a c hc hconv hred hss T hT
  obtain ⟨S₂, hS₂⟩ := hG C p hp hp1 F' ι a c hc hconv hred hss T hT
  classical
  refine ⟨S₁ ∪ S₂, ?_⟩
  intro E _ _ _ φ hφ hS hal _ _ aE cE haE hcE F₀ _ _ _ _ _ _ _ _ χ hχ hfr hTχ ϖ hϖ n g hg hpts
    hssg
  have hS₁' : (S₁ : Set C) ⊆ Set.range φ := fun z hz ↦ hS (by simp [hz])
  have hS₂' : (S₂ : Set C) ⊆ Set.range φ := fun z hz ↦ hS (by simp [hz])
  have hclass := hS₁ E φ hφ hS₁' hal aE cE haE hcE F₀ χ hχ hfr hTχ ϖ hϖ
  have hgi := hS₂ E φ hφ hS₂' hal aE cE haE hcE F₀ χ hχ hfr hTχ ϖ hϖ n g hg hpts hssg
  have hcE0 : ∀ i, cE i ≠ 0 := fun i h ↦ hc i (by rw [← hcE i, h, map_zero])
  have hconvE := W10Assembly.isConvex_descent φ hφ haE hcE hconv
  have hredE := W10Assembly.isReduced_descent φ hφ haE hcE hred
  have hfin := gaussJoinModel_normalization_isFiniteType (F' := F₀) hcE0 hconvE hredE
    (eq_or_eq_top_of_le hϖ)
  obtain ⟨hsplitF, hbr⟩ := projModelCode_split_of_points hg _ hfin hpts
  have hsn := hsplitF ϖ (by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ])
    (fun C' hC' _ hc' 𝔭 hp' ↦ (hclass C' hC' hc' 𝔭 hp').isSplitSemistableAt)
  have hx : Transcendental E (algebraMap (RatFunc E) F₀ RatFunc.X) :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc E) F₀).injective).2
      RatFunc.transcendental_X
  have hnode : ∀ y, TemperedFundamentalGroups.SemistableReduction.ModelCode.IsNodePt
      (projModelCode (NormedField.valuation (K := E)).valuationSubring hg) y →
      ∃ (W : ValuationSubring F₀) (jj m : ι), DiscLE (NormedField.valuation (K := E)) aE cE jj m ∧
        normChart F₀ (nodeChart (NormedField.valuation (K := E))
          (coord (RatFunc.X : RatFunc E) (aE jj) (cE m)) (cE jj / cE m)) ≤ W.toSubring ∧
        W.valuation (algebraMap (RatFunc E) F₀ (coord (RatFunc.X : RatFunc E) (aE jj) (cE m))) <
          1 ∧
        W.valuation (algebraMap (RatFunc E) F₀
          (algebraMap E (RatFunc E) (cE jj / cE m) /
            coord (RatFunc.X : RatFunc E) (aE jj) (cE m))) < 1 ∧
        TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
          (projModelCode (NormedField.valuation (K := E)).valuationSubring hg)
          (genericPt (NormedField.valuation (K := E)).valuationSubring hg) y =
          (localAt (normChart F₀ (nodeChart (NormedField.valuation (K := E))
            (coord (RatFunc.X : RatFunc E) (aE jj) (cE m)) (cE jj / cE m))) W : Set F₀) :=
    fun y hy ↦ by
    obtain ⟨W, S, ⟨jj, m, hdisc, -, -, rfl, hy₁, hy₂⟩, hSW, hgerm⟩ :=
      W10Route.exists_routedEdge_of_isNodePt hg hbr hclass y hy
    exact ⟨W, jj, m, hdisc, hSW, (comap_valuation_lt_one_iff W).1 hy₁,
      (comap_valuation_lt_one_iff W).1 hy₂, hgerm⟩
  obtain ⟨hnl, hunf⟩ :=
    TemperedFundamentalGroups.SemistableReduction.noLoops_isUnfolded_projModelCode
    (NormedField.valuation (K := E)).valuationSubring hx aE cE hcE0 (NormedField.valuation (K := E))
    rfl hconvE hredE hg hpts hϖ hssg hnode
  exact ⟨⟨hsn, hgi⟩, hnl, hunf⟩

end W10

end SemistableReduction
