/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10TreeStatement
import TemperedFundamentalGroups.SemistableReduction.W10WModel

/-!
# The statement that the component models of a descended tree are split and unfolded

Blueprint §10.3.8 (StrongComponentA (a), (b)). **`W10.TreeComponentsUnfolded`**: as
`W10.TreeChartsSemistable` (same data: a semistable Gauss tree over `C`, a finite set `S` of
constants, every complete discretely valued `E`-form), with the conclusion that every projective
model `projModelCode O_E g` with the points of the normalized `E`-tree model which is semistable
has split nodes, has no loops and is unfolded on the x-line `X`. It is a definition only (a targeted
input of `strongComponentA_of_W7`); it is to be proved from the classification of the points of
the charts (G4′, split nodes), `noLoops_isUnfolded_projModelCode` and the geometric irreducibility
of the components.
-/

universe u

open IsLocalRing

namespace SemistableReduction

namespace W10

open TemperedFundamentalGroups ProjScheme

/-- **The component models over `E` are split, without loops and unfolded.** -/
def TreeComponentsUnfolded : Prop :=
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
      TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg) ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.NoLoops
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg) ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsUnfolded
        (NormedField.valuation (K := E)).valuationSubring (algebraMap (RatFunc E) F₀ RatFunc.X)
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg)
        (genericPt (NormedField.valuation (K := E)).valuationSubring hg)

end W10

end SemistableReduction
