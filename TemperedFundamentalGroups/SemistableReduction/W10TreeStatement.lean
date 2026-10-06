/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W7Statement
import TemperedFundamentalGroups.SemistableReduction.ProjNormalizationCode

/-!
# The statement of the descent of semistable Gauss trees (G4)

Blueprint §9.7a, step 4. **`W10.TreeChartsSemistable`**: a Gauss tree `(a, c)` over an
algebraically closed `C` that is semistable for `F' / C(x)` in the sense of W7
(`W7.IsSemistableTree`) has, for every complete discretely valued `E ⊆ C` (perfect residue field)
containing a finite set `S` of constants, all charts of the normalization in any `E`-form `F₀` of
`F'` of the `E`-tree model semistable over `O_E`. The finite set `T` of generators of `F'` over
`C(x)` that must lie in `χ(F₀)` makes `S` independent of the `E`-form.

This is the hypothesis `hss` of M9c (`exists_projModelCode_normalization`). It is a definition
only; it is proved from the pointwise descent lemmas (smooth points, node points) and the routing
of points of Segre charts to standard charts.
-/

universe u

open IsLocalRing

namespace SemistableReduction

namespace W10

/-- **G4: the charts of the normalized tree model over `E` are semistable.** -/
def TreeChartsSemistable : Prop :=
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
      (ϖ : (NormedField.valuation (K := E)).valuationSubring) (_ : Irreducible ϖ),
      ∀ Cc ∈ ((gaussJoinModel (NormedField.valuation (K := E)) aE cE).normalization F₀).charts,
        ∀ [Algebra (NormedField.valuation (K := E)).valuationSubring Cc],
          (∀ o, ((algebraMap (NormedField.valuation (K := E)).valuationSubring Cc o : Cc) : F₀) =
            algebraMap (NormedField.valuation (K := E)).valuationSubring F₀ o) →
          IsSemistable ϖ Cc

end W10

end SemistableReduction
