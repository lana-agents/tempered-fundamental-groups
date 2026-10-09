/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiConnected
import TemperedFundamentalGroups.SemistableReduction.ZariskiDVR
import Oka.AlgebraicGeometry.ProjectiveSpace.ZariskiConnected

/-!
# Proof of `Statement.ZariskiConnected`

`Statement.zariskiConnected`: a projective model `c'` over the valuation ring `O'` of a finite
extension of a complete discretely valued field, with a scheme-theoretically dominant point
`Spec L ⟶ c'` over `O'`, has a connected special fibre.

* `c'` is integral: reduced since `Spec L ⟶ c'` is scheme-theoretically dominant (and
  quasi-compact), and irreducible as the closure of a point.
* `O'` is complete (`ZariskiDVR.isAdicComplete_maximalIdeal`).
* If the generic point of `c'` lies over the generic point of `Spec O'`, then the special fibre is
  preconnected by Zariski's connectedness theorem
  (`AlgebraicGeometry.ProjectiveSpace.isPreconnected_closedFibre`, in oka), and nonempty since
  `c' → Spec O'` is closed and the closed point is a specialization of the generic point.
* Otherwise the generic point lies in the (closed) special fibre, which is then everything.

Semistability of `c'` is not needed.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Zariski's connectedness theorem for model codes** (`Statement.ZariskiConnected`). -/
theorem Statement.zariskiConnected : Statement.ZariskiConnected.{u} := by
  intro K _ _ O _ _ K' _ _ _ O' hcomap _ ϖ' hϖ' L _ _ c' j' _ hdom hj
  haveI : IsAdicComplete (maximalIdeal O') O' :=
    ZariskiDVR.isAdicComplete_maximalIdeal O hcomap
  let X := c'.scheme
  let i : X ⟶ ℙ(c'.m; O') := c'.I.subschemeι
  have hf : c'.toSpec = i ≫ ProjectiveSpace.toSpec c'.m O' := rfl
  haveI : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion c'.I.subschemeι)
  -- `j'` is quasi-compact
  haveI : QuasiCompact j' := by
    have h1 : QuasiCompact (j' ≫ c'.toSpec) := by rw [hj]; infer_instance
    exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) j' c'.toSpec
      inferInstance h1
  -- `X` is integral
  haveI : IsReduced X := IsSchemeTheoreticallyDominant.isReduced j'
  let pt : Spec (CommRingCat.of L) := (inferInstance : Nonempty (Spec (CommRingCat.of L))).some
  have hdense : DenseRange j' := j'.denseRange
  have hpt : closure {j' pt} = Set.univ := by
    have hr : Set.range j' = {j' pt} := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        rw [Subsingleton.elim q pt]
        rfl
      · rintro rfl
        exact ⟨pt, rfl⟩
    rw [← hr]
    exact hdense.closure_range
  have hirr : IsIrreducible (Set.univ : Set X) := hpt ▸ isIrreducible_singleton.closure
  haveI : IrreducibleSpace X :=
    { isPreirreducible_univ := hirr.isPreirreducible
      toNonempty := ⟨j' pt⟩ }
  haveI : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hZc : IsClosed (specialFibre c'.toSpec) :=
    (isClosed_singleton_closedPoint O').preimage c'.toSpec.continuous
  rw [← isConnected_iff_connectedSpace]
  by_cases hcase : c'.toSpec (genericPoint X) = closedPoint O'
  · -- the generic point lies in the special fibre, which is then everything
    have huniv : specialFibre c'.toSpec = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      exact (genericPoint_specializes x).mem_closed hZc hcase
    rw [huniv]
    exact hirr.isConnected
  · refine ⟨?_, ?_⟩
    · -- nonempty: the closed point specializes from the image of the generic point
      have hcl : IsClosed (Set.range c'.toSpec) := c'.toSpec.isClosedMap.isClosed_range
      obtain ⟨x, hx⟩ : closedPoint O' ∈ Set.range c'.toSpec :=
        (specializes_closedPoint (c'.toSpec (genericPoint X))).mem_closed hcl ⟨_, rfl⟩
      exact ⟨x, hx⟩
    · rw [hf] at hcase ⊢
      exact ProjectiveSpace.isPreconnected_closedFibre i hcase

end TemperedFundamentalGroups.SemistableReduction
