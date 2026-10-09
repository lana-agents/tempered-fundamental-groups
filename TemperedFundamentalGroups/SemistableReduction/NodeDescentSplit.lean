/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentRoute
import TemperedFundamentalGroups.SemistableReduction.SplitNodeGen

/-!
# The node descent statement, split form

Blueprint §10.3.8 (split nodes). `W10Route.NodeDescentSplitStatement`: the node descent statement
`W10Route.NodeDescentStatement` with the conclusion strengthened to a **split node**
(`IsSplitNodeAt`): the descended node point has the residue field of `O_E` in a common étale
neighbourhood with the singular point of the node. It holds with the same finite set of
constants (`W10Route.nodeDescentSplitStatement`): the residues at the descended point are
rational by construction (`exists_finset_forall_isSplitNodeAt`).
-/

namespace SemistableReduction

namespace W10Route

open GaussTube DVRDescent

universe u

/-- **Descent of node points, split form.** As `NodeDescentStatement`, with the conclusion
`IsSplitNodeAt ϖ (P'.comap ιN)`. -/
def NodeDescentSplitStatement : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ) (_ : p.Prime) (_ : ‖(p : C)‖ < 1)
    (G : Type u) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
    [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
    (T : Finset G) (_ : Algebra.adjoin (RatFunc C) (T : Set G) = ⊤)
    (c₀ : C) (hc : ‖c₀‖ < 1) (hc0 : c₀ ≠ 0),
    ∃ S : Finset C, ∀ (E : Type u) [NontriviallyNormedField E] [IsUltrametricDist E]
      [CompleteSpace E] (φ : E →+* C) (hφ : ∀ e, ‖φ e‖ = ‖e‖) (_ : (S : Set C) ⊆ Set.range φ)
      (_ : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
      [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
      [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := E)).valuationSubring)]
      (F₀ : Type u) [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀]
      [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
      [Algebra.IsSeparable (RatFunc E) F₀]
      (χ : F₀ →+* G)
      (hχ : ∀ x, χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) G (ratFuncMap φ x))
      (_ : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
      (_ : (T : Set G) ⊆ Set.range χ)
      (ϖ : (NormedField.valuation (K := E)).valuationSubring) (_ : Irreducible ϖ)
      (c₀E : E) (hcE : φ c₀E = c₀)
      [Algebra (NormedField.valuation (K := E)).valuationSubring (Rint c₀E F₀)]
      (_ : ∀ o, ((algebraMap (NormedField.valuation (K := E)).valuationSubring
        (Rint c₀E F₀) o : Rint c₀E F₀) : F₀) = algebraMap E F₀ o)
      (P' : Ideal (Rint c₀ G)), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c₀) (Rint c₀ G)) = tubeIdeal c₀ →
      IsNodeODP hc hc0 P' →
      IsSplitNodeAt ϖ (P'.comap (ιN χ hφ hχ hcE))

/-- **O1, split form.** -/
theorem nodeDescentSplitStatement : NodeDescentSplitStatement.{u} := by
  intro C _ _ _ _ p hp hp1 G _ _ _ _ _ T hT c₀ hc hc0
  obtain ⟨S, hS⟩ := exists_finset_forall_isSplitNodeAt.{u, u, u} hp hp1 hT hc hc0
  refine ⟨S, ?_⟩
  intro E _ _ _ φ hφ hSφ halg _ _ F₀ _ _ _ _ _ _ χ hχ hdeg hTχ ϖ hϖ c₀E hcE inst hinst P' hP'm
    hP' hODP
  have heq := algebra_eq_algO inst hinst
  subst heq
  exact hS φ hφ hSφ halg χ hχ hdeg hTχ c₀E hcE (ιN χ hφ hχ hcE) (fun _ ↦ rfl) hϖ P' hP' hODP

/-- The split form implies the original. -/
theorem nodeDescentStatement_of_split (h : NodeDescentSplitStatement.{u}) :
    NodeDescentStatement.{u} := by
  intro C _ _ _ _ p hp hp1 G _ _ _ _ _ T hT c₀ hc hc0
  obtain ⟨S, hS⟩ := h C p hp hp1 G T hT c₀ hc hc0
  refine ⟨S, ?_⟩
  intro E _ _ _ φ hφ hSφ halg _ _ F₀ _ _ _ _ _ _ χ hχ hdeg hTχ ϖ hϖ c₀E hcE inst hinst P' hP'm
    hP' hODP
  exact (hS E φ hφ hSφ halg F₀ χ hχ hdeg hTχ ϖ hϖ c₀E hcE hinst P' hP'm hP' hODP).isSemistableAt

end W10Route

end SemistableReduction
