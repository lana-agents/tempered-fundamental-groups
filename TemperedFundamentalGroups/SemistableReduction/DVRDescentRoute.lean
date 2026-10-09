/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentUniform
import TemperedFundamentalGroups.SemistableReduction.W10RouteStatements

/-!
# The W10 node descent statement (O1)

Blueprint §9.12, O1: `W10Route.NodeDescentStatement` holds (`W10Route.nodeDescentStatement`),
by specializing `DVRDescent.exists_finset_forall_isSemistableAt`: any `O_E`-algebra structure on
the node chart over `O_E` compatible with `O_E → E → F₀` is `DVRDescent.algO`.
-/

namespace SemistableReduction

namespace W10Route

open GaussTube DVRDescent

universe u

/-- Two `O_E`-algebra structures on `B_E` agreeing with the constants coincide. -/
lemma algebra_eq_algO {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
    {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀]
    [IsScalarTower E (RatFunc E) F₀] {c₀ : E}
    (inst : Algebra (HenselComplete.integers E) (BE F₀ c₀))
    (h : ∀ o, ((@algebraMap _ _ _ _ inst o : BE F₀ c₀) : F₀) = algebraMap E F₀ o) :
    inst = algO (F₀ := F₀) c₀ := by
  refine Algebra.algebra_ext _ _ fun o ↦ Subtype.ext ?_
  rw [h]
  change algebraMap E F₀ o = algebraMap (RatFunc E) F₀ (algebraMap E (RatFunc E) o)
  rw [← IsScalarTower.algebraMap_apply]

/-- **O1, W10-facing form.** -/
theorem nodeDescentStatement : NodeDescentStatement.{u} := by
  intro C _ _ _ _ p hp hp1 G _ _ _ _ _ T hT c₀ hc hc0
  have key := exists_finset_forall_isSemistableAt.{u, u, u} hp hp1 hT hc hc0
  obtain ⟨S, hS⟩ := key
  refine ⟨S, ?_⟩
  intro E _ _ _ φ hφ hSφ halg _ _ F₀ _ _ _ _ _ _ χ hχ hdeg hTχ ϖ hϖ c₀E hcE inst hinst P' hP'm
    hP' hODP
  have heq := algebra_eq_algO inst hinst
  subst heq
  exact hS φ hφ hSφ halg χ hχ hdeg hTχ c₀E hcE (ιN χ hφ hχ hcE) (fun _ ↦ rfl) hϖ P' hP' hODP

end W10Route

end SemistableReduction
