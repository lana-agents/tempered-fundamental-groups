/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentChoice
import TemperedFundamentalGroups.SemistableReduction.TubeSkeleton

/-!
# Exact node data at ordinary double points under `DefinedOverDVR` (O1)

Blueprint §9.12, O1. The named hypothesis `ExhaustGluing.NodeDataOfODP C F'` of (T⇒)
(`TubeSkeleton`) holds whenever `F'` is defined over a complete discretely valued subfield of `C`
(`nodeDataOfODP`): the affine twists of `F'` are again defined over such a subfield
(`DefinedOverDVR.of_finite`), and at an ordinary double point over the node the descent to a
discretely valued `E ⊆ C` gives the exact node data (`DVRDescent.exists_nodeData`).

* `ExhaustGluing.tubeOfExhausting_of_definedOverDVR`: (T⇒) modulo the off-skeleton clause only.
-/

namespace SemistableReduction

namespace ExhaustGluing

open GaussTube AffineTwist

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

include hp hp1 in
/-- **O1: exact node data at ordinary double points**, for `F'` defined over a complete discretely
valued subfield of `C`. -/
theorem nodeDataOfODP (hdef : DefinedOverDVR C F') : NodeDataOfODP C F' := by
  intro a c c' hc hc' hc0' P' _ hP' hODP
  obtain ⟨b₁, -, hb₁, -⟩ := id hODP
  haveI : Algebra.IsSeparable (RatFunc C) (Aff a c hc F') :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨b₁, hb₁, DVRDescent.exists_nodeData hp hp1 (hdef.of_finite (Aff a c hc F')) hc' hc0' P'
    hP' hODP b₁ hb₁⟩

include hp hp1 in
/-- **(T⇒)** `TubeOfExhausting` for `F'` defined over a complete discretely valued subfield of
`C`, modulo the off-skeleton clause (`OffSkeletonOfExhausting`, lemma (L)). -/
theorem tubeOfExhausting_of_definedOverDVR (hdef : DefinedOverDVR C F')
    (hOff : OffSkeletonOfExhausting C F') : TubeOfExhausting C F' :=
  tubeOfExhausting hp hp1 (nodeDataOfODP hp hp1 hdef) hOff

end ExhaustGluing

end SemistableReduction
