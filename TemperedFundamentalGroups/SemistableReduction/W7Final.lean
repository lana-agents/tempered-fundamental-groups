/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W7Leaves
import TemperedFundamentalGroups.SemistableReduction.W10RouteFinal
import TemperedFundamentalGroups.SemistableReduction.NodeDataODP
import TemperedFundamentalGroups.SemistableReduction.TypeFourLimit
import TemperedFundamentalGroups.SemistableReduction.S8DescentA6
import TemperedFundamentalGroups.SemistableReduction.S8DescentTree
import TemperedFundamentalGroups.SemistableReduction.S8FiniteBad
import TemperedFundamentalGroups.SemistableReduction.DiscCondSmooth
import TemperedFundamentalGroups.SemistableReduction.TypeFourKummerAssembly
import TemperedFundamentalGroups.SemistableReduction.OffSkeleton
import TemperedFundamentalGroups.SemistableReduction.TypeFourCoreG
import TemperedFundamentalGroups.SemistableReduction.ExhaustLimit
import TemperedFundamentalGroups.SemistableReduction.TypeThreeGermTwo

/-!
# `StrongA` from the still open leaves

Blueprint §9.12 (final glue). Of the leaves of `W7.Leaves`, the following are proved:

* `NodeDataOfODP` (O1): `ExhaustGluing.nodeDataOfODP`;
* `L7For` (O6.1c): `S8A.l7For_of` from (T⇒) and (D⇐);
* `A6For` (O6.1f(iii)): `ClassicalSmooth.a6For`;
* `FiniteBadFor` (O6.3): `S8A.finiteBadFor`;
* the S8.C descent (O6.6): `S8A.s8cDescent_of` from the off-skeleton clause and (T⇐);
* (D⇒) `DiscCondOfSmooth` (O11): `ExhaustGluing.discCondOfSmooth`;
* the off-skeleton clause of (T⇒) (lemma (L)): `ExhaustGluing.offSkeletonOfExhausting`;
* the type-4 leaf `TypeFourGoodFor` modulo the Artin–Schreier case of the degree reduction:
  `TypeFour.typeFourGoodFor_of_degreeReductionAS` with part (G) `TypeFour.coreGFor`;
* (D⇐) and (T⇐) (O12) modulo the two `δ`-count steps, the two-sided type-3 germ and the type-4
  leaf: `ExhaustGluing.smoothOfDiscCond_and_exhaustingOfTube`;
* the (one-sided) type-3 germ from the two-sided one: `S8A.typeThreeGermFor_of_two`.

`W7.OpenLeaves` collects the remaining ones: the `δ`-count steps `ExhaustDescentFor`,
`ExhaustGlueFor`, the two-sided type-3 germ `S8A.TypeThreeGermTwoFor`, R5 and the
Artin–Schreier case `TypeFour.DegRed.DegreeReductionASFor` of the degree reduction at type-4
points. **`W10Assembly.strongA_of_openLeaves`**.
-/

universe u

namespace SemistableReduction

open ExhaustGluing ClassicalSmooth

namespace W7

/-- The still open local leaves of `W7.Statement` (Blueprint §9.12). -/
structure OpenLeaves : Prop where
  /-- O12, `δ`-count step: descent of singularities into an exhausting disc of a tube. -/
  exhDescent : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → ExhaustDescentFor C F
  /-- O12, `δ`-count step: gluing of exhaustion through a circle of a tube. -/
  exhGlue : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → ExhaustGlueFor C F
  /-- The two-sided type-3 germ (O6.1h). -/
  typeThreeTwo : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → S8A.TypeThreeGermTwoFor C F
  /-- R5 (O6.2), for Galois `F`. -/
  r5 : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F] [IsGalois (RatFunc C) F], DefinedOverDVR C F →
    S8A.R5MeasureFor C F
  /-- Type-4 leaf, part (d), Artin–Schreier case `μ = A` of the degree reduction at type-4 points
  (Temkin §6.3); the case `μ > A` is `TypeFour.DegRed.degreeReductionFor_of_AS`. -/
  degreeReductionAS : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    TypeFour.DegRed.DegreeReductionASFor C p

/-- The type-4 leaf from the open leaves. -/
theorem OpenLeaves.typeFour (h : OpenLeaves.{u}) (C : Type u) [NontriviallyNormedField C]
    [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) (hp : p.Prime)
    (hp1 : ‖(p : C)‖ < 1) (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] :
    S8A.TypeFourGoodFor C F :=
  TypeFour.typeFourGoodFor_of_degreeReductionAS hp hp1 (h.degreeReductionAS C p hp hp1)
    (fun L _ _ _ _ _ _ ↦ TypeFour.coreGFor hp hp1 L) (fun L _ _ _ _ _ _ _ _ ↦ a6For hp hp1)

/-- (D⇐) and (T⇐) from the open leaves. -/
theorem OpenLeaves.smooth_exh (h : OpenLeaves.{u}) (C : Type u) [NontriviallyNormedField C]
    [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) (hp : p.Prime)
    (hp1 : ‖(p : C)‖ < 1) (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
    (hdef : DefinedOverDVR C F) : SmoothOfDiscCond C F ∧ ExhaustingOfTube C F :=
  smoothOfDiscCond_and_exhaustingOfTube hp hp1 (h.exhDescent C p hp hp1 F hdef)
    (h.exhGlue C p hp hp1 F hdef) (h.typeThreeTwo C p hp hp1 F hdef) (h.typeFour C p hp hp1 F)

/-- The leaves of `W7.Statement` from the still open ones. -/
theorem leaves_of_open (h : OpenLeaves.{u}) : Leaves.{u, u} where
  nodeData := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef
    exact nodeDataOfODP hp hp1 hdef
  offSkeleton := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef
    exact offSkeletonOfExhausting hp hp1 (nodeDataOfODP hp hp1 hdef)
  discCond := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ _
    exact discCondOfSmooth hp hp1
  exhOfTube := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef
    exact (h.smooth_exh C p hp hp1 F hdef).2
  smoothOfDisc := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef
    exact (h.smooth_exh C p hp hp1 F hdef).1
  l7 := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ _ hdef
    exact S8A.l7For_of (tubeOfExhausting_of_definedOverDVR hp hp1 hdef
      (offSkeletonOfExhausting hp hp1 (nodeDataOfODP hp hp1 hdef)))
      (h.smooth_exh C p hp hp1 F hdef).1
  a6 := by
    intro C _ _ _ _ p hp hp1 E _ _ _ _ _ L _ _ _ _ _ _ _ _
    exact a6For hp hp1
  typeThree := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef
    exact S8A.typeThreeGermFor_of_two (h.typeThreeTwo C p hp hp1 F hdef)
  r5 := h.r5
  finiteBad := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ _
    exact S8A.finiteBadFor hp hp1 F
  typeFour := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ _
    exact h.typeFour C p hp hp1 F
  descent := S8A.s8cDescent_of
    (fun _ _ _ _ _ _ hp hp1 _ _ _ _ _ _ hdef ↦
      offSkeletonOfExhausting hp hp1 (nodeDataOfODP hp hp1 hdef))
    (fun C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef ↦ (h.smooth_exh C p hp hp1 F hdef).2)

/-- **`W7.Statement` from the still open leaves.** -/
theorem statement_of_openLeaves (h : OpenLeaves.{u}) : W7.Statement.{u, u} :=
  statement_of_leaves (leaves_of_open h)

end W7

/-- **`StrongA` from the still open leaves of W7.** -/
theorem W10Assembly.strongA_of_openLeaves (h : W7.OpenLeaves.{u}) :
    TemperedFundamentalGroups.SemistableReduction.Statement.StrongA.{u} :=
  W10Assembly.strongA_of_W7 (W7.statement_of_openLeaves h)

end SemistableReduction
