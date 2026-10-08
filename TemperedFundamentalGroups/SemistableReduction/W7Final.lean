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

/-!
# `StrongA` from the still open leaves

Blueprint §9.12 (final glue). Of the leaves of `W7.Leaves`, the following are proved:

* `NodeDataOfODP` (O1): `ExhaustGluing.nodeDataOfODP`;
* `L7For` (O6.1c): `S8A.l7For_of` from (T⇒) and (D⇐);
* `A6For` (O6.1f(iii)): `ClassicalSmooth.a6For`;
* `FiniteBadFor` (O6.3): `S8A.finiteBadFor`;
* the S8.C descent (O6.6): `S8A.s8cDescent_of` from the off-skeleton clause and (T⇐).

`W7.OpenLeaves` collects the remaining ones: the off-skeleton clause of (T⇒) (lemma (L)), (D⇒),
(T⇐), (D⇐), the type-3 germ, R5 and the type-4 leaf. **`W10Assembly.strongA_of_openLeaves`**.
-/

universe u

namespace SemistableReduction

open ExhaustGluing ClassicalSmooth

namespace W7

/-- The still open local leaves of `W7.Statement` (Blueprint §9.12). -/
structure OpenLeaves : Prop where
  /-- Lemma (L): the off-skeleton clause of (T⇒). -/
  offSkeleton : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → OffSkeletonOfExhausting C F
  /-- (D⇒). -/
  discCond : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → DiscCondOfSmooth C F
  /-- (T⇐), O12. -/
  exhOfTube : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → ExhaustingOfTube C F
  /-- (D⇐), O12. -/
  smoothOfDisc : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → SmoothOfDiscCond C F
  /-- The type-3 germ (O6.1h). -/
  typeThree : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → S8A.TypeThreeGermFor C F
  /-- R5 (O6.2), for Galois `F`. -/
  r5 : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F] [IsGalois (RatFunc C) F], DefinedOverDVR C F →
    S8A.R5MeasureFor C F
  /-- Goodness near type-4 points (leaf T4). -/
  typeFour : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → S8A.TypeFourGoodFor C F

/-- The leaves of `W7.Statement` from the still open ones. -/
theorem leaves_of_open (h : OpenLeaves.{u}) : Leaves.{u, u} where
  nodeData := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef
    exact nodeDataOfODP hp hp1 hdef
  offSkeleton := h.offSkeleton
  discCond := h.discCond
  exhOfTube := h.exhOfTube
  smoothOfDisc := h.smoothOfDisc
  l7 := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ _ hdef
    exact S8A.l7For_of (tubeOfExhausting_of_definedOverDVR hp hp1 hdef
      (h.offSkeleton C p hp hp1 F hdef)) (h.smoothOfDisc C p hp hp1 F hdef)
  a6 := by
    intro C _ _ _ _ p hp hp1 E _ _ _ _ _ L _ _ _ _ _ _ _ _
    exact a6For hp hp1
  typeThree := h.typeThree
  r5 := h.r5
  finiteBad := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ _
    exact S8A.finiteBadFor hp hp1 F
  typeFour := h.typeFour
  descent := S8A.s8cDescent_of h.offSkeleton h.exhOfTube

/-- **`W7.Statement` from the still open leaves.** -/
theorem statement_of_openLeaves (h : OpenLeaves.{u}) : W7.Statement.{u, u} :=
  statement_of_leaves (leaves_of_open h)

end W7

/-- **`StrongA` from the still open leaves of W7.** -/
theorem W10Assembly.strongA_of_openLeaves (h : W7.OpenLeaves.{u}) :
    TemperedFundamentalGroups.SemistableReduction.Statement.StrongA.{u} :=
  W10Assembly.strongA_of_W7 (W7.statement_of_openLeaves h)

end SemistableReduction
