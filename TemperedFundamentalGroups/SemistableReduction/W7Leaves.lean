/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Galois
import TemperedFundamentalGroups.SemistableReduction.S8BAssembly
import TemperedFundamentalGroups.SemistableReduction.EdgeRepairGerms
import TemperedFundamentalGroups.SemistableReduction.TubeSkeleton
import TemperedFundamentalGroups.SemistableReduction.TypeFourGood

/-!
# `W7.Statement` from the remaining local leaves

Blueprint §9.12. The interfaces of `W7.statement_of_interfaces'` (`S8A.GaloisInputs`,
`S8A.S8CDescent`) are reduced to the **leaves** collected in `W7.Leaves`, the open obligations
on the W7 side:

* `NodeDataOfODP` (O1), `OffSkeletonOfExhausting` (lemma (L)), together giving (T⇒);
* (D⇒) `DiscCondOfSmooth`; (T⇐) `ExhaustingOfTube` and (D⇐) `SmoothOfDiscCond` (O12);
* `L7For` (O6.1c), `A6For` (O6.1f(iii)), the type-3 germ `TypeThreeGermFor` (O6.1h);
* `R5MeasureFor` (O6.2), `FiniteBadFor` (O6.3);
* goodness near type-4 points `TypeFourGoodFor` (T4; input of (D⇐), (T⇐));
* the S8.C descent `S8CDescent` (O6.6).

Everything else (R4(ii) `BelowGerm`, its dual `AboveGerm`, the type-2 germ, `KummerUnramFor`,
transport, the Galois lift, the global induction) is proved. **`W7.statement_of_leaves`**.
-/

universe u v

namespace SemistableReduction

open ExhaustGluing ClassicalSmooth

namespace W7

/-- The open local leaves of `W7.Statement` (Blueprint §9.12). -/
structure Leaves : Prop where
  /-- O1: exact node data at ordinary double points (under `DefinedOverDVR`). -/
  nodeData : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → NodeDataOfODP C F
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
  /-- L7 (O6.1c), for Galois `F`. -/
  l7 : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F] [IsGalois (RatFunc C) F], DefinedOverDVR C F → S8A.L7For C F
  /-- A6 (O6.1f(iii)): smoothness descends along Galois towers `C(x) ⊆ E ⊆ L`. -/
  a6 : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (E : Type u) [Field E] [Algebra (RatFunc C) E] [Algebra C E] [IsScalarTower C (RatFunc C) E]
    [FiniteDimensional (RatFunc C) E]
    (L : Type u) [Field L] [Algebra (RatFunc C) L] [Algebra E L] [IsScalarTower (RatFunc C) E L]
    [Algebra C L] [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
    [IsGalois E L], A6For C E L
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
  /-- Finiteness of bad residue balls (O6.3). -/
  finiteBad : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → S8A.FiniteBadFor C F
  /-- Goodness near type-4 points (leaf T4): input of (D⇐), (T⇐). -/
  typeFour : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F → S8A.TypeFourGoodFor C F
  /-- The S8.C descent (O6.6). -/
  descent : S8A.S8CDescent.{u, v}

/-- The Galois inputs of the global induction from the leaves. -/
theorem galoisInputs_of_leaves (h : Leaves.{u, v}) : S8A.GaloisInputs.{u} where
  s8b C _ _ _ _ p hp hp1 F _ _ _ _ _ _ hdef :=
    have hT := tubeOfExhausting hp hp1 (h.nodeData C p hp hp1 F hdef)
      (h.offSkeleton C p hp hp1 F hdef)
    S8A.s8bMinFor_of_open hp hp1 (h.l7 C p hp hp1 F hdef) hT (h.exhOfTube C p hp hp1 F hdef)
      (h.discCond C p hp hp1 F hdef) (h.smoothOfDisc C p hp hp1 F hdef)
      (fun L _ _ _ _ _ _ _ _ ↦ h.a6 C p hp hp1 F L) (h.typeThree C p hp hp1 F hdef)
  r5 C _ _ _ _ p hp hp1 F _ _ _ _ _ _ hdef := h.r5 C p hp hp1 F hdef
  finiteBad C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef := h.finiteBad C p hp hp1 F hdef
  infty C _ _ _ _ p hp hp1 _ _ _ _ _ _ _ :=
    S8A.inftyGoodFor_of_A6 hp hp1 (fun L _ _ _ _ _ _ _ _ ↦ h.a6 C p hp hp1 _ L)
  edgeRepair C _ _ _ _ p hp hp1 F _ _ _ _ _ hdef :=
    EdgeRepair.edgeRepairFor_of hp hp1
      (tubeOfExhausting hp hp1 (h.nodeData C p hp hp1 F hdef) (h.offSkeleton C p hp hp1 F hdef))
      (h.exhOfTube C p hp hp1 F hdef) (h.typeThree C p hp hp1 F hdef)

/-- **`W7.Statement` from the open local leaves.** -/
theorem statement_of_leaves (h : Leaves.{u, v}) : W7.Statement.{u, v} :=
  statement_of_interfaces' (galoisInputs_of_leaves h) h.descent

end W7

end SemistableReduction
