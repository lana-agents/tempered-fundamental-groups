/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Interfaces

/-!
# Goodness near type-4 points (and points of `Ĉ ∖ C`)

Blueprint §9.12, leaf T4 (approved by the coordinator 2026-10-07, option (a)). A nested sequence
of open residue balls of `C` with empty intersection converges to a point of the Berkovich line
which is not seen by `C`: a type-4 point, or a classical point of `Ĉ ∖ C`. Such a point is not on
the skeleton of a semistable model, so some ball of the sequence is good.

`S8A.TypeFourGoodFor C F` is the named leaf; it is an input of (D⇐) `SmoothOfDiscCond` and
(T⇐) `ExhaustingOfTube` (finite-model `δ`-counting cannot exclude nested bad balls with empty
intersection). Planned proof (S8.5, T3 via T2): R5 + L6 + R4, with R5 free of (D⇐)/(T⇐).
-/

open Metric

namespace SemistableReduction

namespace S8A

variable (C : Type*) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- **Goodness near type-4 points** (chart-wise): in every nested sequence of open balls of `C`
with empty intersection, some ball is good in the chart of its given centre. Radii `→ 0`: a limit
in `Ĉ ∖ C`; radii `→ r > 0`: a type-4 point. -/
def TypeFourGoodFor : Prop :=
  ∀ (a c : ℕ → C) (hc : ∀ n, c n ≠ 0),
    (∀ n, ball (a (n + 1)) ‖c (n + 1)‖ ⊆ ball (a n) ‖c n‖) →
    (⋂ n, ball (a n) ‖c n‖) = ∅ → ∃ n, DiscGood F (a n) (hc n)

end S8A

end SemistableReduction
