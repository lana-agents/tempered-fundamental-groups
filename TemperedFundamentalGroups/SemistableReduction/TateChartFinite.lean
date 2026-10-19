/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0V0

/-!
# The Tate model is a coherent chart algebra on `ℙ¹_O` (Blueprint §12.8, M2.5)

The chart modules of `TateTwoChart.twoChart` are finite over `O[X]` on both charts
(`TateTwoChart.finite_x0`, `finite_x1`): the input `[Module.Finite …]` of
`TwoChartTower.exists_structureMap` for `D = TateTwoChart.twoChart` (the base model `𝒳`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateTwoChart

variable {O : Type u} [CommRing O] (π b₄ t κ : O)

/-- The first chart module of the Tate model is finite over `O[X]`. -/
theorem finite_x0 :
    Module.Finite O[X] (Module.AEval' (twoChart π b₄ t κ).chartModule.x0) :=
  TwoChartGlue.finite_aeval_mulLeft _ (TateGlue0.finite_aeval_h0 (π := π) (b₄ := b₄) (t := t)
    (κ := κ))

/-- The second chart module of the Tate model is finite over `O[X]`. -/
theorem finite_x1 :
    Module.Finite O[X] (Module.AEval' (twoChart π b₄ t κ).chartModule.x1) :=
  TwoChartGlue.finite_aeval_mulLeft _ (TateGlue0.finite_aeval_h1 (π := π) (b₄ := b₄) (t := t)
    (κ := κ))

end TateTwoChart

end SemistableReduction
