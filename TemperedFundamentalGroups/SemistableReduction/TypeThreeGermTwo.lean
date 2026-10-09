/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8BLimit
import TemperedFundamentalGroups.SemistableReduction.EdgeRepair

/-!
# The two-sided type-3 germ

Blueprint §9.10a, §9.12 O6.1h. The two-sided germ of annuli at a type-3 point `w_{a,ρ}`
(`S8A.TypeThreeGermTwoFor`): there are `r₁ < ρ < ρ₂` such that every edge
`closedBall a ‖c₁‖ ⊊ closedBall a ‖c₂‖` with `r₁ ≤ ‖c₁‖ < ρ < ‖c₂‖ ≤ ρ₂` is good. It implies the
one-sided germ `S8A.TypeThreeGermFor` (`typeThreeGermFor_of_two`).
-/

open Metric

namespace SemistableReduction

namespace S8A

section Field

variable (C : Type*) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- **The two-sided type-3 germ.** -/
def TypeThreeGermTwoFor : Prop :=
  ∀ (a : C) (ρ : ℝ), 0 < ρ → (∀ z : C, ‖z‖ ≠ ρ) → ∃ r₁ < ρ, ∃ ρ₂ > ρ,
    ∀ c₁ c₂ : C, c₁ ≠ 0 → r₁ ≤ ‖c₁‖ → ‖c₁‖ < ρ → ρ < ‖c₂‖ → ‖c₂‖ ≤ ρ₂ →
      EdgeGood F (closedBall a ‖c₁‖) (closedBall a ‖c₂‖)

variable {C F}

/-- The two-sided germ implies the one-sided one. -/
theorem typeThreeGermFor_of_two (h : TypeThreeGermTwoFor C F) : TypeThreeGermFor C F := by
  intro a ρ hρ hirr
  obtain ⟨r₁, hr₁, ρ₂, hρ₂, H⟩ := h a ρ hρ hirr
  obtain ⟨c₁, hc₁, hc₁'⟩ := EdgeRepair.exists_norm_mem_Ioo (C := C)
    (lt_max_of_lt_right (half_pos hρ)) (max_lt hr₁ (half_lt_self hρ))
  have hc₀ : c₁ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hc₁
    exact (lt_max_of_lt_right (half_pos hρ)).not_ge hc₁.le |>.elim
  exact ⟨c₁, hc₀, hc₁', ρ₂, hρ₂, fun c₂ h1 h2 ↦
    H c₁ c₂ hc₀ ((le_max_left _ _).trans hc₁.le) hc₁' h1 h2⟩

end Field

end S8A

end SemistableReduction
