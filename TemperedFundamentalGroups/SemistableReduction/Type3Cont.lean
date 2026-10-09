/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3NP

/-!
# Continuation of values from a type-3 point

Blueprint §9.10a (II.2). Let `ρ ∉ |C^×|` and `y ∈ F'`, `y ≠ 0`. Near `ρ` the coefficients of the
characteristic polynomial of `y` are monomials in the radius, and the comparisons between their
weighted versions have the same outcome as at `ρ` (no crossing radius equals `ρ`). Hence
(`exists_cont`): for every radius `t` near `ρ` and every extension `w''` of `w_{0,t}`, there are an
extension `ξ` of `w_{0,ρ}` and `N ≥ 1`, `c ∈ C^×`, `m ∈ ℤ` with

  `w''(y)^N = |c| tᵐ`  and  `ξ(y)^N = |c| ρᵐ`,

i.e. `w''(y)` is the monomial continuation of one of the values `ξ(y)` (Newton polygons:
`not_uniqueDom_of_ext` at `t`, `exists_ext_eq_of_not_uniqueDom` at `ρ`).
-/

open Polynomial Filter Topology
open scoped NNReal

namespace SemistableReduction

namespace Type3

open Gauss GaussStability TubeCount TypeThree

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section Persist

variable {ρ : ℝ≥0}

/-- **No crossing at `ρ`.** A comparison of two monomials in the radius which holds near `ρ`
holds at `ρ`. -/
lemma near_le_imp (hρ : IsIrrat C ρ) (α β : C) (hα : α ≠ 0) (a b : ℤ) :
    Near ρ fun s ↦ ‖α‖₊ * (s : ℝ≥0) ^ a ≤ ‖β‖₊ * (s : ℝ≥0) ^ b →
      ‖α‖₊ * ρ ^ a ≤ ‖β‖₊ * ρ ^ b := by
  have hρ0 := hρ.pos
  rcases eq_or_ne a b with rfl | hab
  · refine (near_true hρ0).mono fun s _ h ↦ ?_
    have hs : (0 : ℝ≥0) < (s : ℝ≥0) ^ a := zpow_pos (pos_iff_ne_zero.2 s.ne_zero) a
    have := le_of_mul_le_mul_right h hs
    exact mul_le_mul_of_nonneg_right this zero_le
  rcases lt_or_ge (‖β‖₊ * ρ ^ b) (‖α‖₊ * ρ ^ a) with hgt | hle
  · -- the comparison fails at `ρ`, hence near `ρ`
    have hev : ∀ᶠ t in 𝓝 ρ, ‖β‖₊ * t ^ b < ‖α‖₊ * t ^ a :=
      (continuousAt_mul_zpow _ b hρ0.ne').eventually_lt (continuousAt_mul_zpow _ a hρ0.ne') hgt
    exact (near_of_eventually hρ0 hev).mono fun s hs h ↦ absurd h (not_le.2 hs)
  · exact (near_true hρ0).mono fun _ _ _ ↦ hle

end Persist

end Type3

end SemistableReduction
