/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingSource

/-!
# The crossing step (Blueprint §10.3.8, CrossingX1, CX6)

Let `c` be a split W-model without loops, `v` a component with centre valuation `W`, and
`t ∈ L` (the pull back of `u'^{e₂}`) with `W(t) = W(ϖ) ^ p` (the **position** `p` of `v`). If `t`
divides a power of `ϖ` in the germs at a point `z ∈ v`, and `t / ϖ ^ p` vanishes at `z` (it lies
in the maximal ideal of a valuation centred at `z`), then (`step`):

* `z` is a node (at a smooth point `t / ϖ ^ p` would be a unit);
* the other component `v'` through `z` has position `p' > p`;
* `t / ϖ ^ p'` has a pole at `z` along `v'`.

The valuation computation is `step_core`: with node coordinates `s₁ s₂ = ϖ ^ m`, `s₁` the unit on
`v` and `s₂` the unit on `v'`, the divisor lemma gives `t = ε ϖ ^ α s₁ ^ e` with `e ≥ 1`, so
`p = α` and `p' = α + m e`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode

section Core

variable {L : Type u} [Field L]

lemma pow_inj {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ} (h0 : a ≠ 0) (h1 : a < 1)
    {p q : ℕ} (h : a ^ p = a ^ q) : p = q :=
  (pow_right_strictAnti₀ (zero_lt_iff.2 h0) h1).injective h

lemma valuation_unit {V : ValuationSubring L} {ε : L} (h0 : ε ≠ 0) (h : ε ∈ V)
    (hi : ε⁻¹ ∈ V) : V.valuation ε = 1 := by
  have h1 : V.valuation ε ≤ 1 := (V.valuation_le_one_iff _).2 h
  have h2 : V.valuation ε⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 hi
  rw [map_inv₀] at h2
  have h0' : V.valuation ε ≠ 0 := by simpa using h0
  exact le_antisymm h1 (by
    by_contra hlt
    exact absurd h2 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0')).2 (lt_of_not_ge hlt))))

/-- **The valuation computation of the step.** -/
theorem step_core {P : Set L} {ϖ s₁ s₂ t ε : L} {m α e p : ℕ} (hm : 1 ≤ m)
    (hs : s₁ * s₂ = ϖ ^ m) (hϖ0 : ϖ ≠ 0) (hε0 : ε ≠ 0) (hε : ε ∈ P) (hεi : ε⁻¹ ∈ P) (hs₁ : s₁ ∈ P)
    (ht : t = ε * ϖ ^ α * s₁ ^ e ∨ t = ε * ϖ ^ α * s₂ ^ e)
    {W W' R : ValuationSubring L} (hPW : P ⊆ W) (hPW' : P ⊆ W') (hPR : P ⊆ R)
    (hWϖ : W.valuation ϖ < 1)
    (hW₁ : W.valuation s₁ = 1) (hW'₂ : W'.valuation s₂ = 1)
    (htW : W.valuation t = W.valuation ϖ ^ p) (hR : R.valuation (t / ϖ ^ p) < 1) :
    ∃ p', p < p' ∧ W'.valuation t = W'.valuation ϖ ^ p' ∧
      ∀ R' : ValuationSubring L, P ⊆ R' → R'.valuation s₂ < 1 →
        R'.valuation (t / ϖ ^ p')⁻¹ < 1 := by
  have hs₁0 : s₁ ≠ 0 := fun h ↦ by simp [h] at hW₁
  have hs₂0 : s₂ ≠ 0 := fun h ↦ by simp [h] at hW'₂
  have hWϖ0 : W.valuation ϖ ≠ 0 := by simpa using hϖ0
  have hW₂ : W.valuation s₂ = W.valuation ϖ ^ m := by
    rw [← map_pow, ← hs, map_mul, hW₁, one_mul]
  have hW'₁ : W'.valuation s₁ = W'.valuation ϖ ^ m := by
    rw [← map_pow, ← hs, map_mul, hW'₂, mul_one]
  have hWε := valuation_unit hε0 (hPW hε) (hPW hεi)
  have hW'ε := valuation_unit hε0 (hPW' hε) (hPW' hεi)
  have hRε := valuation_unit hε0 (hPR hε) (hPR hεi)
  rcases ht with rfl | rfl
  · -- `t = ε ϖ ^ α s₁ ^ e`: `p = α`
    have hp : p = α := by
      refine pow_inj hWϖ0 hWϖ ?_
      rw [← htW, map_mul, map_mul, hWε, map_pow, map_pow, hW₁]; simp
    subst hp
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · rw [pow_zero, mul_one, mul_div_assoc, div_self (pow_ne_zero _ hϖ0), mul_one,
          hRε] at hR
        exact absurd hR (lt_irrefl _)
      · exact he
    refine ⟨p + m * e, by nlinarith, ?_, fun R' hPR' hR's₂ ↦ ?_⟩
    · rw [map_mul, map_mul, hW'ε, map_pow, map_pow, hW'₁, one_mul, ← pow_mul, ← pow_add]
    · have e1 : (ε * ϖ ^ p * s₁ ^ e / ϖ ^ (p + m * e))⁻¹ = ε⁻¹ * s₂ ^ e := by
        have : ϖ ^ (p + m * e) = ϖ ^ p * (s₁ * s₂) ^ e := by rw [hs, ← pow_mul, pow_add]
        rw [this]
        field_simp
        ring
      rw [e1, map_mul, map_pow, valuation_unit (inv_ne_zero hε0) (hPR' hεi)
        (by rw [inv_inv]; exact hPR' hε), one_mul]
      exact pow_lt_one₀ zero_le hR's₂ (by omega)
  · -- `t = ε ϖ ^ α s₂ ^ e`: impossible
    exfalso
    have hp : p = α + m * e := by
      refine pow_inj hWϖ0 hWϖ ?_
      rw [← htW, map_mul, map_mul, hWε, map_pow, map_pow, hW₂, one_mul, ← pow_mul, ← pow_add]
    subst hp
    have e1 : (ε * ϖ ^ α * s₂ ^ e / ϖ ^ (α + m * e))⁻¹ = ε⁻¹ * s₁ ^ e := by
      have : ϖ ^ (α + m * e) = ϖ ^ α * (s₁ * s₂) ^ e := by rw [hs, ← pow_mul, pow_add]
      rw [this]
      field_simp
      ring
    have hin : (ε * ϖ ^ α * s₂ ^ e / ϖ ^ (α + m * e))⁻¹ ∈ R := by
      rw [e1]; exact mul_mem (hPR hεi) (pow_mem (hPR hs₁) _)
    have hne : ε * ϖ ^ α * s₂ ^ e / ϖ ^ (α + m * e) ≠ 0 := by
      have := hs₂0; have := hϖ0; positivity
    have := valuation_unit hne (R.mem_of_valuation_le_one _ (le_of_lt hR)) hin
    rw [this] at hR
    exact lt_irrefl _ hR

end Core

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
