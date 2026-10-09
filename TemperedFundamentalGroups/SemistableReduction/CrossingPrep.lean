/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingGlue

/-!
# Small lemmas for `Statement.CrossingX1` (Blueprint §10.3.8)

* `exists_ramification`: the uniformizer of `O` is a unit times a positive power of the
  uniformizer of an extension DVR;
* `lt_one_of_pow_lt_one`, `eq_one_of_pow_eq_one`: powers of valuations of integral elements.
-/

open IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingGlue

/-- **Ramification.** -/
theorem exists_ramification {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    {O : ValuationSubring K} {O' : ValuationSubring K'} [IsDiscreteValuationRing O']
    (h' : O'.comap (algebraMap K K') = O) {ϖ₀ : O} (hϖ₀ : Irreducible ϖ₀) {ϖ' : O'}
    (hϖ' : Irreducible ϖ') :
    ∃ (e : ℕ) (μ : O'ˣ), 1 ≤ e ∧ algebraMap K K' (ϖ₀ : K) = ((μ : O') : K') * (ϖ' : K') ^ e := by
  subst h'
  have hmem : algebraMap K K' (ϖ₀ : K) ∈ O' := ϖ₀.2
  set a : O' := ⟨_, hmem⟩
  have ha0 : a ≠ 0 := fun h ↦ by
    have : algebraMap K K' (ϖ₀ : K) = 0 := congrArg Subtype.val h
    rw [map_eq_zero] at this
    exact hϖ₀.ne_zero (Subtype.ext this)
  obtain ⟨e, μ, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ'
  refine ⟨e, μ, ?_, by simpa using congrArg Subtype.val he⟩
  rcases Nat.eq_zero_or_pos e with rfl | h
  · exfalso
    rw [pow_zero, mul_one] at he
    -- `ϖ₀` would be a unit of `O`
    apply hϖ₀.not_isUnit
    have hinv : (algebraMap K K' (ϖ₀ : K))⁻¹ ∈ O' := by
      have : (algebraMap K K' (ϖ₀ : K))⁻¹ = ((μ⁻¹ : O'ˣ) : O') := by
        rw [show algebraMap K K' (ϖ₀ : K) = ((μ : O') : K') from congrArg Subtype.val he]
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (by simp), ← Subring.coe_mul, ← Units.val_mul,
          inv_mul_cancel, Units.val_one]; rfl
      rw [this]; exact Subtype.property _
    have h0 : (ϖ₀ : K) ≠ 0 := fun h ↦ hϖ₀.ne_zero (Subtype.ext h)
    have hO : (ϖ₀ : K)⁻¹ ∈ O'.comap (algebraMap K K') :=
      ValuationSubring.mem_comap.2 (by rw [map_inv₀]; exact hinv)
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hO⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  · exact h

lemma lt_one_of_pow_lt_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ} (ha : a ≤ 1)
    {e : ℕ} (h : a ^ e < 1) : a < 1 :=
  ha.lt_of_ne fun h1 ↦ by rw [h1, one_pow] at h; exact lt_irrefl _ h

lemma eq_one_of_pow_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ} (ha : a ≤ 1)
    {e : ℕ} (he : 1 ≤ e) (h : a ^ e = 1) : a = 1 := by
  by_contra h1
  have := pow_lt_one₀ zero_le (ha.lt_of_ne h1) (by omega : e ≠ 0)
  rw [h] at this
  exact lt_irrefl _ this

end TemperedFundamentalGroups.SemistableReduction.CrossingGlue
