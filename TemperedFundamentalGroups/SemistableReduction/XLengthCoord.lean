/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XLengthMono

/-!
# The x-length does not depend on the node coordinates (Blueprint §9.7, XL5)

`NodeBranches`: a node core `u v = ϖ ^ n` with branch valuations `W₁` (`u` a unit) and `W₂`
(`v` a unit), the only monomial points at the ends.

* `isXLength_scale_iff`: `u ↦ ε u ^ e`, `n ↦ n e` does not change the x-length;
* `isXLength_swap_iff`: neither does `u ↔ v`;
* `isXLength_of_coord`: any coordinates `u' v' = ϖ ^ n'` of `P` (non-units) for which the
  x-length exists give the x-length of `u`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K} {ϖK : O}
  {P : Subring L} {u v : L} {n : ℕ} {ι : O →+* L}

/-- A node core with its two branch valuations. -/
structure NodeBranches (O : ValuationSubring K) (ϖK : O) (P : Subring L) (ι : O →+* L)
    (u v : L) (n : ℕ) (W₁ W₂ : ValuationSubring L) : Prop where
  core : TemperedFundamentalGroups.SemistableReduction.NodeCore P ι (algebraMap K L ϖK) u v n
  base : ∀ o : O, ι o = algebraMap K L (o : K)
  irred : Irreducible ϖK
  mono₁ : IsMonomialPt O P (algebraMap K L ϖK) u 0 W₁
  mono₂ : IsMonomialPt O P (algebraMap K L ϖK) u n W₂
  uniq₁ : ∀ U : ValuationSubring L, (P : Set L) ⊆ U → U.valuation (algebraMap K L ϖK) < 1 →
    U.valuation u = 1 → U = W₁
  uniq₂ : ∀ U : ValuationSubring L, (P : Set L) ⊆ U → U.valuation (algebraMap K L ϖK) < 1 →
    U.valuation v = 1 → U = W₂

namespace NodeBranches

variable {W₁ W₂ : ValuationSubring L}

/-- The values at a valuation containing `P`. -/
lemma valuation_v_eq (H : NodeBranches O ϖK P ι u v n W₁ W₂) {U : ValuationSubring L}
    (hu : U.valuation u ^ 1 = U.valuation (algebraMap K L ϖK) ^ (n : ℤ)) (hu0 : u ≠ 0) :
    U.valuation v = 1 := by
  have hprod : U.valuation u * U.valuation v = U.valuation (algebraMap K L ϖK) ^ n := by
    rw [← map_mul, H.core.mul_eq, map_pow]
  rw [pow_one, zpow_natCast] at hu
  rw [hu] at hprod
  have hw0 : U.valuation (algebraMap K L ϖK) ^ n ≠ 0 := by
    rw [← hu]; simpa using hu0
  exact (mul_eq_left₀ hw0).1 hprod

lemma ϖ_ne_zero (H : NodeBranches O ϖK P ι u v n W₁ W₂) : algebraMap K L ϖK ≠ 0 := by
  simp only [ne_eq, map_eq_zero]; exact_mod_cast H.irred.ne_zero

lemma u_ne_zero (H : NodeBranches O ϖK P ι u v n W₁ W₂) : u ≠ 0 := fun h ↦ by
  have := H.core.mul_eq; rw [h, zero_mul] at this; exact pow_ne_zero _ H.ϖ_ne_zero this.symm

lemma v_ne_zero (H : NodeBranches O ϖK P ι u v n W₁ W₂) : v ≠ 0 := fun h ↦ by
  have := H.core.mul_eq; rw [h, mul_zero] at this; exact pow_ne_zero _ H.ϖ_ne_zero this.symm

/-- The roles of the coordinates are symmetric. -/
theorem swap [IsDiscreteValuationRing O] (H : NodeBranches O ϖK P ι u v n W₁ W₂) :
    NodeBranches O ϖK P ι v u n W₂ W₁ where
  core := H.core.swap
  base := H.base
  irred := H.irred
  mono₁ := (isMonomialPt_swap_iff H.base H.core H.irred).2 (by simpa using H.mono₂)
  mono₂ := (isMonomialPt_swap_iff H.base H.core H.irred).2 (by simpa using H.mono₁)
  uniq₁ := H.uniq₂
  uniq₂ := H.uniq₁

lemma isLogValue_zero_iff {U : ValuationSubring L} {ϖ f : L} :
    IsLogValue U ϖ f 0 ↔ U.valuation f = 1 := by
  unfold IsLogValue; simp

lemma isLogValue_nat_iff {U : ValuationSubring L} {ϖ f : L} (N : ℕ) :
    IsLogValue U ϖ f (N : ℚ) ↔ U.valuation f = U.valuation ϖ ^ N := by
  have : ((N : ℤ) : ℚ) / ((1 : ℕ) : ℚ) = (N : ℚ) := by simp
  rw [← this, isLogValue_iff one_pos, pow_one, zpow_natCast]

lemma eq_one_of_pow_eq_one' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ} (ha : a ≤ 1)
    {e : ℕ} (he : e ≠ 0) (h : a ^ e = 1) : a = 1 := by
  by_contra h1
  have := pow_lt_one₀ zero_le (ha.lt_of_ne h1) he
  rw [h] at this; exact lt_irrefl _ this

lemma pow_inj' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} {e : ℕ} (he : e ≠ 0)
    (h : a ^ e = b ^ e) : a = b :=
  le_antisymm ((pow_le_pow_iff_left₀ zero_le zero_le he).mp h.le)
    ((pow_le_pow_iff_left₀ zero_le zero_le he).mp h.ge)

variable [IsDiscreteValuationRing O]

/-- **Monomial points under `u ↦ ε u ^ e`**, including the ends. -/
theorem mono_scale (H : NodeBranches O ϖK P ι u v n W₁ W₂) {ε : L} (hε : ε ∈ P)
    (hεi : ε⁻¹ ∈ P) (hε0 : ε ≠ 0) {e : ℕ} (he : 1 ≤ e)
    (hW₁' : IsMonomialPt O P (algebraMap K L ϖK) (ε * u ^ e) 0 W₁)
    (hW₂' : IsMonomialPt O P (algebraMap K L ϖK) (ε * u ^ e) (n * e : ℕ) W₂) {s' : ℚ}
    (hs0 : 0 ≤ s') (hsn : s' ≤ (n * e : ℕ)) {U : ValuationSubring L} :
    IsMonomialPt O P (algebraMap K L ϖK) (ε * u ^ e) s' U ↔
      IsMonomialPt O P (algebraMap K L ϖK) u (s' / e) U := by
  set ϖL := algebraMap K L ϖK
  have hval : ∀ U : ValuationSubring L, (P : Set L) ⊆ U →
      U.valuation (ε * u ^ e) = U.valuation u ^ e := fun U hPU ↦ by
    rw [map_mul, (valuation_eq_one_iff_mem_and_inv_mem U).mpr ⟨hε0, hPU hε, hPU hεi⟩, one_mul,
      map_pow]
  have hle : ∀ U : ValuationSubring L, (P : Set L) ⊆ U → U.valuation u ≤ 1 :=
    fun U hPU ↦ (U.valuation_le_one_iff _).2 (hPU H.core.u_mem)
  have he' : e ≠ 0 := by omega
  rcases hs0.eq_or_lt with rfl | hs0'
  · rw [zero_div]
    constructor
    · intro hU
      have h1 : U.valuation u = 1 := by
        have := (isLogValue_zero_iff.1 hU.2.2.1)
        rw [hval U hU.1] at this
        exact eq_one_of_pow_eq_one' (hle U hU.1) he' this
      rw [H.uniq₁ U hU.1 hU.2.1 h1]; exact H.mono₁
    · intro hU
      rw [H.uniq₁ U hU.1 hU.2.1 (isLogValue_zero_iff.1 hU.2.2.1)]; exact hW₁'
  rcases hsn.eq_or_lt with rfl | hsn'
  · have hne : ((n * e : ℕ) : ℚ) / e = (n : ℚ) := by
      push_cast; field_simp
    rw [hne]
    constructor
    · intro hU
      have h1 : U.valuation u = U.valuation ϖL ^ n := by
        have := (isLogValue_nat_iff _).1 hU.2.2.1
        rw [hval U hU.1, pow_mul] at this
        exact pow_inj' he' this
      have hv1 := H.valuation_v_eq (U := U) (by rw [pow_one, zpow_natCast]; exact h1) H.u_ne_zero
      rw [H.uniq₂ U hU.1 hU.2.1 hv1]; exact H.mono₂
    · intro hU
      have h1 := (isLogValue_nat_iff n).1 hU.2.2.1
      have hv1 := H.valuation_v_eq (U := U) (by rw [pow_one, zpow_natCast]; exact h1) H.u_ne_zero
      rw [H.uniq₂ U hU.1 hU.2.1 hv1]; exact hW₂'
  · exact isMonomialPt_scale_iff H.base H.core H.irred hε hεi hε0 he hs0'
      (by exact_mod_cast hsn')

end NodeBranches

end SemistableReduction
