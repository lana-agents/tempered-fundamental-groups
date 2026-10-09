/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XLengthTools
import TemperedFundamentalGroups.SemistableReduction.NodeCore

/-!
# Monomial points under change of node coordinates (Blueprint §9.7, XL5)

For a node core `P` with coordinates `u v = ϖ ^ n` (`NodeCore`):

* `isMonomialPt_scale_iff`: for a unit `ε` of `P` and `e ≥ 1`, the interior monomial points of
  `ε u ^ e` at `s'` are those of `u` at `s' / e`;
* `isMonomialPt_swap_iff`: the monomial points of `v` at `t` are those of `u` at `n - t`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K} {ϖK : O}
  {P : Subring L} {u v : L} {n : ℕ}

variable {ι : O →+* L} (hι : ∀ o : O, ι o = algebraMap K L (o : K))

include hι in
/-- Units of `P` are congruent to unit constants at valuations with `ϖ, u, v` in the maximal
ideal. -/
lemma exists_const_of_core
    (h : TemperedFundamentalGroups.SemistableReduction.NodeCore P ι (algebraMap K L ϖK) u v n)
    {U : ValuationSubring L} (hPU : (P : Set L) ⊆ U)
    (hϖ : U.valuation (algebraMap K L ϖK) < 1) (hu : U.valuation u < 1) (hv : U.valuation v < 1)
    {ε : L} (hε : ε ∈ P) (hε1 : U.valuation ε = 1) :
    ∃ o : O, IsUnit o ∧ U.valuation (ε - algebraMap K L o) < 1 := by
  have hle : ∀ p ∈ P, U.valuation p ≤ 1 := fun p hp ↦ (U.valuation_le_one_iff _).2 (hPU hp)
  obtain ⟨o, a, ha, b, hb, c, hc, rfl⟩ := h.gen ε hε
  have hsmall : U.valuation (algebraMap K L ϖK * a + u * b + v * c) < 1 := by
    refine lt_of_le_of_lt (U.valuation.map_add _ _) (max_lt (lt_of_le_of_lt
      (U.valuation.map_add _ _) (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
    · exact (mul_le_of_le_one_right' (hle a ha)).trans_lt hϖ
    · exact (mul_le_of_le_one_right' (hle b hb)).trans_lt hu
    · exact (mul_le_of_le_one_right' (hle c hc)).trans_lt hv
  refine ⟨o, ?_, ?_⟩
  · by_contra hno
    obtain ⟨o', ho'⟩ := h.base_nonunit o hno
    have ho : U.valuation (ι o) < 1 := by
      rw [ho', map_mul]
      exact (mul_le_of_le_one_right' (hle _ (h.base_mem o'))).trans_lt hϖ
    have : U.valuation (ι o + algebraMap K L ϖK * a + u * b + v * c) < 1 := by
      rw [add_assoc, add_assoc, ← add_assoc (algebraMap K L ϖK * a)]
      exact lt_of_le_of_lt (U.valuation.map_add _ _) (max_lt ho hsmall)
    rw [hε1] at this
    exact lt_irrefl _ this
  · have : ι o + algebraMap K L ϖK * a + u * b + v * c - algebraMap K L o =
        algebraMap K L ϖK * a + u * b + v * c := by rw [hι]; ring
    rw [this]; exact hsmall

lemma lt_one_of_pow_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a w : Γ} (ha : a ≤ 1)
    (hw : w < 1) {d : ℕ} (h : a ^ d ≤ w) : a < 1 :=
  ha.lt_of_ne fun h1 ↦ by rw [h1, one_pow] at h; exact absurd hw (not_lt.2 h)

include hι in
/-- **Monomial points under `u ↦ ε u ^ e`** (interior parameters). -/
theorem isMonomialPt_scale_iff [IsDiscreteValuationRing O]
    (h : TemperedFundamentalGroups.SemistableReduction.NodeCore P ι (algebraMap K L ϖK) u v n)
    (hϖK : Irreducible ϖK) {ε : L} (hε : ε ∈ P) (hεi : ε⁻¹ ∈ P)
    (hε0 : ε ≠ 0) {e : ℕ} (he : 1 ≤ e) {s' : ℚ} (hs0 : 0 < s') (hsn : s' < n * e)
    {U : ValuationSubring L} :
    IsMonomialPt O P (algebraMap K L ϖK) (ε * u ^ e) s' U ↔
      IsMonomialPt O P (algebraMap K L ϖK) u (s' / e) U := by
  set ϖL := algebraMap K L ϖK
  have hcomap : (P : Set L) ⊆ U → U.valuation ϖL < 1 → U.comap (algebraMap K L) = O :=
    fun hPU hlt ↦ comap_eq_of_lt_one hϖK (fun o ↦ hι o ▸ hPU (h.base_mem o)) hlt
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  set N' := s'.num
  set D' := s'.den
  have hD'e : 0 < e * D' := Nat.mul_pos (by omega) s'.den_pos
  have hs : s' / e = (N' : ℚ) / ((e * D' : ℕ) : ℚ) := by
    rw [show (s' : ℚ) = N' / D' from (Rat.num_div_den s').symm]
    push_cast; field_simp
  -- common facts at a valuation with `P ⊆ U`, `U(ϖ) < 1`
  have key : ∀ (hPU : (P : Set L) ⊆ U) (hϖU : U.valuation ϖL < 1),
      (IsLogValue U ϖL (ε * u ^ e) s' ↔ IsLogValue U ϖL u (s' / e)) ∧
      (IsLogValue U ϖL u (s' / e) →
        (IsResidueTranscendental O U ((ε * u ^ e) ^ D' / ϖL ^ N') ↔
          IsResidueTranscendental O U (u ^ (s' / e).den / ϖL ^ (s' / e).num))) := by
    intro hPU hϖU
    have hUO := hcomap hPU hϖU
    have hε1 : U.valuation ε = 1 :=
      (valuation_eq_one_iff_mem_and_inv_mem U).mpr ⟨hε0, hPU hε, hPU hεi⟩
    have hlog : IsLogValue U ϖL (ε * u ^ e) s' ↔ IsLogValue U ϖL u (s' / e) := by
      rw [hs, isLogValue_iff hD'e]
      unfold IsLogValue
      rw [map_mul, hε1, one_mul, map_pow, ← pow_mul]
    refine ⟨hlog, fun hu ↦ ?_⟩
    -- interior: `ϖ, u, v` in the maximal ideal
    have hsn' : s' / e < n := by
      rw [div_lt_iff₀ (by positivity)]; exact hsn
    obtain ⟨-, hbu, hbv⟩ := generator_bounds h.mul_eq hUO hϖK (by positivity) hsn' hu
    have hu1 := lt_one_of_pow_le ((U.valuation_le_one_iff _).2 (hPU h.u_mem)) hϖU hbu
    have hv1 := lt_one_of_pow_le ((U.valuation_le_one_iff _).2 (hPU h.v_mem)) hϖU hbv
    have hεD : ε ^ D' ∈ P := pow_mem hε _
    have hεDi : (ε ^ D')⁻¹ ∈ P := by rw [← inv_pow]; exact pow_mem hεi _
    have hεD1 : U.valuation (ε ^ D') = 1 := by rw [map_pow, hε1, one_pow]
    have hεDi1 : U.valuation (ε ^ D')⁻¹ = 1 := by rw [map_inv₀, hεD1, inv_one]
    obtain ⟨o, ho, hεo⟩ := exists_const_of_core hι h hPU hϖU hu1 hv1 hεD hεD1
    obtain ⟨o', ho', hεo'⟩ := exists_const_of_core hι h hPU hϖU hu1 hv1 hεDi hεDi1
    have e1 : (ε * u ^ e) ^ D' / ϖL ^ N' = ε ^ D' * (u ^ (e * D') / ϖL ^ N') ^ 1 := by
      rw [pow_one, mul_pow, ← pow_mul, mul_div_assoc]
    have e2 : u ^ (e * D') / ϖL ^ N' = (ε ^ D')⁻¹ * ((ε * u ^ e) ^ D' / ϖL ^ N') ^ 1 := by
      rw [pow_one, e1, pow_one, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hε0), one_mul]
    have hmem : u ^ (s' / e).den / ϖL ^ (s' / e).num ∈ U := by
      have h1 : U.valuation (u ^ (s' / e).den / ϖL ^ (s' / e).num) = 1 := by
        unfold IsLogValue at hu
        rw [map_div₀, map_pow, map_zpow₀, hu, div_self (zpow_ne_zero _
          (valuation_uniformizer hUO hϖK).1)]
      exact (U.valuation_le_one_iff _).1 h1.le
    rw [← residueTranscendental_iff_repr hUO hD'e hs hmem]
    constructor
    · intro htr
      rw [e2]
      exact htr.mul_pow hUO le_rfl ho' hεo'
    · intro htr
      rw [e1]
      exact htr.mul_pow hUO le_rfl ho hεo
  constructor
  · rintro ⟨hPU, hϖU, hlog, htr⟩
    obtain ⟨hl, hr⟩ := key hPU hϖU
    have hu := hl.1 hlog
    exact ⟨hPU, hϖU, hu, (hr hu).1 htr⟩
  · rintro ⟨hPU, hϖU, hlog, htr⟩
    obtain ⟨hl, hr⟩ := key hPU hϖU
    exact ⟨hPU, hϖU, hl.2 hlog, (hr hlog).2 htr⟩

include hι in
/-- **Monomial points under `u ↔ v`**: those of `v` at `t` are those of `u` at `n - t`. -/
theorem isMonomialPt_swap_iff [IsDiscreteValuationRing O]
    (h : TemperedFundamentalGroups.SemistableReduction.NodeCore P ι (algebraMap K L ϖK) u v n)
    (hϖK : Irreducible ϖK) {t : ℚ} {U : ValuationSubring L} :
    IsMonomialPt O P (algebraMap K L ϖK) v t U ↔
      IsMonomialPt O P (algebraMap K L ϖK) u (n - t) U := by
  set ϖL := algebraMap K L ϖK
  have hϖ0 : ϖL ≠ 0 := by
    simp only [ϖL, ne_eq, map_eq_zero]; exact_mod_cast hϖK.ne_zero
  have hu0 : u ≠ 0 := fun h0 ↦ by
    have := h.mul_eq; rw [h0, zero_mul] at this; exact pow_ne_zero _ hϖ0 this.symm
  have hv0 : v ≠ 0 := fun h0 ↦ by
    have := h.mul_eq; rw [h0, mul_zero] at this; exact pow_ne_zero _ hϖ0 this.symm
  set N := t.num
  set D := t.den
  have hD := t.den_pos
  have hrepr : (n : ℚ) - t = ((n * D - N : ℤ) : ℚ) / (D : ℚ) := by
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast t.den_nz
    rw [show t = N / D from (Rat.num_div_den t).symm]
    push_cast
    rw [sub_div, mul_div_assoc, div_self hD0, mul_one]
  have hinv : u ^ D / ϖL ^ (n * D - N : ℤ) = (v ^ D / ϖL ^ N)⁻¹ := by
    have huv : u ^ D * v ^ D = ϖL ^ ((n * D : ℕ) : ℤ) := by
      rw [← mul_pow, h.mul_eq, zpow_natCast, ← pow_mul]
    rw [inv_div, eq_div_iff (pow_ne_zero _ hv0), div_mul_eq_mul_div, huv, zpow_sub₀ hϖ0]
    push_cast
    field_simp
  have key : ∀ (hPU : (P : Set L) ⊆ U) (hϖU : U.valuation ϖL < 1),
      (IsLogValue U ϖL v t ↔ IsLogValue U ϖL u (n - t)) ∧ (IsLogValue U ϖL v t →
        (IsResidueTranscendental O U (v ^ D / ϖL ^ N) ↔
          IsResidueTranscendental O U (u ^ (n - t).den / ϖL ^ (n - t).num))) := by
    intro hPU hϖU
    have hUO : U.comap (algebraMap K L) = O :=
      comap_eq_of_lt_one hϖK (fun o ↦ hι o ▸ hPU (h.base_mem o)) hϖU
    have hw0 : U.valuation ϖL ≠ 0 := by simpa using hϖ0
    have hprod : U.valuation u ^ D * U.valuation v ^ D = U.valuation ϖL ^ ((n * D : ℕ) : ℤ) := by
      rw [← mul_pow, ← map_mul, h.mul_eq, map_pow, zpow_natCast, ← pow_mul]
    have hv0' : U.valuation v ^ D ≠ 0 := pow_ne_zero _ (by simpa using hv0)
    have hlog : IsLogValue U ϖL v t ↔ IsLogValue U ϖL u (n - t) := by
      rw [hrepr, isLogValue_iff hD]
      change U.valuation v ^ D = U.valuation ϖL ^ N ↔ _
      push_cast at hprod ⊢
      constructor
      · intro hB
        rw [zpow_sub₀ hw0, ← hprod, ← hB, mul_div_cancel_right₀ _ (hB ▸ hv0')]
      · intro hA
        have := hprod
        rw [hA, zpow_sub₀ hw0, div_mul_eq_mul_div, div_eq_iff (zpow_ne_zero _ hw0)] at this
        exact mul_left_cancel₀ (zpow_ne_zero _ hw0) this
    refine ⟨hlog, fun hv ↦ ?_⟩
    have hx1 : U.valuation (v ^ D / ϖL ^ N) = 1 := by
      unfold IsLogValue at hv
      rw [map_div₀, map_pow, map_zpow₀, hv, div_self (zpow_ne_zero _ hw0)]
    have hxm : v ^ D / ϖL ^ N ∈ U := (U.valuation_le_one_iff _).1 hx1.le
    have hxi : (v ^ D / ϖL ^ N)⁻¹ ∈ U :=
      (U.valuation_le_one_iff _).1 (by rw [map_inv₀, hx1, inv_one])
    have hymem : u ^ (n - t).den / ϖL ^ (n - t).num ∈ U := by
      have hu := hlog.1 hv
      have h1 : U.valuation (u ^ (n - t).den / ϖL ^ (n - t).num) = 1 := by
        unfold IsLogValue at hu
        rw [map_div₀, map_pow, map_zpow₀, hu, div_self (zpow_ne_zero _ hw0)]
      exact (U.valuation_le_one_iff _).1 h1.le
    rw [← residueTranscendental_iff_repr hUO hD hrepr hymem, hinv]
    exact ⟨fun h' ↦ h'.inv hUO hxi, fun h' ↦ by simpa using h'.inv hUO (by simpa using hxm)⟩
  constructor
  · rintro ⟨hPU, hϖU, hlog, htr⟩
    obtain ⟨hl, hr⟩ := key hPU hϖU
    exact ⟨hPU, hϖU, hl.1 hlog, (hr hlog).1 htr⟩
  · rintro ⟨hPU, hϖU, hlog, htr⟩
    obtain ⟨hl, hr⟩ := key hPU hϖU
    have hv := hl.2 hlog
    exact ⟨hPU, hϖU, hv, (hr hv).2 htr⟩

end SemistableReduction
