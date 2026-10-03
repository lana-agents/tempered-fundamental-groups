/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GoodCentre

/-!
# The reduction of a Kummer generator

Blueprint §9.10, L4 (K6, residue computation). Let `v` be a valuation on a field `E` extending the
norm of `C` (`‖p‖ < 1`, `γ^(p-1) = -p`), `θ ∈ E` with `θ^p` close to `F ∈ E`, and `H ∈ E` with
`v H ≤ 1` an approximation of `F` by a `p`-th power: `G = F - H^p`.

* **`valuation_sub_eq` (purely inseparable case)**: if `v G = ‖λ‖^p` with `‖γ‖ < ‖λ‖ ≤ 1` and
  `v(θ^p - F) < ‖λ‖^p`, then `v(θ - H) = ‖λ‖`, and `w = (θ - H)/λ` satisfies
  `v(w^p - G/λ^p) < 1`: the reduction of `w` is a `p`-th root of the reduction of `G/λ^p`
  (Arzdorf (2.18)–(2.19), `l > 0`);
* **`valuation_as_lt` (Artin–Schreier case)**: if `v G ≤ ‖γ‖^p` and `v(θ^p - F) < ‖γ‖^p`, then
  `w = (θ - H)/γ` satisfies `v w ≤ 1` and `v(w^p - H^(p-1) w - G/γ^p) < 1`
  (Arzdorf (2.19) with `P_l = P'₀`).
-/

open NNReal

namespace SemistableReduction

namespace KummerResidue

variable {C : Type*} [NormedField C] {E : Type*} [Field E] [Algebra C E]
  (v : Valuation E ℝ≥0) (hv : ∀ c : C, v (algebraMap C E c) = ‖c‖₊)

variable (p : ℕ) [hp : Fact p.Prime]

include hv in
lemma valuation_natCast (n : ℕ) : v (n : E) = ‖(n : C)‖₊ := by
  rw [← map_natCast (algebraMap C E), hv]

include hv in
/-- `(H + z)^p - H^p - z^p` is bounded by `‖p‖ max(v z, v z^(p-1))` if `v H ≤ 1`. -/
lemma valuation_binom_le [IsUltrametricDist C] {H z : E} (hH : v H ≤ 1) :
    v ((H + z) ^ p - H ^ p - z ^ p) ≤ ‖(p : C)‖₊ * max (v z) (v z ^ (p - 1)) := by
  have hsum : (H + z) ^ p - H ^ p - z ^ p =
      ∑ k ∈ (Finset.range (p + 1)).erase 0 |>.erase p,
        z ^ k * H ^ (p - k) * (p.choose k : E) := by
    rw [add_comm H z, add_pow, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 (Nat.lt_succ_self p)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hp.out.ne_zero.symm, Finset.mem_range.2
        (Nat.succ_pos p)⟩)]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero,
      Nat.choose_zero_right, one_mul, Nat.sub_zero]
    rw [Finset.erase_right_comm]
    ring
  rw [hsum]
  refine Valuation.map_sum_le v fun k hk ↦ ?_
  obtain ⟨hkp, hk'⟩ := Finset.mem_erase.1 hk
  obtain ⟨hk0, hk⟩ := Finset.mem_erase.1 hk'
  have hklt : k < p := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hkp
  rw [map_mul, map_mul, map_pow, map_pow, valuation_natCast v hv]
  have hch : ‖(p.choose k : C)‖₊ ≤ ‖(p : C)‖₊ := PTaylor.nnnorm_choose_le p hk0 hklt
  have hzk : v z ^ k ≤ max (v z) (v z ^ (p - 1)) := by
    rcases le_total (v z) 1 with h1 | h1
    · exact (pow_le_of_le_one zero_le h1 hk0).trans (le_max_left _ _)
    · exact (pow_le_pow_right₀ h1 (by omega)).trans (le_max_right _ _)
  calc v z ^ k * v H ^ (p - k) * ‖(p.choose k : C)‖₊
      ≤ max (v z) (v z ^ (p - 1)) * 1 * ‖(p : C)‖₊ := by
        gcongr
        exact pow_le_one₀ zero_le hH
    _ = _ := by ring

include hv in
/-- The binomial terms of degree `≥ 2` in `z`: `(H + z)^p - H^p - z^p - p H^(p-1) z` is bounded by
`‖p‖ (v z)^2` if `v H ≤ 1` and `v z ≤ 1`. -/
lemma valuation_binom_two_le [IsUltrametricDist C] {H z : E} (hH : v H ≤ 1) (hz : v z ≤ 1) :
    v ((H + z) ^ p - H ^ p - z ^ p - (p : E) * H ^ (p - 1) * z) ≤ ‖(p : C)‖₊ * v z ^ 2 := by
  have hp2 := hp.out.two_le
  have hsum : (H + z) ^ p - H ^ p - z ^ p - (p : E) * H ^ (p - 1) * z =
      ∑ k ∈ ((Finset.range (p + 1)).erase 0 |>.erase p).erase 1,
        z ^ k * H ^ (p - k) * (p.choose k : E) := by
    have h1 : 1 ∈ ((Finset.range (p + 1)).erase 0).erase p :=
      Finset.mem_erase.2 ⟨by omega, Finset.mem_erase.2 ⟨one_ne_zero, Finset.mem_range.2 (by omega)⟩⟩
    rw [add_comm H z, add_pow, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 (Nat.lt_succ_self p)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hp.out.ne_zero.symm, Finset.mem_range.2
        (Nat.succ_pos p)⟩)]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero,
      Nat.choose_zero_right, one_mul, Nat.sub_zero]
    rw [Finset.erase_right_comm, ← Finset.add_sum_erase _ _ h1]
    simp only [pow_one, Nat.choose_one_right]
    ring
  rw [hsum]
  refine Valuation.map_sum_le v fun k hk ↦ ?_
  obtain ⟨hk1, hk⟩ := Finset.mem_erase.1 hk
  obtain ⟨hkp, hk'⟩ := Finset.mem_erase.1 hk
  obtain ⟨hk0, hk⟩ := Finset.mem_erase.1 hk'
  have hklt : k < p := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hkp
  rw [map_mul, map_mul, map_pow, map_pow, valuation_natCast v hv]
  have hch : ‖(p.choose k : C)‖₊ ≤ ‖(p : C)‖₊ := PTaylor.nnnorm_choose_le p hk0 hklt
  calc v z ^ k * v H ^ (p - k) * ‖(p.choose k : C)‖₊ ≤ v z ^ 2 * 1 * ‖(p : C)‖₊ :=
        mul_le_mul (mul_le_mul (pow_le_pow_of_le_one zero_le hz (by omega))
          (pow_le_one₀ zero_le hH) zero_le zero_le) hch zero_le zero_le
    _ = _ := by ring

variable [IsUltrametricDist C] {γ : C} (hγ : γ ^ (p - 1) = -(p : C))

omit hp [IsUltrametricDist C] in
include hγ in
lemma nnnorm_p_eq' : ‖(p : C)‖₊ = ‖γ‖₊ ^ (p - 1) := by
  rw [← nnnorm_pow, hγ, nnnorm_neg]

include hv hγ in
/-- **The purely inseparable case.** If `v(F - H^p) = ‖λ‖^p` with `‖γ‖ < ‖λ‖ ≤ 1` and
`v(θ^p - F) < ‖λ‖^p`, then `v(θ - H) = ‖λ‖` and `((θ - H)/λ)^p ≡ (F - H^p)/λ^p` modulo the
maximal ideal of `v`. -/
theorem valuation_sub_eq {θ H F : E} (hH : v H ≤ 1) {l : C} (hγl : ‖γ‖₊ < ‖l‖₊)
    (hl1 : ‖l‖₊ ≤ 1) (hG : v (F - H ^ p) = ‖l‖₊ ^ p) (hθ : v (θ ^ p - F) < ‖l‖₊ ^ p) :
    v (θ - H) = ‖l‖₊ ∧
      v (((θ - H) / algebraMap C E l) ^ p - (F - H ^ p) / algebraMap C E l ^ p) < 1 := by
  have hp2 := hp.out.two_le
  set z := θ - H
  set T := ‖l‖₊
  have hT0 : 0 < T := lt_of_le_of_lt zero_le hγl
  have hpT : ‖(p : C)‖₊ < T ^ (p - 1) := by
    rw [nnnorm_p_eq' p hγ]; exact pow_lt_pow_left₀ hγl zero_le (by omega)
  set R := (H + z) ^ p - H ^ p - z ^ p
  have hR := valuation_binom_le v hv p (z := z) hH
  have hid : z ^ p + R = (F - H ^ p) + (θ ^ p - F) := by
    simp only [R, z]; ring
  have hrhs : v ((F - H ^ p) + (θ ^ p - F)) = T ^ p := by
    rw [Valuation.map_add_eq_of_lt_left _ (hG ▸ hθ), hG]
  have hs : v z = T := by
    set s := v z
    rcases le_or_gt s 1 with hs1 | hs1
    · have hmax : max s (s ^ (p - 1)) = s :=
        max_eq_left (pow_le_of_le_one zero_le hs1 (by omega))
      rw [hmax] at hR
      by_cases hdom : ‖(p : C)‖₊ * s < s ^ p
      · have : v (z ^ p + R) = s ^ p := by
          rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hR.trans_lt hdom),
            map_pow]
        rw [hid, hrhs] at this
        exact ((pow_left_inj₀ zero_le zero_le hp.out.ne_zero).1 this).symm
      · push Not at hdom
        exfalso
        have hle : v (z ^ p + R) ≤ ‖(p : C)‖₊ * s :=
          (Valuation.map_add v _ _).trans (max_le (by rw [map_pow]; exact hdom) hR)
        rw [hid, hrhs] at hle
        -- `s ≤ ‖γ‖`
        have hsγ : s ≤ ‖γ‖₊ := by
          rcases eq_or_ne s 0 with h0 | h0
          · rw [h0]; exact zero_le
          have hs0 : 0 < s := pos_iff_ne_zero.2 h0
          have : s ^ (p - 1) ≤ ‖(p : C)‖₊ := by
            have h2 : s ^ (p - 1) * s ≤ ‖(p : C)‖₊ * s := by
              rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]; exact hdom
            exact le_of_mul_le_mul_right h2 hs0
          rw [nnnorm_p_eq' p hγ] at this
          exact (pow_le_pow_iff_left₀ zero_le zero_le (by omega)).1 this
        have : T ^ p ≤ ‖γ‖₊ ^ p := by
          calc T ^ p ≤ ‖(p : C)‖₊ * s := hle
            _ ≤ ‖γ‖₊ ^ (p - 1) * ‖γ‖₊ := by
                rw [nnnorm_p_eq' p hγ]; exact mul_le_mul_of_nonneg_left hsγ zero_le
            _ = ‖γ‖₊ ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
        exact absurd this (not_le.2 (pow_lt_pow_left₀ hγl zero_le hp.out.ne_zero))
    · exfalso
      have hmax : max s (s ^ (p - 1)) = s ^ (p - 1) :=
        max_eq_right (le_self_pow₀ hs1.le (by omega))
      rw [hmax] at hR
      have hlt : ‖(p : C)‖₊ * s ^ (p - 1) < s ^ p := by
        have hp1 : ‖(p : C)‖₊ < 1 := by
          rw [nnnorm_p_eq' p hγ]
          exact pow_lt_one₀ zero_le (hγl.trans_le hl1) (by omega)
        calc ‖(p : C)‖₊ * s ^ (p - 1) < 1 * s ^ (p - 1) :=
              mul_lt_mul_of_pos_right hp1 (pow_pos (zero_lt_one.trans hs1) _)
          _ ≤ s ^ p := by
              rw [one_mul]; exact pow_le_pow_right₀ hs1.le (by omega)
      have : v (z ^ p + R) = s ^ p := by
        rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hR.trans_lt hlt), map_pow]
      rw [hid, hrhs] at this
      have : T < s := by
        calc T ≤ 1 := hl1
          _ < s := hs1
      exact absurd ((pow_left_inj₀ zero_le zero_le hp.out.ne_zero).1 ‹T ^ p = s ^ p›)
        (ne_of_lt this)
  refine ⟨hs, ?_⟩
  have hl0 : l ≠ 0 := nnnorm_ne_zero_iff.1 hT0.ne'
  have hlE : algebraMap C E l ≠ 0 := by
    intro h; rw [← map_zero (algebraMap C E)] at h; exact hl0 ((algebraMap C E).injective h)
  have hvl : v (algebraMap C E l ^ p) = T ^ p := by rw [map_pow, hv]
  have hdiff : ((θ - H) / algebraMap C E l) ^ p - (F - H ^ p) / algebraMap C E l ^ p =
      ((θ ^ p - F) - R) / algebraMap C E l ^ p := by
    rw [div_pow]
    field_simp
    simp only [R, z]
    ring
  rw [hdiff, map_div₀, hvl]
  have hRT : v R < T ^ p := by
    have hmax : max (v z) (v z ^ (p - 1)) = T := by
      rw [hs]; exact max_eq_left (pow_le_of_le_one zero_le hl1 (by omega))
    rw [hmax] at hR
    calc v R ≤ ‖(p : C)‖₊ * T := hR
      _ < T ^ (p - 1) * T := mul_lt_mul_of_pos_right hpT hT0
      _ = T ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  have hnum : v ((θ ^ p - F) - R) < T ^ p := by
    rw [sub_eq_add_neg]
    exact (Valuation.map_add v _ _).trans_lt (max_lt hθ (by rw [Valuation.map_neg]; exact hRT))
  exact (div_lt_one (pow_pos hT0 p)).2 hnum

include hv hγ in
/-- **The Artin–Schreier case.** If `v(F - H^p) ≤ ‖γ‖^p` and `v(θ^p - F) < ‖γ‖^p` (`‖γ‖ < 1`),
then `w = (θ - H)/γ` has `v w ≤ 1` and `w^p - H^(p-1) w ≡ (F - H^p)/γ^p` modulo the maximal
ideal of `v`. -/
theorem valuation_as {θ H F : E} (hH : v H ≤ 1) (hγ1 : ‖γ‖₊ < 1) (hγ0 : γ ≠ 0)
    (hG : v (F - H ^ p) ≤ ‖γ‖₊ ^ p) (hθ : v (θ ^ p - F) < ‖γ‖₊ ^ p) :
    v (θ - H) ≤ ‖γ‖₊ ∧
      v (((θ - H) / algebraMap C E γ) ^ p - H ^ (p - 1) * ((θ - H) / algebraMap C E γ) -
        (F - H ^ p) / algebraMap C E γ ^ p) < 1 := by
  have hp2 := hp.out.two_le
  set z := θ - H
  set g := ‖γ‖₊
  have hg0 : 0 < g := nnnorm_pos.2 hγ0
  set R := (H + z) ^ p - H ^ p - z ^ p
  have hR := valuation_binom_le v hv p (z := z) hH
  have hid : z ^ p + R = (F - H ^ p) + (θ ^ p - F) := by
    simp only [R, z]; ring
  have hrhs : v ((F - H ^ p) + (θ ^ p - F)) ≤ g ^ p :=
    (Valuation.map_add v _ _).trans (max_le hG hθ.le)
  have hs : v z ≤ g := by
    by_contra hsg
    push Not at hsg
    set s := v z
    rcases le_or_gt s 1 with hs1 | hs1
    · have hmax : max s (s ^ (p - 1)) = s :=
        max_eq_left (pow_le_of_le_one zero_le hs1 (by omega))
      rw [hmax] at hR
      have hps : ‖(p : C)‖₊ < s ^ (p - 1) := by
        rw [nnnorm_p_eq' p hγ]; exact pow_lt_pow_left₀ hsg zero_le (by omega)
      have hdom : ‖(p : C)‖₊ * s < s ^ p := by
        calc ‖(p : C)‖₊ * s < s ^ (p - 1) * s :=
              mul_lt_mul_of_pos_right hps (hg0.trans hsg)
          _ = s ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
      have : v (z ^ p + R) = s ^ p := by
        rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hR.trans_lt hdom), map_pow]
      rw [hid] at this
      exact absurd (this ▸ hrhs) (not_le.2 (pow_lt_pow_left₀ hsg zero_le hp.out.ne_zero))
    · have hmax : max s (s ^ (p - 1)) = s ^ (p - 1) :=
        max_eq_right (le_self_pow₀ hs1.le (by omega))
      rw [hmax] at hR
      have hp1 : ‖(p : C)‖₊ < 1 := by
        rw [nnnorm_p_eq' p hγ]; exact pow_lt_one₀ zero_le hγ1 (by omega)
      have hlt : ‖(p : C)‖₊ * s ^ (p - 1) < s ^ p := by
        calc ‖(p : C)‖₊ * s ^ (p - 1) < 1 * s ^ (p - 1) :=
              mul_lt_mul_of_pos_right hp1 (pow_pos (zero_lt_one.trans hs1) _)
          _ ≤ s ^ p := by rw [one_mul]; exact pow_le_pow_right₀ hs1.le (by omega)
      have : v (z ^ p + R) = s ^ p := by
        rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hR.trans_lt hlt), map_pow]
      rw [hid] at this
      have h1 : g ^ p < s ^ p := pow_lt_pow_left₀ hsg zero_le hp.out.ne_zero
      exact absurd (this ▸ hrhs) (not_le.2 h1)
  refine ⟨hs, ?_⟩
  have hγE : algebraMap C E γ ≠ 0 := by
    intro h; rw [← map_zero (algebraMap C E)] at h; exact hγ0 ((algebraMap C E).injective h)
  have hz1 : v z ≤ 1 := hs.trans hγ1.le
  have hR2 := valuation_binom_two_le v hv p hH hz1
  have hγp : algebraMap C E γ ^ (p - 1) = -(p : E) := by
    rw [← map_pow, hγ, map_neg, map_natCast]
  have hdiff : (z / algebraMap C E γ) ^ p - H ^ (p - 1) * (z / algebraMap C E γ) -
      (F - H ^ p) / algebraMap C E γ ^ p =
      ((θ ^ p - F) - ((H + z) ^ p - H ^ p - z ^ p - (p : E) * H ^ (p - 1) * z)) /
        algebraMap C E γ ^ p := by
    have hγpow : algebraMap C E γ ^ p = algebraMap C E γ ^ (p - 1) * algebraMap C E γ := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
    rw [div_pow, eq_div_iff (pow_ne_zero _ hγE)]
    field_simp
    rw [hγpow, hγp]
    simp only [z]
    ring
  rw [hdiff, map_div₀, map_pow, hv]
  have hR2' : v ((H + z) ^ p - H ^ p - z ^ p - (p : E) * H ^ (p - 1) * z) < g ^ p := by
    calc _ ≤ ‖(p : C)‖₊ * v z ^ 2 := hR2
      _ ≤ g ^ (p - 1) * g ^ 2 := by
          rw [nnnorm_p_eq' p hγ]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le hs _)
            zero_le
      _ = g ^ (p + 1) := by rw [← pow_add]; congr 1; omega
      _ < g ^ p := pow_lt_pow_right_of_lt_one₀ hg0 hγ1 (by omega)
  have hnum : v ((θ ^ p - F) - ((H + z) ^ p - H ^ p - z ^ p - (p : E) * H ^ (p - 1) * z)) <
      g ^ p := by
    rw [sub_eq_add_neg]
    exact (Valuation.map_add v _ _).trans_lt (max_lt hθ (by rw [Valuation.map_neg]; exact hR2'))
  exact (div_lt_one (pow_pos hg0 p)).2 hnum

end KummerResidue

end SemistableReduction
