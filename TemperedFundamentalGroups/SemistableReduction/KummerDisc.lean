/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.PTaylor

/-!
# `p`-th power approximations of power series

Blueprint §9.10, L4 (K2): Arzdorf's recognition of best approximations (Lemma 2.7, Remark 2.8),
for power series over the coefficient field `C` (no discreteness, no attained suprema).

* **`not_better`**: let `f - h^p` have all coefficients of norm `≤ M`, with `‖p‖^p < M^(p-1)`
  (i.e. `M > ‖p‖^(p/(p-1))`, below the Artin–Schreier threshold), and coefficient of norm exactly
  `M` at an index `m` prime to `p`. Then no `h'` with integral coefficients improves this: it is
  impossible that all coefficients of `f - h'^p` have norm `≤ M` and the one at `m` has norm
  `< M`. Proof: `g = h'^p - h^p = frob Δ + E` with `Δ = h' - h`, `‖E‖ ≤ ‖p‖ s` (`s` bounding the
  coefficients of `Δ`, PTaylor's binomial and Frobenius estimates); at the index `m` (not a
  multiple of `p`) this forces `M ≤ ‖p‖ s`, hence `s^p > max (‖p‖ s) M`, and at an index `p j`
  with `‖Δⱼ‖^p > max (‖p‖ s) M` the coefficient of `g`, hence one of `f - h'^p`, exceeds `M`.
-/

open PowerSeries NNReal

namespace SemistableReduction

namespace KummerDisc

open PTaylor

variable {C : Type*} [NormedField C] [IsUltrametricDist C] (p : ℕ) [hp : Fact p.Prime]

/-- `h'^p - h^p = frob (h' - h) + E` with `E` bounded by `‖p‖ s` if `h` and `h' - h` are bounded
by `1` and `s ≤ 1`. -/
lemma bnd_pow_sub_pow_sub_frob {h Δ : PowerSeries C} {s : ℝ≥0} (hh : Bnd h 1) (hΔ : Bnd Δ s)
    (hs : s ≤ 1) : Bnd ((h + Δ) ^ p - h ^ p - frob p Δ) (‖(p : C)‖₊ * s) := by
  have h1 : Bnd ((h + Δ) ^ p - h ^ p - Δ ^ p) (‖(p : C)‖₊ * s) :=
    bnd_add_pow_sub_pow p fun k hk hkp ↦ by
      have := (hh.pow k).mul (hΔ.pow (p - k))
      refine this.mono ?_
      rw [one_pow, one_mul]
      exact pow_le_of_le_one zero_le hs (by omega)
  have h2 : Bnd (Δ ^ p - frob p Δ) (‖(p : C)‖₊ * s) :=
    (bnd_pow_sub_frob p hΔ).mono (mul_le_mul_of_nonneg_left
      (pow_le_of_le_one zero_le hs hp.out.ne_zero) zero_le)
  have hdecomp : (h + Δ) ^ p - h ^ p - frob p Δ =
      ((h + Δ) ^ p - h ^ p - Δ ^ p) + (Δ ^ p - frob p Δ) := by ring
  rw [hdecomp]
  exact h1.add h2

lemma nnnorm_sub_eq_of_lt {x y : C} (h : ‖y‖₊ < ‖x‖₊) : ‖x - y‖₊ = ‖x‖₊ := by
  apply le_antisymm
  · rw [sub_eq_add_neg]
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [nnnorm_neg]
    exact h.le
  · by_contra! hlt
    have : ‖x‖₊ ≤ max ‖x - y‖₊ ‖y‖₊ := by
      calc ‖x‖₊ = ‖(x - y) + y‖₊ := by rw [sub_add_cancel]
        _ ≤ _ := IsUltrametricDist.nnnorm_add_le_max _ _
    exact absurd this (not_le.2 (max_lt hlt h))

/-- **Recognition of best approximations** (Arzdorf, Lemma 2.7). If all coefficients of
`f - h^p` have norm `≤ M`, `‖p‖^p < M^(p-1)`, and the coefficient at an index `m` prime to `p`
has norm `M`, then no `h'` with coefficients of norm `≤ 1` makes all coefficients of `f - h'^p`
of norm `≤ M` and the one at `m` of norm `< M`. -/
theorem not_better {f h h' : PowerSeries C} {M : ℝ≥0} {m : ℕ} (hM : ‖(p : C)‖₊ ^ p < M ^ (p - 1))
    (hm : ¬ p ∣ m) (hh : Bnd h 1) (hh' : Bnd h' 1) (hfh : ∀ i, ‖coeff i (f - h ^ p)‖₊ ≤ M)
    (hfm : ‖coeff m (f - h ^ p)‖₊ = M) :
    ¬ ((∀ i, ‖coeff i (f - h' ^ p)‖₊ ≤ M) ∧ ‖coeff m (f - h' ^ p)‖₊ < M) := by
  rintro ⟨hall, hlt⟩
  have hp0 := hp.out.ne_zero
  set Δ := h' - h
  have hΔ : Bnd Δ 1 := hh'.sub hh
  have hbdd : BddAbove (Set.range fun i ↦ ‖coeff i Δ‖₊) := ⟨1, by rintro _ ⟨i, rfl⟩; exact hΔ i⟩
  set s : ℝ≥0 := ⨆ i, ‖coeff i Δ‖₊
  have hs1 : s ≤ 1 := ciSup_le hΔ
  have hΔs : Bnd Δ s := fun i ↦ le_ciSup hbdd i
  set g := h' ^ p - h ^ p
  have hg : g = (f - h ^ p) - (f - h' ^ p) := by ring
  have hgM : ∀ i, ‖coeff i g‖₊ ≤ M := fun i ↦ by
    rw [hg, map_sub]
    exact (Bnd.sub (C := C) (fun i ↦ hfh i) (fun i ↦ hall i)) i
  have hgm : ‖coeff m g‖₊ = M := by
    rw [hg, map_sub, nnnorm_sub_eq_of_lt (hfm ▸ hlt), hfm]
  have hE := bnd_pow_sub_pow_sub_frob p hh hΔs hs1
  rw [show h + Δ = h' by ring] at hE
  -- at `m` the Frobenius twist vanishes
  have hfrobm : coeff m (frob p Δ) = 0 := by rw [coeff_frob, if_neg hm]
  have hMs : M ≤ ‖(p : C)‖₊ * s := by
    have := hE m
    rw [map_sub, hfrobm, sub_zero] at this
    exact hgm ▸ this
  have hM0 : 0 < M := by
    rcases eq_or_ne M 0 with h0 | h0
    · rw [h0, zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt)] at hM
      exact absurd hM (not_lt.2 zero_le)
    · exact pos_iff_ne_zero.2 h0
  have hps0 : 0 < ‖(p : C)‖₊ * s := hM0.trans_le hMs
  have hs0 : 0 < s := pos_of_mul_pos_right hps0 zero_le
  -- `s^(p-1) > ‖p‖`
  have hsp : ‖(p : C)‖₊ * s < s ^ p := by
    have h1 : ‖(p : C)‖₊ ^ (p - 1) * ‖(p : C)‖₊ < ‖(p : C)‖₊ ^ (p - 1) * s ^ (p - 1) := by
      calc ‖(p : C)‖₊ ^ (p - 1) * ‖(p : C)‖₊ = ‖(p : C)‖₊ ^ p := by
            rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
        _ < M ^ (p - 1) := hM
        _ ≤ (‖(p : C)‖₊ * s) ^ (p - 1) := pow_le_pow_left₀ zero_le hMs _
        _ = _ := mul_pow _ _ _
    have h2 : ‖(p : C)‖₊ < s ^ (p - 1) :=
      lt_of_mul_lt_mul_left h1 zero_le
    calc ‖(p : C)‖₊ * s < s ^ (p - 1) * s := mul_lt_mul_of_pos_right h2 hs0
      _ = s ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  -- a coefficient of `Δ` whose `p`-th power exceeds `‖p‖ s`
  obtain ⟨j, hj⟩ : ∃ j, ‖(p : C)‖₊ * s < ‖coeff j Δ‖₊ ^ p := by
    by_contra! H
    have : s ^ p ≤ ‖(p : C)‖₊ * s := by
      have hle : s ≤ (‖(p : C)‖₊ * s) ^ ((p : ℝ)⁻¹) := ciSup_le fun i ↦ by
        calc ‖coeff i Δ‖₊ = (‖coeff i Δ‖₊ ^ p) ^ ((p : ℝ)⁻¹) :=
              (NNReal.pow_rpow_inv_natCast _ hp0).symm
          _ ≤ _ := NNReal.rpow_le_rpow (H i) (inv_nonneg.2 (Nat.cast_nonneg p))
      calc s ^ p ≤ ((‖(p : C)‖₊ * s) ^ ((p : ℝ)⁻¹)) ^ p := pow_le_pow_left₀ zero_le hle p
        _ = _ := NNReal.rpow_inv_natCast_pow _ hp0
    exact absurd hsp (not_lt.2 this)
  -- the coefficient of `g` at `p j`
  have hgpj : ‖coeff (p * j) g‖₊ = ‖coeff j Δ‖₊ ^ p := by
    have := hE (p * j)
    rw [map_sub, coeff_frob_mul] at this
    have h1 : ‖coeff (p * j) g - coeff j Δ ^ p‖₊ < ‖coeff j Δ ^ p‖₊ := by
      rw [nnnorm_pow]
      exact this.trans_lt hj
    calc ‖coeff (p * j) g‖₊ = ‖coeff j Δ ^ p - (coeff j Δ ^ p - coeff (p * j) g)‖₊ := by
          rw [sub_sub_cancel]
      _ = ‖coeff j Δ ^ p‖₊ := nnnorm_sub_eq_of_lt (by rwa [← nnnorm_neg, neg_sub])
      _ = _ := nnnorm_pow _ _
  have := hgM (p * j)
  rw [hgpj] at this
  exact absurd (this.trans hMs) (not_le.2 hj)

end KummerDisc

end SemistableReduction
