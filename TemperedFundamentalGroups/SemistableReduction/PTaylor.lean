/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Formal `p`-Taylor expansions

Blueprint §9.10, L4 (K3): Matignon's `p`-Taylor expansion in the form of Arzdorf's thesis
(Def. 2.9, Prop. 2.12), over the coefficient field `C` itself (algebraically closed, with a
non-archimedean norm and `‖p‖ < 1`; no completeness and no field extensions are needed).

For a power series `φ` and `r : ℝ≥0` write `Bnd φ r` if all coefficients have norm `≤ r`.

* `Bnd.add`, `Bnd.mul`, `Bnd.pow`, `Bnd.sum`: bounds of sums and (Cauchy) products;
* `frob φ = Σ (coeff j φ)^p X^(p j)` and **`bnd_pow_sub_frob`**: `φ^p - frob φ` has coefficients
  of norm `≤ ‖p‖ r^p` if `Bnd φ r` (the `p`-th power is additive modulo `p`; truncate and use
  `p ∣ binom(p, k)`);
* `bnd_add_pow_sub`: `(h + δ)^p - h^p - δ^p` has coefficients of norm `≤ ‖p‖ r` if `Bnd h 1`,
  `Bnd δ r`, `r ≤ 1`;
* **`exists_pTaylor`**: for `f` with integral coefficients and every level `n` there is `h` with
  integral coefficients such that `f - h^p` has constant coefficient `0` and all coefficients of
  index divisible by `p` of norm `≤ pBound p n`, where `pBound p 0 = ‖p‖`,
  `pBound p (n + 1) = ‖p‖ · pBound p n ^ (1/p)`, i.e. `pBound p n = ‖p‖^(1 + 1/p + ⋯ + 1/pⁿ)`.
-/

open PowerSeries NNReal

namespace SemistableReduction

namespace PTaylor

variable {C : Type*} [NormedField C]

/-- All coefficients of `φ` have norm at most `r`. -/
def Bnd (φ : PowerSeries C) (r : ℝ≥0) : Prop := ∀ i, ‖coeff i φ‖₊ ≤ r

namespace Bnd

lemma mono {φ : PowerSeries C} {r s : ℝ≥0} (h : Bnd φ r) (hrs : r ≤ s) : Bnd φ s :=
  fun i ↦ (h i).trans hrs

lemma zero (r : ℝ≥0) : Bnd (0 : PowerSeries C) r := fun i ↦ by simp

lemma add [IsUltrametricDist C] {φ ψ : PowerSeries C} {r : ℝ≥0} (hφ : Bnd φ r)
    (hψ : Bnd ψ r) : Bnd (φ + ψ) r :=
  fun i ↦ by
    rw [map_add]
    exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le (hφ i) (hψ i))

lemma neg {φ : PowerSeries C} {r : ℝ≥0} (hφ : Bnd φ r) : Bnd (-φ) r :=
  fun i ↦ by rw [map_neg, nnnorm_neg]; exact hφ i

lemma sub [IsUltrametricDist C] {φ ψ : PowerSeries C} {r : ℝ≥0} (hφ : Bnd φ r)
    (hψ : Bnd ψ r) : Bnd (φ - ψ) r := by
  rw [sub_eq_add_neg]
  exact hφ.add hψ.neg

lemma mul [IsUltrametricDist C] {φ ψ : PowerSeries C} {r s : ℝ≥0} (hφ : Bnd φ r)
    (hψ : Bnd ψ s) : Bnd (φ * ψ) (r * s) :=
  fun i ↦ by
    rw [coeff_mul]
    refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun x _ ↦ ?_
    rw [nnnorm_mul]
    exact mul_le_mul' (hφ _) (hψ _)

lemma pow [IsUltrametricDist C] {φ : PowerSeries C} {r : ℝ≥0} (hφ : Bnd φ r) (n : ℕ) :
    Bnd (φ ^ n) (r ^ n) := by
  induction n with
  | zero =>
    intro i
    rw [pow_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hφ

lemma sum [IsUltrametricDist C] {ι : Type*} (s : Finset ι) {φ : ι → PowerSeries C} {r : ℝ≥0}
    (h : ∀ i ∈ s, Bnd (φ i) r) : Bnd (∑ i ∈ s, φ i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

lemma smul_nat {φ : PowerSeries C} {r : ℝ≥0} (hφ : Bnd φ r) (n : ℕ) :
    Bnd ((n : PowerSeries C) * φ) (‖(n : C)‖₊ * r) := fun i ↦ by
  rw [← map_natCast (PowerSeries.C (R := C)), coeff_C_mul, nnnorm_mul]
  exact mul_le_mul_right (hφ i) _

lemma monomial {c : C} {r : ℝ≥0} (hc : ‖c‖₊ ≤ r) (n : ℕ) :
    Bnd (PowerSeries.monomial n c) r := fun i ↦ by
  rw [coeff_monomial]
  split_ifs
  · exact hc
  · simp

end Bnd

variable (p : ℕ) [hp : Fact p.Prime]

/-- `binom(p, k)` is divisible by `p` for `0 < k < p`, hence has norm `≤ ‖p‖`. -/
lemma nnnorm_choose_le [IsUltrametricDist C] {k : ℕ} (hk0 : k ≠ 0) (hkp : k < p) :
    ‖(p.choose k : C)‖₊ ≤ ‖(p : C)‖₊ := by
  obtain ⟨m, hm⟩ := hp.out.dvd_choose_self hk0 hkp
  rw [hm, Nat.cast_mul, nnnorm_mul]
  refine mul_le_of_le_one_right' ?_
  exact IsUltrametricDist.nnnorm_natCast_le_one C m

/-- **Binomial estimate.** `(x + y)^p - x^p - y^p = Σ_{0<k<p} binom(p,k) x^k y^(p-k)` has
coefficients of norm `≤ ‖p‖ t` if every `x^k y^(p-k)`, `0 < k < p`, is bounded by `t`. -/
lemma bnd_add_pow_sub_pow [IsUltrametricDist C] {x y : PowerSeries C} {t : ℝ≥0}
    (h : ∀ k, 0 < k → k < p → Bnd (x ^ k * y ^ (p - k)) t) :
    Bnd ((x + y) ^ p - x ^ p - y ^ p) (‖(p : C)‖₊ * t) := by
  have hsum : (x + y) ^ p - x ^ p - y ^ p =
      ∑ k ∈ (Finset.range (p + 1)).erase 0 |>.erase p,
        x ^ k * y ^ (p - k) * (p.choose k : PowerSeries C) := by
    rw [add_pow, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 (Nat.lt_succ_self p)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hp.out.ne_zero.symm, Finset.mem_range.2
        (Nat.succ_pos p)⟩)]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero,
      Nat.choose_zero_right,
      one_mul, Nat.sub_zero]
    rw [Finset.erase_right_comm]
    ring
  rw [hsum]
  refine Bnd.sum _ fun k hk ↦ ?_
  obtain ⟨hkp, hk'⟩ := Finset.mem_erase.1 hk
  obtain ⟨hk0, hk⟩ := Finset.mem_erase.1 hk'
  have hklt : k < p := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hkp
  rw [mul_comm]
  have := (h k (Nat.pos_of_ne_zero hk0) hklt).smul_nat (p.choose k)
  exact this.mono (mul_le_mul_of_nonneg_right (nnnorm_choose_le p hk0 hklt) zero_le)

/-- The Frobenius twist `Σ (coeff j φ)^p X^(p j)`. -/
noncomputable def frob (φ : PowerSeries C) : PowerSeries C :=
  mk fun k ↦ if p ∣ k then coeff (k / p) φ ^ p else 0

omit hp in
lemma coeff_frob (φ : PowerSeries C) (k : ℕ) :
    coeff k (frob p φ) = if p ∣ k then coeff (k / p) φ ^ p else 0 :=
  coeff_mk _ _

lemma coeff_frob_mul (φ : PowerSeries C) (j : ℕ) : coeff (p * j) (frob p φ) = coeff j φ ^ p := by
  rw [coeff_frob, if_pos (dvd_mul_right p j), Nat.mul_div_cancel_left _ hp.out.pos]

lemma bnd_sum_pow_sub [IsUltrametricDist C] {c : ℕ → C} {r : ℝ≥0} (hc : ∀ j, ‖c j‖₊ ≤ r)
    (N : ℕ) :
    Bnd ((∑ j ∈ Finset.range N, PowerSeries.monomial j (c j)) ^ p -
      ∑ j ∈ Finset.range N, PowerSeries.monomial (p * j) (c j ^ p)) (‖(p : C)‖₊ * r ^ p) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_pow hp.out.ne_zero, sub_zero]
    exact Bnd.zero _
  | succ N ih =>
    set φ := ∑ j ∈ Finset.range N, PowerSeries.monomial j (c j)
    set m := PowerSeries.monomial N (c N)
    have hφ : Bnd φ r := Bnd.sum _ fun j _ ↦ Bnd.monomial (hc j) j
    have hm : Bnd m r := Bnd.monomial (hc N) N
    have hdecomp : (φ + m) ^ p - (∑ j ∈ Finset.range N, PowerSeries.monomial (p * j) (c j ^ p) +
        PowerSeries.monomial (p * N) (c N ^ p)) =
        (φ ^ p - ∑ j ∈ Finset.range N, PowerSeries.monomial (p * j) (c j ^ p)) +
          ((φ + m) ^ p - φ ^ p - m ^ p) := by
      rw [show m ^ p = PowerSeries.monomial (p * N) (c N ^ p) from monomial_pow _ _ _]
      ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hdecomp]
    refine ih.add (bnd_add_pow_sub_pow p fun k _ hkp ↦ ?_)
    have := (hφ.pow k).mul (hm.pow (p - k))
    rwa [← pow_add, Nat.add_sub_cancel' hkp.le] at this

/-- **The `p`-th power is additive modulo `p`.** If `Bnd φ r`, then `φ^p - frob φ` has
coefficients of norm `≤ ‖p‖ r^p`. -/
theorem bnd_pow_sub_frob [IsUltrametricDist C] {φ : PowerSeries C} {r : ℝ≥0} (hφ : Bnd φ r) :
    Bnd (φ ^ p - frob p φ) (‖(p : C)‖₊ * r ^ p) := by
  intro i
  set N := i + 1
  set ψ : PowerSeries C := ∑ j ∈ Finset.range N, PowerSeries.monomial j (coeff j φ)
  have hψ : ψ = (trunc N φ : PowerSeries C) := by
    ext k
    rw [Polynomial.coeff_coe, coeff_trunc, map_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq]
    exact if_congr Finset.mem_range rfl rfl
  have hpow : coeff i (φ ^ p) = coeff i (ψ ^ p) := by
    have h := congrArg (fun q : Polynomial C ↦ q.coeff i) (trunc_trunc_pow φ N p)
    simp only [coeff_trunc] at h
    rw [if_pos (Nat.lt_succ_self i), if_pos (Nat.lt_succ_self i)] at h
    rw [hψ, h]
  have hfrob : coeff i (frob p φ) =
      coeff i (∑ j ∈ Finset.range N, PowerSeries.monomial (p * j) (coeff j φ ^ p)) := by
    rw [coeff_frob, map_sum]
    simp only [coeff_monomial]
    split_ifs with hdiv
    · obtain ⟨q, rfl⟩ := hdiv
      rw [Nat.mul_div_cancel_left _ hp.out.pos, Finset.sum_eq_single q]
      · rw [if_pos rfl]
      · intro j _ hjq
        rw [if_neg]
        intro h
        exact hjq (Nat.eq_of_mul_eq_mul_left hp.out.pos h).symm
      · intro hq
        exfalso
        refine hq (Finset.mem_range.2 (Nat.lt_succ_of_le ?_))
        exact Nat.le_mul_of_pos_left q hp.out.pos
    · refine (Finset.sum_eq_zero fun j _ ↦ ?_).symm
      rw [if_neg]
      rintro rfl
      exact hdiv (dvd_mul_right p j)
  rw [map_sub, hpow, hfrob, ← map_sub]
  exact bnd_sum_pow_sub p (fun j ↦ hφ j) N i

/-! ### The `p`-Taylor expansion -/

/-- The bounds `‖p‖^(1 + 1/p + ⋯ + 1/pⁿ)` of the `p`-coefficients at level `n`. -/
noncomputable def pBound (C : Type*) [NormedField C] (p : ℕ) : ℕ → ℝ≥0
  | 0 => ‖(p : C)‖₊
  | n + 1 => ‖(p : C)‖₊ * pBound C p n ^ ((p : ℝ)⁻¹)

omit hp in
lemma pBound_le_one [IsUltrametricDist C] (n : ℕ) : pBound C p n ≤ 1 := by
  have hp1 : ‖(p : C)‖₊ ≤ 1 := IsUltrametricDist.nnnorm_natCast_le_one C p
  induction n with
  | zero => exact hp1
  | succ n ih =>
    exact mul_le_one' hp1 (NNReal.rpow_le_one ih (inv_nonneg.2 (Nat.cast_nonneg p)))

/-- **One step of the `p`-Taylor algorithm.** If the coefficients of `a = f - h^p` of index
divisible by `p` have norm `≤ B ≤ 1`, adding `δ = Σ a_{pj}^(1/p) X^j` to `h` yields
`f - (h + δ)^p` with `p`-coefficients of norm `≤ ‖p‖ B^(1/p)` and vanishing constant term
(provided `h = 0` or the constant term of `a` vanishes). -/
theorem exists_step [IsUltrametricDist C] [IsAlgClosed C] {f h : PowerSeries C} {B : ℝ≥0}
    (hB : B ≤ 1) (hh : Bnd h 1) (ha : ∀ j, ‖coeff (p * j) (f - h ^ p)‖₊ ≤ B)
    (h0 : h = 0 ∨ coeff 0 (f - h ^ p) = 0) :
    ∃ h' : PowerSeries C, Bnd h' 1 ∧ coeff 0 (f - h' ^ p) = 0 ∧
      ∀ j, ‖coeff (p * j) (f - h' ^ p)‖₊ ≤ ‖(p : C)‖₊ * B ^ ((p : ℝ)⁻¹) := by
  classical
  set a := f - h ^ p
  have hp0 : p ≠ 0 := hp.out.ne_zero
  -- `p`-th roots of the `p`-coefficients
  have hroot : ∀ j, ∃ b : C, b ^ p = coeff (p * j) a := fun j ↦
    IsAlgClosed.exists_pow_nat_eq _ hp.out.pos
  choose b hb using hroot
  set δ : PowerSeries C := mk b
  set B' : ℝ≥0 := B ^ ((p : ℝ)⁻¹)
  have hB'1 : B' ≤ 1 := NNReal.rpow_le_one hB (inv_nonneg.2 (Nat.cast_nonneg p))
  have hBB' : B ≤ B' := by
    have h1 : B' ^ p = B := NNReal.rpow_inv_natCast_pow B hp0
    calc B = B' ^ p := h1.symm
      _ ≤ B' := pow_le_of_le_one zero_le hB'1 hp0
  have hδ : Bnd δ B' := fun j ↦ by
    rw [coeff_mk]
    have h1 : ‖b j‖₊ ^ p ≤ B := by rw [← nnnorm_pow, hb]; exact ha j
    calc ‖b j‖₊ = (‖b j‖₊ ^ p) ^ ((p : ℝ)⁻¹) := (NNReal.pow_rpow_inv_natCast _ hp0).symm
      _ ≤ B' := NNReal.rpow_le_rpow h1 (inv_nonneg.2 (Nat.cast_nonneg p))
  have hfrob : ∀ j, coeff (p * j) (frob p δ) = coeff (p * j) a := fun j ↦ by
    rw [coeff_frob_mul, coeff_mk, hb]
  set R := (h + δ) ^ p - h ^ p - δ ^ p
  have hR : Bnd R (‖(p : C)‖₊ * B') := bnd_add_pow_sub_pow p fun k hk hkp ↦ by
    have := (hh.pow k).mul (hδ.pow (p - k))
    refine this.mono ?_
    rw [one_pow, one_mul]
    exact pow_le_of_le_one zero_le hB'1 (by omega)
  have hF : Bnd (δ ^ p - frob p δ) (‖(p : C)‖₊ * B') :=
    (bnd_pow_sub_frob p hδ).mono (mul_le_mul_of_nonneg_left
      ((NNReal.rpow_inv_natCast_pow B hp0).le.trans hBB') zero_le)
  have hdecomp : f - (h + δ) ^ p = (a - frob p δ) - (δ ^ p - frob p δ) - R := by
    simp only [a, R]
    ring
  refine ⟨h + δ, hh.add (hδ.mono hB'1), ?_, fun j ↦ ?_⟩
  · have hb0 : b 0 ^ p = coeff 0 a := by simpa using hb 0
    have hδ0 : coeff 0 δ = b 0 := coeff_mk _ _
    have ha0' : coeff 0 a = coeff 0 f - coeff 0 h ^ p := by
      simp only [a, map_sub, coeff_zero_eq_constantCoeff_apply, map_pow]
    rw [map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_pow,
      map_add, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_zero_eq_constantCoeff_apply, hδ0]
    rcases h0 with rfl | ha0
    · rw [map_zero, zero_add, hb0, ha0', map_zero, zero_pow hp0, sub_zero, sub_self]
    · have hb00 : b 0 = 0 := pow_eq_zero_iff hp0 |>.1 (hb0.trans ha0)
      rw [hb00, add_zero, ← ha0', ha0]
  · rw [hdecomp, map_sub, map_sub, map_sub, hfrob, sub_self, zero_sub]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [nnnorm_neg]
      exact hF _
    · rw [nnnorm_neg]
      exact hR _

/-- **Formal `p`-Taylor expansion** (Matignon; Arzdorf, Prop. 2.12). For `f` with coefficients
of norm `≤ 1` and every level `n` there is `h` with coefficients of norm `≤ 1` such that
`f - h^p` has constant coefficient `0` and all coefficients of index divisible by `p` of norm
`≤ pBound C p n = ‖p‖^(1 + 1/p + ⋯ + 1/pⁿ)`. -/
theorem exists_pTaylor [IsUltrametricDist C] [IsAlgClosed C] {f : PowerSeries C} (hf : Bnd f 1)
    (n : ℕ) : ∃ h : PowerSeries C, Bnd h 1 ∧ coeff 0 (f - h ^ p) = 0 ∧
      ∀ j, ‖coeff (p * j) (f - h ^ p)‖₊ ≤ pBound C p n := by
  induction n with
  | zero =>
    obtain ⟨h, hh, h0, hj⟩ := exists_step p (f := f) (h := 0) le_rfl (Bnd.zero 1)
      (fun j ↦ by rw [zero_pow hp.out.ne_zero, sub_zero]; exact hf _) (Or.inl rfl)
    refine ⟨h, hh, h0, fun j ↦ (hj j).trans_eq ?_⟩
    rw [NNReal.one_rpow, mul_one]
    rfl
  | succ n ih =>
    obtain ⟨h, hh, h0, hj⟩ := ih
    exact exists_step p (pBound_le_one p n) hh hj (Or.inr h0)

end PTaylor

end SemistableReduction
