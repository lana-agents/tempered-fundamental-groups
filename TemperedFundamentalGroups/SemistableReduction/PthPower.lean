/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.HenselComplete

/-!
# `p`-th roots of `1`-units in complete fields of mixed characteristic

Blueprint §9.4, F4 (Kuhlmann, *Elimination of ramification I*, §2.2: Lemmas 2.10, 2.11 and
Corollary 2.12). Let `K` be a complete non-archimedean normed field, `p` a prime with
`(p : K) ≠ 0`, and `γ ∈ K` with `γ ^ (p - 1) = -p` (Kuhlmann's `C`), so `‖γ‖ ^ (p - 1) = ‖p‖`.

* `exists_root`: Hensel's lemma in normed form (from `HenselComplete.henselianLocalRing`).
* `norm_add_pow_sub_le`, `norm_one_add_pow_sub_le`: the middle binomial terms of `(x + y) ^ p`
  are divisible by `p`.
* `exists_pow_eq_one_add` (Lemma 2.11): `1 + b` is a `p`-th power if `‖b‖ < ‖γ‖ ^ p`
  (i.e. `v b > p v(p) / (p - 1)`). Proof: the substitution `X = γ Y + 1` turns `X ^ p - (1 + b)`
  into a polynomial with reduction `Y ^ p - Y`, and Hensel's lemma applies at `Y = 0`.
* `exists_eq_mul_pow` (Corollary 2.12 a): if `u` is a `1`-unit and `‖v - u‖ < ‖γ‖ ^ p`, then
  `v ∈ u · K ^ p`.
* `exists_eq_mul_pow_of_pow` (Corollary 2.12 d): if `‖b‖ ≤ ‖γ‖` and `‖c‖ ^ p < ‖p‖`, then
  `1 + b + c ^ p ∈ (1 + b - p c) · K ^ p`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

namespace PthPower

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => HenselComplete.integers K

/-- A polynomial with coefficients of norm `≤ 1` lifts to the ring of integers. -/
lemma exists_map_eq (f : K[X]) (hf : ∀ i, ‖f.coeff i‖ ≤ 1) :
    ∃ g : 𝒪[X], g.map (algebraMap 𝒪 K) = f := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  exact fun n ↦ ⟨⟨f.coeff n, (HenselComplete.mem_integers_iff _).2 (hf n)⟩, rfl⟩

/-- **Hensel's lemma** for a complete non-archimedean field, in normed form: a monic `f` with
coefficients of norm `≤ 1`, and `a` with `‖a‖ ≤ 1`, `‖f(a)‖ < 1`, `‖f'(a)‖ = 1`, has a root `x`
with `‖x - a‖ < 1`. -/
theorem exists_root [CompleteSpace K] {f : K[X]} (hm : f.Monic) (hf : ∀ i, ‖f.coeff i‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) (h1 : ‖f.eval a‖ < 1) (h2 : ‖f.derivative.eval a‖ = 1) :
    ∃ x, f.eval x = 0 ∧ ‖x - a‖ < 1 := by
  have := HenselComplete.henselianLocalRing (K := K)
  obtain ⟨g, rfl⟩ := exists_map_eq f hf
  have hgm : g.Monic := monic_of_injective Subtype.val_injective hm
  have hev (z : 𝒪) : (g.map (algebraMap 𝒪 K)).eval (z : K) = ((g.eval z : 𝒪) : K) := by
    rw [eval_map]
    exact eval₂_at_apply (algebraMap 𝒪 K) z
  have hder (z : 𝒪) :
      (g.map (algebraMap 𝒪 K)).derivative.eval (z : K) = ((g.derivative.eval z : 𝒪) : K) := by
    rw [derivative_map, eval_map]
    exact eval₂_at_apply (algebraMap 𝒪 K) z
  set a' : 𝒪 := ⟨a, (HenselComplete.mem_integers_iff a).2 ha⟩
  obtain ⟨x, hx, hxa⟩ := HenselianLocalRing.is_henselian g hgm a'
    ((HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).2 (by rw [← hev]; exact h1))
    ((HenselComplete.isUnit_iff_norm_eq_one _).2 (by rw [← hder]; exact h2))
  refine ⟨x, ?_, ?_⟩
  · rw [hev, hx.eq_zero]
    rfl
  · have := (HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).1 hxa
    simpa [a'] using this

/-- The ultrametric inequality for differences. -/
lemma norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)

section Binomial

variable {p : ℕ}

/-- The middle binomial coefficients of a prime `p` are divisible by `p`. -/
lemma norm_choose_le (hp : p.Prime) {i : ℕ} (h0 : i ≠ 0) (hi : i < p) :
    ‖(p.choose i : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨m, hm⟩ := hp.dvd_choose_self h0 hi
  rw [hm, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K m)

/-- `‖(x + y) ^ p - x ^ p - y ^ p‖ ≤ ‖p‖ ‖x‖ ‖y‖` for `‖x‖, ‖y‖ ≤ 1`. -/
lemma norm_add_pow_sub_le (hp : p.Prime) {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(x + y) ^ p - x ^ p - y ^ p‖ ≤ ‖(p : K)‖ * (‖x‖ * ‖y‖) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpmem : p ∈ Finset.range (p + 1) := Finset.mem_range.2 (Nat.lt_succ_self p)
  have h0mem : 0 ∈ (Finset.range (p + 1)).erase p :=
    Finset.mem_erase.2 ⟨Ne.symm hp0, Finset.mem_range.2 (Nat.succ_pos p)⟩
  have key : (x + y) ^ p - x ^ p - y ^ p =
      ∑ m ∈ ((Finset.range (p + 1)).erase p).erase 0, x ^ m * y ^ (p - m) * (p.choose m : K) := by
    rw [add_pow, ← Finset.add_sum_erase _ _ hpmem, ← Finset.add_sum_erase _ _ h0mem]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, Nat.sub_zero,
      one_mul, Nat.choose_zero_right]
    ring
  rw [key]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m hm ↦ ?_
  obtain ⟨hm0, hm'⟩ := Finset.mem_erase.1 hm
  obtain ⟨hmp, hm''⟩ := Finset.mem_erase.1 hm'
  have hmp' : m < p := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm'')) hmp
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 : ‖x‖ ^ m ≤ ‖x‖ := pow_le_of_le_one (norm_nonneg _) hx hm0
  have h2 : ‖y‖ ^ (p - m) ≤ ‖y‖ :=
    pow_le_of_le_one (norm_nonneg _) hy (Nat.sub_ne_zero_of_lt hmp')
  calc ‖x‖ ^ m * ‖y‖ ^ (p - m) * ‖(p.choose m : K)‖ ≤ ‖x‖ * ‖y‖ * ‖(p : K)‖ :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (norm_nonneg _))
          (norm_choose_le hp hm0 hmp') (norm_nonneg _) (by positivity)
    _ = ‖(p : K)‖ * (‖x‖ * ‖y‖) := by ring

/-- `‖(1 + c) ^ p - 1 - c ^ p - p c‖ ≤ ‖p‖ ‖c‖ ^ 2` for `‖c‖ ≤ 1`. -/
lemma norm_one_add_pow_sub_le (hp : p.Prime) {c : K} (hc : ‖c‖ ≤ 1) :
    ‖(1 + c) ^ p - 1 - c ^ p - p * c‖ ≤ ‖(p : K)‖ * ‖c‖ ^ 2 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : 1 ≠ p := (Nat.Prime.one_lt hp).ne
  have hpmem : p ∈ Finset.range (p + 1) := Finset.mem_range.2 (Nat.lt_succ_self p)
  have h0mem : 0 ∈ (Finset.range (p + 1)).erase p :=
    Finset.mem_erase.2 ⟨Ne.symm hp0, Finset.mem_range.2 (Nat.succ_pos p)⟩
  have h1mem : 1 ∈ ((Finset.range (p + 1)).erase p).erase 0 :=
    Finset.mem_erase.2 ⟨one_ne_zero, Finset.mem_erase.2 ⟨hp1,
      Finset.mem_range.2 (Nat.succ_lt_succ hp.pos)⟩⟩
  have key : (1 + c) ^ p - 1 - c ^ p - p * c =
      ∑ m ∈ (((Finset.range (p + 1)).erase p).erase 0).erase 1,
        c ^ m * 1 ^ (p - m) * (p.choose m : K) := by
    rw [add_comm (1 : K) c, add_pow, ← Finset.add_sum_erase _ _ hpmem,
      ← Finset.add_sum_erase _ _ h0mem, ← Finset.add_sum_erase _ _ h1mem]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_pow,
      Nat.choose_zero_right, pow_one, Nat.choose_one_right]
    ring
  rw [key]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m hm ↦ ?_
  obtain ⟨hm1, hm⟩ := Finset.mem_erase.1 hm
  obtain ⟨hm0, hm'⟩ := Finset.mem_erase.1 hm
  obtain ⟨hmp, hm''⟩ := Finset.mem_erase.1 hm'
  have hmp' : m < p := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm'')) hmp
  have hm2 : 2 ≤ m := by omega
  rw [one_pow, mul_one, norm_mul, norm_pow]
  calc ‖c‖ ^ m * ‖(p.choose m : K)‖ ≤ ‖c‖ ^ 2 * ‖(p : K)‖ :=
        mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hc hm2) (norm_choose_le hp hm0 hmp')
          (norm_nonneg _) (by positivity)
    _ = ‖(p : K)‖ * ‖c‖ ^ 2 := mul_comm _ _

/-- **Frobenius modulo `p`** for finite sums: if `‖yⱼ‖ ≤ r ≤ 1`, then
`‖(Σ yⱼ) ^ p - Σ yⱼ ^ p‖ ≤ ‖p‖ r`. -/
lemma norm_sum_pow_sub_le (hp : p.Prime) {ι : Type*} (s : Finset ι) (y : ι → K) {r : ℝ}
    (hy : ∀ j ∈ s, ‖y j‖ ≤ r) (hr : r ≤ 1) (hr0 : 0 ≤ r) :
    ‖(∑ j ∈ s, y j) ^ p - ∑ j ∈ s, y j ^ p‖ ≤ ‖(p : K)‖ * r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow hp.ne_zero, sub_zero, norm_zero]
    positivity
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hyj : ‖y j‖ ≤ r := hy j (Finset.mem_insert_self j s)
    have hs : ‖∑ i ∈ s, y i‖ ≤ r :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr0 fun i hi ↦
        hy i (Finset.mem_insert_of_mem hi)
    have h1 := norm_add_pow_sub_le hp (hyj.trans hr) (hs.trans hr)
    have h2 := ih fun i hi ↦ hy i (Finset.mem_insert_of_mem hi)
    have hxy : ‖y j‖ * ‖∑ i ∈ s, y i‖ ≤ r :=
      (mul_le_mul hyj hs (norm_nonneg _) hr0).trans (by nlinarith)
    have e : (y j + ∑ i ∈ s, y i) ^ p - (y j ^ p + ∑ i ∈ s, y i ^ p) =
        ((y j + ∑ i ∈ s, y i) ^ p - y j ^ p - (∑ i ∈ s, y i) ^ p) +
          ((∑ i ∈ s, y i) ^ p - ∑ i ∈ s, y i ^ p) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h2)
    exact h1.trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg _))

end Binomial

section PthRoot

variable {p : ℕ} (hp : p.Prime) {γ : K} (hγ : γ ^ (p - 1) = -(p : K))
include hγ

omit [IsUltrametricDist K] in
lemma norm_gamma_pow_sub_one : ‖γ‖ ^ (p - 1) = ‖(p : K)‖ := by
  rw [← norm_pow, hγ, norm_neg]

omit [IsUltrametricDist K] in
include hp in
lemma gamma_pow : γ ^ p = -(p : K) * γ := by
  rw [← hγ, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le]

omit [IsUltrametricDist K] in
include hp in
lemma norm_gamma_pow : ‖γ‖ ^ p = ‖(p : K)‖ * ‖γ‖ := by
  rw [← norm_pow, gamma_pow hp hγ, norm_mul, norm_neg]

include hp in
lemma norm_gamma_le_one : ‖γ‖ ≤ 1 := by
  have h := norm_gamma_pow_sub_one hγ
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  by_contra! hlt
  have : 1 < ‖γ‖ ^ (p - 1) := one_lt_pow₀ hlt hp1
  rw [h] at this
  exact (IsUltrametricDist.norm_natCast_le_one K p).not_gt this

omit [IsUltrametricDist K] in
include hp in
lemma norm_gamma_lt_one (hp1 : ‖(p : K)‖ < 1) : ‖γ‖ < 1 := by
  have h := norm_gamma_pow_sub_one hγ
  have hn : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  rwa [← h, pow_lt_one_iff_of_nonneg (norm_nonneg _) hn] at hp1

include hp in
lemma norm_natCast_le_norm_gamma : ‖(p : K)‖ ≤ ‖γ‖ := by
  rw [← norm_gamma_pow_sub_one hγ]
  exact pow_le_of_le_one (norm_nonneg _) (norm_gamma_le_one hp hγ)
    (Nat.sub_ne_zero_of_lt hp.one_lt)

omit [IsUltrametricDist K] in
include hp in
lemma gamma_ne_zero (hp0 : (p : K) ≠ 0) : γ ≠ 0 := by
  rintro rfl
  rw [zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt), eq_comm, neg_eq_zero] at hγ
  exact hp0 hγ

variable [CompleteSpace K]

include hp in
/-- **Kuhlmann, Lemma 2.11.** A `1`-unit `1 + b` with `‖b‖ < ‖γ‖ ^ p` (i.e. of level
`> p v(p) / (p - 1)`) is a `p`-th power. -/
theorem exists_pow_eq_one_add (hp0 : (p : K) ≠ 0) {b : K} (hb : ‖b‖ < ‖γ‖ ^ p) :
    ∃ y : K, y ^ p = 1 + b := by
  have hγ0 : γ ≠ 0 := gamma_ne_zero hp hγ hp0
  have hγn : 0 < ‖γ‖ := norm_pos_iff.2 hγ0
  set f : K[X] := (X + C γ⁻¹) ^ p - C ((1 + b) / γ ^ p) with hf
  have hcoeff (k : ℕ) : f.coeff k =
      if k = 0 then -(b / γ ^ p) else γ⁻¹ ^ (p - k) * (p.choose k : K) := by
    simp only [hf, coeff_sub, coeff_X_add_C_pow, coeff_C]
    split_ifs with hk
    · subst hk
      simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, inv_pow]
      field_simp
      ring
    · rw [sub_zero]
  have hmonic : f.Monic := by
    refine ((monic_X_add_C _).pow p).sub_of_left ?_
    rw [degree_pow, degree_X_add_C, nsmul_eq_mul, mul_one]
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hp.pos)
  have hbound (k : ℕ) : ‖f.coeff k‖ ≤ 1 := by
    rw [hcoeff]
    split_ifs with hk
    · rw [norm_neg, norm_div, norm_pow]
      exact (div_lt_one (by positivity)).2 hb |>.le
    · rcases lt_trichotomy k p with hkp | rfl | hkp
      · rw [norm_mul, norm_pow, norm_inv]
        have h1 := norm_choose_le (K := K) hp hk hkp
        have h2 : ‖(p : K)‖ ≤ ‖γ‖ ^ (p - k) := by
          rw [← norm_gamma_pow_sub_one hγ]
          exact pow_le_pow_of_le_one (norm_nonneg _) (norm_gamma_le_one hp hγ) (by omega)
        calc ‖γ‖⁻¹ ^ (p - k) * ‖(p.choose k : K)‖ ≤ ‖γ‖⁻¹ ^ (p - k) * ‖γ‖ ^ (p - k) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
          _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hγn.ne', one_pow]
      · simp
      · rw [Nat.choose_eq_zero_of_lt hkp]
        simp
  have hev0 : ‖f.eval 0‖ < 1 := by
    rw [← coeff_zero_eq_eval_zero, hcoeff, if_pos rfl, norm_neg, norm_div, norm_pow]
    exact (div_lt_one (by positivity)).2 hb
  have hder0 : ‖f.derivative.eval 0‖ = 1 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, hcoeff, if_neg one_ne_zero,
      Nat.cast_zero, zero_add, mul_one, Nat.choose_one_right, inv_pow, hγ, norm_mul, norm_inv,
      norm_neg, inv_mul_cancel₀ (norm_ne_zero_iff.2 hp0)]
  obtain ⟨η, hη, -⟩ := exists_root hmonic hbound (by simp) hev0 hder0
  refine ⟨γ * η + 1, ?_⟩
  have hη' : (η + γ⁻¹) ^ p = (1 + b) / γ ^ p := by
    simpa [hf, sub_eq_zero] using hη
  calc (γ * η + 1) ^ p = γ ^ p * (η + γ⁻¹) ^ p := by
        rw [← mul_pow]
        congr 1
        field_simp
    _ = 1 + b := by
        rw [hη']
        field_simp

include hp in
/-- **Kuhlmann, Corollary 2.12 a).** If `u` is a `1`-unit and `‖v - u‖ < ‖γ‖ ^ p`, then
`v = u y ^ p` for some `y`. -/
theorem exists_eq_mul_pow (hp0 : (p : K) ≠ 0) {u v : K} (hu : ‖u - 1‖ < 1)
    (hv : ‖v - u‖ < ‖γ‖ ^ p) : ∃ y : K, v = u * y ^ p := by
  have hu1 : ‖u‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := u - 1) (y := 1)
      (by rw [norm_one]; exact hu.ne)
    rwa [sub_add_cancel, norm_one, max_eq_right hu.le] at this
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  obtain ⟨y, hy⟩ := exists_pow_eq_one_add hp hγ hp0 (b := (v - u) / u)
    (by rwa [norm_div, hu1, div_one])
  refine ⟨y, ?_⟩
  rw [hy]
  field_simp
  ring

include hp in
/-- **Kuhlmann, Corollary 2.12 d).** If `‖b‖ ≤ ‖γ‖` and `‖c‖ ^ p < ‖p‖`, then
`1 + b + c ^ p = (1 + b - p c) y ^ p` for some `y`. -/
theorem exists_eq_mul_pow_of_pow (hp0 : (p : K) ≠ 0) (hp1 : ‖(p : K)‖ < 1) {b c : K}
    (hb : ‖b‖ ≤ ‖γ‖) (hc : ‖c‖ ^ p < ‖(p : K)‖) :
    ∃ y : K, 1 + b + c ^ p = (1 + b - p * c) * y ^ p := by
  have hpn : 0 < ‖(p : K)‖ := norm_pos_iff.2 hp0
  have hγ1 : ‖γ‖ < 1 := norm_gamma_lt_one hp hγ hp1
  have hγn : 0 < ‖γ‖ := norm_pos_iff.2 (gamma_ne_zero hp hγ hp0)
  have hc1 : ‖c‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero]
    exact hc.trans hp1
  have hc2 : ‖c‖ ^ 2 < ‖γ‖ := by
    by_contra! h
    have h1 : ‖(p : K)‖ ≤ (‖c‖ ^ 2) ^ (p - 1) := by
      rw [← norm_gamma_pow_sub_one hγ]
      exact pow_le_pow_left₀ (norm_nonneg _) h _
    have h2 : (‖c‖ ^ 2) ^ (p - 1) ≤ ‖c‖ ^ p := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) hc1.le (by have := hp.two_le; omega)
    exact (h1.trans h2).not_gt hc
  set δ := (1 + c) ^ p - 1 - c ^ p - p * c with hδ
  have hδn : ‖δ‖ < ‖(p : K)‖ * ‖γ‖ :=
    (norm_one_add_pow_sub_le hp hc1.le).trans_lt (mul_lt_mul_of_pos_left hc2 hpn)
  have hδp : ‖δ‖ < ‖(p : K)‖ :=
    hδn.trans_le (mul_le_of_le_one_right hpn.le (norm_gamma_le_one hp hγ))
  have hpc : ‖(p : K) * c‖ < ‖(p : K)‖ := by
    rw [norm_mul]
    exact mul_lt_of_lt_one_right hpn hc1
  have hw : ‖c ^ p + p * c + δ‖ < ‖(p : K)‖ := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hδp)
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hpc)
    rwa [norm_pow]
  have hbpc : ‖b - p * c‖ ≤ ‖γ‖ :=
    (norm_sub_le_max' _ _).trans
      (max_le hb (hpc.le.trans (norm_natCast_le_norm_gamma hp hγ)))
  have hexp : (1 + c) ^ p = 1 + (c ^ p + p * c + δ) := by rw [hδ]; ring
  set u := (1 + b - p * c) * (1 + c) ^ p with hu
  have hu1 : ‖u - 1‖ < 1 := by
    have e : u - 1 = (b - p * c) + (c ^ p + p * c + δ) + (b - p * c) * (c ^ p + p * c + δ) := by
      rw [hu, hexp]; ring
    have hw1 : ‖c ^ p + p * c + δ‖ < 1 := hw.trans hp1
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
        (max_lt (hbpc.trans_lt hγ1) hw1)
    · rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hbpc.trans hγ1.le)) hw1
  have hvu : ‖(1 + b + c ^ p) - u‖ < ‖γ‖ ^ p := by
    have e : (1 + b + c ^ p) - u = -(δ + (b - p * c) * (c ^ p + p * c + δ)) := by
      rw [hu, hexp]; ring
    rw [e, norm_neg, norm_gamma_pow hp hγ]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact hδn
    · rw [norm_mul]
      calc ‖b - p * c‖ * ‖c ^ p + p * c + δ‖ ≤ ‖γ‖ * ‖c ^ p + p * c + δ‖ :=
            mul_le_mul_of_nonneg_right hbpc (norm_nonneg _)
        _ < ‖γ‖ * ‖(p : K)‖ := mul_lt_mul_of_pos_left hw hγn
        _ = ‖(p : K)‖ * ‖γ‖ := mul_comm _ _
  obtain ⟨y, hy⟩ := exists_eq_mul_pow hp hγ hp0 hu1 hvu
  exact ⟨(1 + c) * y, by rw [hy, hu, mul_pow, mul_assoc]⟩

end PthRoot

end PthPower

end SemistableReduction
