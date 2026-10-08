/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Gen
import TemperedFundamentalGroups.SemistableReduction.Type3Root

/-!
# The additive `p`-Taylor iteration at a type-3 radius (Phase 1)

Blueprint §9.10a (I.3), Phase 1. Let `M` be the closure of `C(y)`, `‖y‖ ∉ |C^×|`, and `u₀ ∈ M`.

* `norm_add_pow_sub_le`, `norm_sum_pow_sub_le`: `‖(Σ xⱼ)^p - Σ xⱼ^p‖ ≤ ‖p‖ R^p` for `‖xⱼ‖ ≤ R`
  (the multinomial coefficients off the diagonal are divisible by `p`);
* `exists_frob` (Frobenius root): a Laurent polynomial `F` supported on multiples of `p` has a
  `k` with `‖k‖^p ≤ ‖F‖` and `‖k^p - F‖ ≤ ‖p‖ ‖F‖` (`k = Σ F_i^{1/p} y^{i/p}`);
* **`phase1_step`**: if `‖u₀ - h^p - Ψ‖ ≤ B` with `Ψ` supported on exponents prime to `p`,
  `‖h - 1‖ < 1` and `‖p‖^{p/(p-1)} ≤ B < 1`, the same holds with `B' = ‖p‖ B^{1/p}`;
* **`phase1`**: for every `T > 1` the bound `B ≤ ‖p‖^{p/(p-1)} T` is reached.
-/

open Finset

namespace SemistableReduction

namespace Type3

section Multinomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
include hp

/-- `‖(x + y)^p - x^p - y^p‖ ≤ ‖p‖ max_{0<j<p} ‖x‖^j ‖y‖^(p-j)`. -/
lemma norm_add_pow_sub_le' (x y : K) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ j ∈ Ioo 0 p, ‖x‖ ^ j * ‖y‖ ^ (p - j) ≤ R) :
    ‖(x + y) ^ p - x ^ p - y ^ p‖ ≤ ‖(p : K)‖ * R := by
  rw [add_pow_prime_eq' hp, show ∀ a b c : K, a + b + c - a - b = c from fun a b c ↦ by ring,
    norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR fun j hj ↦ ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  exact (mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one K _)).trans
    (h j hj)

/-- `‖(x + y)^p - x^p - y^p‖ ≤ ‖p‖ R^p` for `‖x‖, ‖y‖ ≤ R`. -/
lemma norm_add_pow_sub_le {x y : K} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖(x + y) ^ p - x ^ p - y ^ p‖ ≤ ‖(p : K)‖ * R ^ p := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  refine norm_add_pow_sub_le' hp x y (pow_nonneg hR p) fun j hj ↦ ?_
  have hj' := Finset.mem_Ioo.1 hj
  calc ‖x‖ ^ j * ‖y‖ ^ (p - j) ≤ R ^ j * R ^ (p - j) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _) (pow_le_pow_left₀ (norm_nonneg _) hy _)
          (by positivity) (pow_nonneg hR _)
    _ = R ^ p := by rw [← pow_add]; congr 1; omega

/-- **Multinomial estimate**: `‖(Σ xⱼ)^p - Σ xⱼ^p‖ ≤ ‖p‖ R^p` for `‖xⱼ‖ ≤ R`. -/
lemma norm_sum_pow_sub_le {ι : Type*} (s : Finset ι) (x : ι → K) {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ j ∈ s, ‖x j‖ ≤ R) :
    ‖(∑ j ∈ s, x j) ^ p - ∑ j ∈ s, x j ^ p‖ ≤ ‖(p : K)‖ * R ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [hp.ne_zero] using mul_nonneg (norm_nonneg (p : K)) (pow_nonneg hR p)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ‖∑ j ∈ s, x j‖ ≤ R :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR fun j hj ↦
        hx j (Finset.mem_insert_of_mem hj)
    rw [show (x a + ∑ j ∈ s, x j) ^ p - (x a ^ p + ∑ j ∈ s, x j ^ p) =
      ((x a + ∑ j ∈ s, x j) ^ p - x a ^ p - (∑ j ∈ s, x j) ^ p) +
        ((∑ j ∈ s, x j) ^ p - ∑ j ∈ s, x j ^ p) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (norm_add_pow_sub_le hp (hx a (Finset.mem_insert_self a s)) hs)
      (ih fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)))

end Multinomial

section Frob

variable {C K : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [NormedField K] [IsUltrametricDist K] [NormedAlgebra C K] {p : ℕ} (hp : p.Prime)
include hp

omit [IsUltrametricDist C] in
/-- **Frobenius roots of Laurent polynomials** supported on multiples of `p`. -/
theorem exists_frob {y : K} (hy : IsValTrans C y) (F : ℤ →₀ C)
    (hF : ∀ i ∈ F.support, (p : ℤ) ∣ i) :
    ∃ k : K, ‖k‖ ^ p ≤ ‖lev y F‖ ∧ ‖k ^ p - lev y F‖ ≤ ‖(p : K)‖ * ‖lev y F‖ := by
  classical
  choose r hr using fun i : ℤ ↦ IsAlgClosed.exists_pow_nat_eq (F i) hp.pos
  set t : ℤ → K := fun i ↦ mono y (r i) (i / p)
  have htp : ∀ i ∈ F.support, t i ^ p = mono y (F i) i := by
    intro i hi
    simp only [t]
    rw [mono_pow, hr i, Int.mul_ediv_cancel' (hF i hi)]
  have htn : ∀ i ∈ F.support, ‖t i‖ ^ p ≤ ‖lev y F‖ := by
    intro i hi
    rw [← norm_pow, htp i hi, norm_mono]
    exact tm_le hy F i
  have hsum : lev y F = ∑ i ∈ F.support, t i ^ p := by
    rw [lev_eq_sum]
    exact Finset.sum_congr rfl fun i hi ↦ (htp i hi).symm
  rcases F.support.eq_empty_or_nonempty with he | hne
  · refine ⟨0, ?_, ?_⟩ <;> simp [hsum, he, hp.ne_zero]
  refine ⟨∑ i ∈ F.support, t i, ?_, ?_⟩
  · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne t
    exact (pow_le_pow_left₀ (norm_nonneg _) hle p).trans (htn j hj)
  · obtain ⟨j, hj, hmax⟩ := F.support.exists_max_image (fun i ↦ ‖t i‖) hne
    have h1 := norm_sum_pow_sub_le hp F.support t (norm_nonneg (t j)) hmax
    rw [← hsum] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (htn j hj) (norm_nonneg _))

end Frob

section Phase1

variable {C M : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [NormedField M] [IsUltrametricDist M] [NormedAlgebra C M] {p : ℕ} (hp : p.Prime)

variable (p) in
/-- `Ψ` is supported on exponents prime to `p`. -/
def IsPrimeToP (Ψ : ℤ →₀ C) : Prop := ∀ i ∈ Ψ.support, ¬ (p : ℤ) ∣ i

omit [IsUltrametricDist C] in
/-- The filter of a Laurent polynomial is bounded by it. -/
lemma norm_lev_filter_le {y : M} (hy : IsValTrans C y) (F : ℤ →₀ C) (P : ℤ → Prop)
    [DecidablePred P] : ‖lev y (F.filter P)‖ ≤ ‖lev y F‖ := by
  rcases eq_or_ne (F.filter P) 0 with h0 | h0
  · rw [h0, lev_zero, norm_zero]
    exact norm_nonneg _
  obtain ⟨n, hn0, hn, -⟩ := exists_dom hy h0
  rw [hn]
  have hPn : P n := by
    by_contra hP
    exact hn0 (Finsupp.filter_apply_neg _ _ hP)
  have : tm y (F.filter P) n = tm y F n := by
    simp [tm, Finsupp.filter_apply_pos _ _ hPn]
  rw [this]
  exact tm_le hy F n

omit [NormedAlgebra C M] [IsUltrametricDist C] [IsAlgClosed C] in
lemma norm_sub_le_max' (a b : M) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

include hp in
omit [IsUltrametricDist C] in
/-- **One step of the additive `p`-Taylor iteration.** -/
theorem phase1_step {y : M} (hy : IsType3 C y) (hp0 : 0 < ‖(p : M)‖) {u₀ h : M}
    {Ψ : ℤ →₀ C} (hΨ : IsPrimeToP p Ψ) (hh : ‖h - 1‖ < 1) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hBB : ‖(p : M)‖ * B ^ (p : ℝ)⁻¹ ≤ B) (hBpos : 0 < B) (hinv : ‖u₀ - h ^ p - lev y Ψ‖ ≤ B) :
    ∃ (h' : M) (Ψ' : ℤ →₀ C), IsPrimeToP p Ψ' ∧ ‖h' - 1‖ < 1 ∧
      ‖u₀ - h' ^ p - lev y Ψ'‖ ≤ ‖(p : M)‖ * B ^ (p : ℝ)⁻¹ := by
  classical
  set B' := ‖(p : M)‖ * B ^ (p : ℝ)⁻¹ with hB'
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hBp : B ^ (p : ℝ)⁻¹ < 1 := Real.rpow_lt_one hB0 hB1 (by positivity)
  have hBle : B ≤ B ^ (p : ℝ)⁻¹ :=
    Real.self_le_rpow_of_le_one hB0 hB1.le (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le))
  have hB'0 : 0 < B' := mul_pos hp0 (Real.rpow_pos_of_pos hBpos _)
  set r := u₀ - h ^ p - lev y Ψ with hr
  obtain ⟨F, hF⟩ := exists_lev_near hy r hB'0
  have hFB : ‖lev y F‖ ≤ B := by
    have := IsUltrametricDist.norm_add_le_max r (-(r - lev y F))
    rw [norm_neg, show r + -(r - lev y F) = lev y F by ring] at this
    exact this.trans (max_le hinv (hF.le.trans hBB))
  set Fp := F.filter (fun i ↦ (p : ℤ) ∣ i)
  set Fq := F.filter (fun i ↦ ¬ (p : ℤ) ∣ i)
  have hsplit : lev y F = lev y Fp + lev y Fq := by
    rw [← lev_add, Finsupp.filter_add_filter_not]
  have hFp : ‖lev y Fp‖ ≤ B := (norm_lev_filter_le hy.valTrans F _).trans hFB
  obtain ⟨k, hk1, hk2⟩ := exists_frob hp hy.valTrans Fp fun i hi ↦ by
    rw [Finsupp.support_filter, Finset.mem_filter] at hi
    exact hi.2
  have hk : ‖k‖ ≤ B ^ (p : ℝ)⁻¹ := by
    have := Real.rpow_le_rpow (by positivity) (hk1.trans hFp) (inv_nonneg.2 hp'.le)
    rwa [Real.pow_rpow_inv_natCast (norm_nonneg k) hp.ne_zero] at this
  have hk1' : ‖k‖ < 1 := hk.trans_lt hBp
  have hh1 : ‖h‖ = 1 := norm_eq_one_of_norm_sub_one_lt hh
  refine ⟨h + k, Ψ + Fq, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.1 (Finsupp.support_add hi) with h1 | h1
    · exact hΨ i h1
    · rw [Finsupp.support_filter, Finset.mem_filter] at h1
      exact h1.2
  · rw [show h + k - 1 = (h - 1) + k by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hh hk1')
  · have hid : u₀ - (h + k) ^ p - lev y (Ψ + Fq) =
        (r - lev y F) + (lev y Fp - k ^ p) - ((h + k) ^ p - h ^ p - k ^ p) := by
      rw [lev_add, hsplit, hr]
      ring
    rw [hid]
    refine (norm_sub_le_max' _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hF.le ?_)) ?_)
    · rw [norm_sub_rev]
      refine hk2.trans ?_
      exact mul_le_mul_of_nonneg_left (hFp.trans hBle) (norm_nonneg _)
    · refine norm_add_pow_sub_le' hp h k (by positivity) fun j hj ↦ ?_
      have hj' := Finset.mem_Ioo.1 hj
      rw [hh1, one_pow, one_mul]
      calc ‖k‖ ^ (p - j) ≤ ‖k‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) hk1'.le (by omega)
        _ ≤ B ^ (p : ℝ)⁻¹ := by rw [pow_one]; exact hk

include hp in
omit [IsUltrametricDist C] in
/-- **Phase 1**: the additive `p`-Taylor iteration reaches every bound `A T`, `T > 1`, where `A`
is the fixed point of `B ↦ ‖p‖ B^{1/p}` (`A = ‖π‖^p` for `π^(p-1) = -p`). -/
theorem phase1 {y : M} (hy : IsType3 C y) (hp0 : 0 < ‖(p : M)‖) {A : ℝ} (hA0 : 0 < A)
    (hA1 : A < 1) (hAfix : ‖(p : M)‖ * A ^ (p : ℝ)⁻¹ = A) {u₀ : M} (hu₀ : ‖u₀ - 1‖ < 1)
    {T : ℝ} (hT : 1 < T) :
    ∃ (h : M) (Ψ : ℤ →₀ C), IsPrimeToP p Ψ ∧ ‖h - 1‖ < 1 ∧ ‖u₀ - h ^ p - lev y Ψ‖ ≤ A * T := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.2 hp'.le
  have hpinv1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  -- `‖p‖ B^{1/p} = A (B/A)^{1/p}`
  have hg : ∀ B, 0 ≤ B → ‖(p : M)‖ * B ^ (p : ℝ)⁻¹ = A * (B / A) ^ (p : ℝ)⁻¹ := by
    intro B hB
    have hApos : 0 < A ^ (p : ℝ)⁻¹ := Real.rpow_pos_of_pos hA0 _
    rw [Real.div_rpow hB hA0.le]
    calc ‖(p : M)‖ * B ^ (p : ℝ)⁻¹
        = (‖(p : M)‖ * A ^ (p : ℝ)⁻¹) * (B ^ (p : ℝ)⁻¹ / A ^ (p : ℝ)⁻¹) := by
          field_simp
      _ = _ := by rw [hAfix]
  set B₀ := max ‖u₀ - 1‖ A
  have key : ∀ n : ℕ, ∃ B, A ≤ B ∧ B < 1 ∧ B / A - 1 ≤ (B₀ / A - 1) / p ^ n ∧
      ∃ (h : M) (Ψ : ℤ →₀ C), IsPrimeToP p Ψ ∧ ‖h - 1‖ < 1 ∧ ‖u₀ - h ^ p - lev y Ψ‖ ≤ B := by
    intro n
    induction n with
    | zero =>
      refine ⟨B₀, le_max_right _ _, max_lt hu₀ hA1, by simp, 1, 0, fun i hi ↦ by simp at hi,
        by simp, ?_⟩
      rw [one_pow, lev_zero, sub_zero]
      exact le_max_left _ _
    | succ n ih =>
      obtain ⟨B, hAB, hB1, hBn, h, Ψ, hΨ, hh, hinv⟩ := ih
      have hBpos : 0 < B := hA0.trans_le hAB
      have hx : 1 ≤ B / A := (one_le_div hA0).2 hAB
      have hgB := hg B hBpos.le
      have hle : (B / A) ^ (p : ℝ)⁻¹ ≤ B / A := by
        calc (B / A) ^ (p : ℝ)⁻¹ ≤ (B / A) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx hpinv1
          _ = B / A := Real.rpow_one _
      have hBB : ‖(p : M)‖ * B ^ (p : ℝ)⁻¹ ≤ B := by
        rw [hgB]
        calc A * (B / A) ^ (p : ℝ)⁻¹ ≤ A * (B / A) := mul_le_mul_of_nonneg_left hle hA0.le
          _ = B := by field_simp
      obtain ⟨h', Ψ', hΨ', hh', hinv'⟩ :=
        phase1_step hp hy hp0 hΨ hh hBpos.le hB1 hBB hBpos hinv
      refine ⟨‖(p : M)‖ * B ^ (p : ℝ)⁻¹, ?_, hBB.trans_lt hB1, ?_, h', Ψ', hΨ', hh', hinv'⟩
      · rw [hgB]
        exact le_mul_of_one_le_right hA0.le (Real.one_le_rpow hx hpinv0)
      · rw [hgB, mul_div_cancel_left₀ _ hA0.ne']
        have hb := rpow_one_add_le_one_add_mul_self (s := B / A - 1) (by linarith)
          hpinv0 hpinv1
        rw [add_sub_cancel] at hb
        rw [pow_succ, ← div_div]
        calc (B / A) ^ (p : ℝ)⁻¹ - 1 ≤ (p : ℝ)⁻¹ * (B / A - 1) := by linarith
          _ = (B / A - 1) / p := by ring
          _ ≤ (B₀ / A - 1) / p ^ n / p := div_le_div_of_nonneg_right hBn hp'.le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((B₀ / A - 1) / (T - 1))
    (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  obtain ⟨B, -, -, hBn, h, Ψ, hΨ, hh, hinv⟩ := key n
  refine ⟨h, Ψ, hΨ, hh, hinv.trans ?_⟩
  have hT1 : 0 < T - 1 := by linarith
  have hpn : 0 < (p : ℝ) ^ n := pow_pos hp' n
  have h1 : (B₀ / A - 1) / p ^ n ≤ T - 1 := by
    rw [div_le_iff₀ hpn]
    rw [div_lt_iff₀ hT1] at hn
    nlinarith
  have h2 : B / A ≤ T := by linarith
  rwa [div_le_iff₀ hA0, mul_comm] at h2

end Phase1

end Type3

end SemistableReduction
