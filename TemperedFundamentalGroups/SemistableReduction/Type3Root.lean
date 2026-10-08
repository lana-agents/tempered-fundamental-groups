/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Roots of `1`-units in complete ultrametric fields

Blueprint §9.10a (I.3). Let `M` be a complete non-archimedean field.

* `exists_fixedPoint_of_contract`: a self-map of a closed ball which is a contraction has a
  fixed point (Banach);
* `exists_pow_eq_one_add` (tame roots): if `‖n‖ = 1` and `‖w‖ < 1`, then `1 + w` is an `n`-th
  power;
* `norm_pow_sub_pow_le`: `‖Xᵏ - Yᵏ‖ ≤ r^(k-1) ‖X - Y‖` on the ball of radius `r`;
* for `π^(p-1) = -p` (`IsPi`): `(1 + π X)^p = 1 + π^p (X^p - X) + E(X)` with
  `‖E(X)‖ ≤ ‖π‖^(p+1) max(1, ‖X‖)^(p-1)` (`norm_onePlusPiPow_sub_le`), and
  `exists_pow_eq_one_add_of_lt` (wild roots): `1 + w` is a `p`-th power if `‖w‖ < ‖π‖^p`.
-/

open Finset

namespace SemistableReduction

namespace Type3

variable {M : Type*} [NormedField M] [IsUltrametricDist M]

/-- `‖Xᵏ - Yᵏ‖ ≤ r^(k-1) ‖X - Y‖` for `‖X‖, ‖Y‖ ≤ r`, `k ≥ 1`. -/
lemma norm_pow_sub_pow_le {X Y : M} {r : ℝ} (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r) {k : ℕ}
    (hk : 1 ≤ k) : ‖X ^ k - Y ^ k‖ ≤ r ^ (k - 1) * ‖X - Y‖ := by
  have hr : 0 ≤ r := (norm_nonneg X).trans hX
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _) fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  rw [norm_mul, norm_pow, norm_pow]
  calc ‖X‖ ^ i * ‖Y‖ ^ (k - 1 - i) ≤ r ^ i * r ^ (k - 1 - i) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hX _)
          (pow_le_pow_left₀ (norm_nonneg _) hY _) (by positivity) (pow_nonneg hr _)
    _ = r ^ (k - 1) := by rw [← pow_add]; congr 1; omega

/-- The norm of a natural number in an ultrametric field is at most `1`. -/
lemma norm_natCast_le_one' (n : ℕ) : ‖(n : M)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one M n

variable [CompleteSpace M]

omit [IsUltrametricDist M] in
/-- **Banach's fixed point theorem on a closed ball.** -/
theorem exists_fixedPoint_of_contract (Φ : M → M) {r K : ℝ} (hr : 0 ≤ r) (hK0 : 0 ≤ K)
    (hK : K < 1) (hmaps : ∀ X, ‖X‖ ≤ r → ‖Φ X‖ ≤ r)
    (hlip : ∀ X Y, ‖X‖ ≤ r → ‖Y‖ ≤ r → ‖Φ X - Φ Y‖ ≤ K * ‖X - Y‖) :
    ∃ X, ‖X‖ ≤ r ∧ Φ X = X := by
  set B := Metric.closedBall (0 : M) r
  haveI : CompleteSpace B := (Metric.isClosed_closedBall).completeSpace_coe
  haveI : Nonempty B := ⟨⟨0, Metric.mem_closedBall_self hr⟩⟩
  have hB : ∀ X : M, X ∈ B ↔ ‖X‖ ≤ r := fun X ↦ by simp [B]
  set f : B → B := fun X ↦ ⟨Φ X, (hB _).2 (hmaps X ((hB X).1 X.2))⟩
  have hf : ContractingWith ⟨K, hK0⟩ f := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul fun X Y ↦ ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm, f]
    exact hlip X Y ((hB X).1 X.2) ((hB Y).1 Y.2)
  refine ⟨(ContractingWith.fixedPoint f hf).1, (hB _).1 (ContractingWith.fixedPoint f hf).2, ?_⟩
  have := ContractingWith.fixedPoint_isFixedPt (f := f) hf
  exact congrArg Subtype.val this

omit [CompleteSpace M] in
lemma norm_eq_one_of_norm_sub_one_lt' {u : M} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := u - 1) (y := 1)
    (by rw [norm_one]; exact hu.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right hu.le] at this

omit [CompleteSpace M] in
/-- Products of powers of `1`-units are `1`-units. -/
lemma norm_pow_mul_pow_sub_one_le {u v : M} {δ : ℝ} (hu : ‖u - 1‖ ≤ δ) (hv : ‖v - 1‖ ≤ δ)
    (hδ : δ < 1) (i j : ℕ) : ‖u ^ i * v ^ j - 1‖ ≤ δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hu
  have hpow : ∀ {t : M}, ‖t - 1‖ ≤ δ → ∀ n : ℕ, ‖t ^ n - 1‖ ≤ δ := by
    intro t ht n
    have ht1 : ‖t‖ = 1 := norm_eq_one_of_norm_sub_one_lt' (ht.trans_lt hδ)
    induction n with
    | zero => simpa using hδ0
    | succ n ih =>
      rw [show t ^ (n + 1) - 1 = t ^ n * (t - 1) + (t ^ n - 1) by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      rw [norm_mul, norm_pow, ht1, one_pow, one_mul]
      exact ht
  have h1 := hpow hu i
  have h2 := hpow hv j
  have hu1 : ‖u ^ i‖ = 1 := norm_eq_one_of_norm_sub_one_lt' (h1.trans_lt hδ)
  rw [show u ^ i * v ^ j - 1 = u ^ i * (v ^ j - 1) + (u ^ i - 1) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
  rw [norm_mul, hu1, one_mul]
  exact h2

/-- **Tame roots**: if `‖n‖ = 1` and `‖w‖ < 1`, then `1 + w = (1 + X)^n` with `‖X‖ ≤ ‖w‖`. -/
theorem exists_pow_eq_one_add {n : ℕ} (hn : ‖(n : M)‖ = 1) {w : M} (hw : ‖w‖ < 1) :
    ∃ X : M, ‖X‖ ≤ ‖w‖ ∧ (1 + X) ^ n = 1 + w := by
  have hn0 : (n : M) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  set r := ‖w‖
  set Φ : M → M := fun X ↦ X - ((1 + X) ^ n - 1 - w) / n
  have hlip : ∀ X Y, ‖X‖ ≤ r → ‖Y‖ ≤ r → ‖Φ X - Φ Y‖ ≤ r * ‖X - Y‖ := by
    intro X Y hX hY
    set S := ∑ i ∈ range n, (1 + X) ^ i * (1 + Y) ^ (n - 1 - i)
    have hS : (1 + X) ^ n - (1 + Y) ^ n = S * (X - Y) := by
      rw [← geom_sum₂_mul]; ring
    have hexp : Φ X - Φ Y = (X - Y) * ((n : M) - S) / n := by
      rw [show Φ X - Φ Y = X - Y - ((1 + X) ^ n - (1 + Y) ^ n) / n by simp only [Φ]; ring, hS]
      field_simp
    have hnS : ‖(n : M) - S‖ ≤ r := by
      rw [show (n : M) - S = ∑ i ∈ range n, (1 - (1 + X) ^ i * (1 + Y) ^ (n - 1 - i)) by
        simp [S, Finset.sum_sub_distrib]]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ ↦ ?_
      rw [norm_sub_rev]
      exact norm_pow_mul_pow_sub_one_le (by simpa using hX) (by simpa using hY) hw i _
    rw [hexp, norm_div, hn, div_one, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hnS (norm_nonneg _)
  have hmaps : ∀ X, ‖X‖ ≤ r → ‖Φ X‖ ≤ r := by
    intro X hX
    have h0 : Φ 0 = w / n := by simp only [Φ]; ring
    have h1 := hlip X 0 hX (by rw [norm_zero]; exact norm_nonneg w)
    rw [h0, sub_zero] at h1
    rw [show Φ X = (Φ X - w / n) + w / n by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h1.trans (by nlinarith [norm_nonneg X, norm_nonneg w])
    · rw [norm_div, hn, div_one]
  obtain ⟨X, hX, hfix⟩ := exists_fixedPoint_of_contract Φ (norm_nonneg w) (norm_nonneg w) hw
    hmaps hlip
  refine ⟨X, hX, ?_⟩
  have : ((1 + X) ^ n - 1 - w) / n = 0 := by
    have := hfix
    simp only [Φ] at this
    linear_combination -this
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · linear_combination h
  · exact absurd h hn0

section Wild

variable {p : ℕ} (hp : p.Prime) {π : M} (hπ : π ^ (p - 1) = -(p : M))
include hp hπ

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- `π^p = -p π`. -/
lemma pi_pow_eq : π ^ p = -(p : M) * π := by
  rw [← hπ, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le]

variable (p π) in
/-- The middle terms of `(1 + π X)^p`. -/
noncomputable def pmid (X : M) : M :=
  ∑ k ∈ range (p - 2), (p.choose (k + 2) : M) * π ^ (k + 2) * X ^ (k + 2)

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- `(1 + π X)^p = 1 + π^p (X^p - X) + pmid X`. -/
lemma one_add_pi_pow (X : M) :
    (1 + π * X) ^ p = 1 + π ^ p * (X ^ p - X) + pmid p π X := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hpi := pi_pow_eq hp hπ
  rw [add_comm, add_pow, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ',
    pmid, show m + 2 - 2 = m by omega]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, zero_add,
    pow_one, Nat.choose_one_right, Nat.choose_self]
  push_cast
  have : ∀ k ∈ range m, (π * X) ^ (k + 1 + 1) * ((m + 2).choose (k + 1 + 1) : M) =
      ((m + 2).choose (k + 2) : M) * π ^ (k + 2) * X ^ (k + 2) := fun k _ ↦ by
    rw [mul_pow]; ring
  rw [Finset.sum_congr rfl this]
  push_cast at hpi
  linear_combination X * hpi

omit [CompleteSpace M] hπ in
/-- `‖C(p, k)‖ ≤ ‖p‖` for `0 < k < p`. -/
lemma norm_choose_le {k : ℕ} (hk0 : 0 < k) (hkp : k < p) : ‖(p.choose k : M)‖ ≤ ‖(p : M)‖ := by
  obtain ⟨t, ht⟩ := hp.dvd_choose_self hk0.ne' hkp
  rw [ht, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one M t)

omit [CompleteSpace M] [IsUltrametricDist M] hp in
lemma norm_p_eq : ‖(p : M)‖ = ‖π‖ ^ (p - 1) := by
  rw [← norm_pow, hπ, norm_neg]

omit [CompleteSpace M] in
/-- Each middle term is small. -/
lemma norm_pmid_term_le {k : ℕ} (hk : k ∈ range (p - 2)) {Z : M} :
    ‖(p.choose (k + 2) : M) * π ^ (k + 2) * Z‖ ≤ ‖π‖ ^ (p + 1 + k) * ‖Z‖ := by
  have hk' := Finset.mem_range.1 hk
  rw [norm_mul, norm_mul, norm_pow]
  have h1 := norm_choose_le (M := M) hp (k := k + 2) (by omega) (by omega)
  rw [norm_p_eq hπ] at h1
  have : ‖π‖ ^ (p + 1 + k) = ‖π‖ ^ (p - 1) * ‖π‖ ^ (k + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  gcongr

omit [CompleteSpace M] in
/-- **The Artin–Schreier expansion**:
`‖(1 + πX)^p - 1 - π^p (X^p - X)‖ ≤ ‖π‖^(p+1) max(1,‖X‖)^(p-1)`
for `‖π‖ ≤ 1`. -/
theorem norm_pmid_le (hπ1 : ‖π‖ ≤ 1) (X : M) :
    ‖pmid p π X‖ ≤ ‖π‖ ^ (p + 1) * max 1 ‖X‖ ^ (p - 1) := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk ↦ ?_
  have hk' := Finset.mem_range.1 hk
  refine (norm_pmid_term_le hp hπ hk).trans ?_
  rw [norm_pow, pow_add ‖π‖ (p + 1)]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖π‖ ^ k * ‖X‖ ^ (k + 2) ≤ 1 * max 1 ‖X‖ ^ (k + 2) :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) hπ1)
          (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _) (by positivity) zero_le_one
    _ ≤ max 1 ‖X‖ ^ (p - 1) := by
        rw [one_mul]; exact pow_le_pow_right₀ (le_max_left _ _) (by omega)

/-- **Wild roots**: if `‖w‖ < ‖π‖^p` then `1 + w = (1 + π X)^p` with `‖X‖ ≤ ‖w‖ / ‖π‖^p`. -/
theorem exists_pow_eq_one_add_of_lt (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) {w : M}
    (hw : ‖w‖ < ‖π‖ ^ p) : ∃ X : M, ‖X‖ ≤ ‖w‖ / ‖π‖ ^ p ∧ (1 + π * X) ^ p = 1 + w := by
  have hπp : 0 < ‖π‖ ^ p := pow_pos (norm_pos_iff.2 hπ0) p
  set r := ‖w‖ / ‖π‖ ^ p
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one hπp).2 hw
  set K := max (r ^ (p - 1)) ‖π‖
  have hK0 : 0 ≤ K := le_max_of_le_right (norm_nonneg _)
  have hK1 : K < 1 := max_lt (pow_lt_one₀ hr0 hr1 (by have := hp.two_le; omega)) hπ1
  have hπp0 : π ^ p ≠ 0 := pow_ne_zero _ hπ0
  set Φ : M → M := fun X ↦ X ^ p + (pmid p π X - w) / π ^ p
  have hlip : ∀ X Y, ‖X‖ ≤ r → ‖Y‖ ≤ r → ‖Φ X - Φ Y‖ ≤ K * ‖X - Y‖ := by
    intro X Y hX hY
    have hd : Φ X - Φ Y = (X ^ p - Y ^ p) + (pmid p π X - pmid p π Y) / π ^ p := by
      simp only [Φ]; ring
    rw [hd]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (norm_pow_sub_pow_le hX hY hp.one_lt.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · rw [norm_div, norm_pow, div_le_iff₀ hπp, pmid, pmid, ← Finset.sum_sub_distrib]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        fun k hk ↦ ?_
      rw [← mul_sub]
      refine (norm_pmid_term_le hp hπ hk).trans ?_
      have h1 := norm_pow_sub_pow_le hX hY (k := k + 2) (by omega)
      have h2 : r ^ (k + 2 - 1) ≤ 1 := pow_le_one₀ hr0 hr1.le
      calc ‖π‖ ^ (p + 1 + k) * ‖X ^ (k + 2) - Y ^ (k + 2)‖
          ≤ ‖π‖ ^ (p + 1 + k) * (1 * ‖X - Y‖) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
            exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖π‖ * ‖X - Y‖ * ‖π‖ ^ p * ‖π‖ ^ k := by ring
        _ ≤ ‖π‖ * ‖X - Y‖ * ‖π‖ ^ p * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hπ1.le) (by positivity)
        _ = ‖π‖ * ‖X - Y‖ * ‖π‖ ^ p := mul_one _
        _ ≤ K * ‖X - Y‖ * ‖π‖ ^ p := by
            gcongr
            exact le_max_right _ _
  have hmaps : ∀ X, ‖X‖ ≤ r → ‖Φ X‖ ≤ r := by
    intro X hX
    have h0 : Φ 0 = -w / π ^ p := by
      simp [Φ, pmid, hp.ne_zero]
    have h1 := hlip X 0 hX (by rw [norm_zero]; exact hr0)
    rw [h0, sub_zero] at h1
    rw [show Φ X = (Φ X - -w / π ^ p) + -w / π ^ p by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h1.trans (by nlinarith)
    · rw [norm_div, norm_neg, norm_pow]
  obtain ⟨X, hX, hfix⟩ := exists_fixedPoint_of_contract Φ hr0 hK0 hK1 hmaps hlip
  refine ⟨X, hX, ?_⟩
  rw [one_add_pi_pow hp hπ]
  have : (pmid p π X - w) / π ^ p = X - X ^ p := by
    have := hfix
    simp only [Φ] at this
    linear_combination this
  field_simp at this
  linear_combination this

end Wild

end Type3

end SemistableReduction
