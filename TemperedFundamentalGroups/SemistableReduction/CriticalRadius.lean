/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerDisc

/-!
# Precise approximations and the critical radius

Blueprint §9.10, L4 (K1, K4): Arzdorf's best approximations (Prop. 2.2, Cor. 2.16, 2.23) and the
critical radius of the modified Newton polygon (Def. 2.20–2.30), for power series over a
non-archimedean field `C` (algebraically closed, not necessarily complete).

Over `C` the supremum of the coefficients of a bounded power series need not be attained, so all
statements are made at a radius `‖l‖ < 1` (the rescaled series `Σ aᵢ lⁱ tⁱ` has coefficients
tending to `0`): the "boundary" of the analysis is the Gauss point of radius `‖l‖`, where every
maximum is attained.

## The modified Newton polygon of a sequence

For a sequence `a` of nonnegative reals with maximum `M` attained first at `m` (`Dom a M m`) and a
number `0 < A < M` (the virtual point `P'₀`; `A = ‖γ‖ ^ p = ‖p‖ ^ (p / (p - 1))` below), the
critical radius `crit a A M m hm = max (max_{0<i<m} (aᵢ / M) ^ (1 / (m - i)), (A / M) ^ (1 / m))`
is the absolute value of the slope of the last segment of the modified Newton polygon. Then
(`exists_crit`):
* for `θ₀ < θ < 1` the index `m` strictly dominates: `aᵢ θⁱ < M θ^m` for `i ≠ m`, and
  `A < M θ^m`;
* at `θ₀` all terms are `≤ M θ₀^m`, `A ≤ M θ₀^m`, and either `A = M θ₀^m` (the Artin–Schreier
  case, `P_l = P'₀`) or `A < M θ₀^m` and the smallest dominant index `l` satisfies `0 < l < m`,
  `p ∤ l` (the purely inseparable case); terms at indices divisible by `p` are strictly below,
  provided the approximation is *precise*: `aᵢ ^ m < A ^ (m - i) M ^ i` for `0 < i < m`, `p ∣ i`.

## Power series

* `term g l i = ‖gᵢ‖ ‖l‖^i`, `exists_dom`: at a radius `‖l‖ < 1` the maximum of the terms of a
  nonzero series with integral coefficients is attained;
* `pBound_eq`: `pBound C p n = A ^ (1 - 1/p^(n+1))`; hence `pBound C p n → A`;
* **`exists_precise` (K1)**: for `f` with integral coefficients and a radius `‖l‖ < 1`, either `f`
  is approximable by `p`-th powers up to every bound `> A` at that radius (the degenerate case:
  the Kummer extension at the Gauss point is split or Artin–Schreier), or there is a *precise*
  approximation: `h` with integral coefficients, `g = f - h^p`, `g₀ = 0`, `Dom (term g l) M m`,
  `p ∤ m`, `A < M`, precise at `p`-indices;
* `dom_unique` (K2 at a radius): the value `M` and the index `m` do not depend on the precise
  approximation.
-/

open PowerSeries NNReal Filter Topology

namespace SemistableReduction

namespace CriticalRadius

/-! ### The modified Newton polygon of a sequence -/

section Polygon

/-- `a` is a sequence of nonnegative reals with maximum `M`, attained first at `m`. -/
structure Dom (a : ℕ → ℝ) (M : ℝ) (m : ℕ) : Prop where
  nonneg : ∀ i, 0 ≤ a i
  eq : a m = M
  le : ∀ i, a i ≤ M
  lt : ∀ i < m, a i < M

/-- The sequence with the virtual point `A` at index `0`. -/
def vpt (a : ℕ → ℝ) (A : ℝ) (i : ℕ) : ℝ := if i = 0 then A else a i

/-- The candidate radius of the segment from `Pᵢ` (or `P'₀`) to `P_m`. -/
noncomputable def cand (a : ℕ → ℝ) (A M : ℝ) (m i : ℕ) : ℝ :=
  (vpt a A i / M) ^ (((m - i : ℕ) : ℝ)⁻¹)

/-- The **critical radius**: the largest candidate radius. -/
noncomputable def crit (a : ℕ → ℝ) (A M : ℝ) (m : ℕ) (hm : 0 < m) : ℝ :=
  (Finset.range m).sup' ⟨0, Finset.mem_range.2 hm⟩ (cand a A M m)

variable {a : ℕ → ℝ} {A M : ℝ} {m : ℕ}

lemma vpt_nonneg (ha : ∀ i, 0 ≤ a i) (hA : 0 ≤ A) (i : ℕ) : 0 ≤ vpt a A i := by
  unfold vpt; split_ifs <;> simp_all

lemma cand_le_iff (ha : ∀ i, 0 ≤ a i) (hA : 0 ≤ A) (hM : 0 < M) {i : ℕ} (hi : i < m)
    {θ : ℝ} (hθ : 0 ≤ θ) : cand a A M m i ≤ θ ↔ vpt a A i ≤ M * θ ^ (m - i) := by
  have hz : (0 : ℝ) < ((m - i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  rw [cand, Real.rpow_inv_le_iff_of_pos (div_nonneg (vpt_nonneg ha hA i) hM.le) hθ hz,
    Real.rpow_natCast, div_le_iff₀ hM, mul_comm]

lemma cand_lt_iff (ha : ∀ i, 0 ≤ a i) (hA : 0 ≤ A) (hM : 0 < M) {i : ℕ} (hi : i < m)
    {θ : ℝ} (hθ : 0 ≤ θ) : cand a A M m i < θ ↔ vpt a A i < M * θ ^ (m - i) := by
  have hz : (0 : ℝ) < ((m - i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  rw [cand, Real.rpow_inv_lt_iff_of_pos (div_nonneg (vpt_nonneg ha hA i) hM.le) hθ hz,
    Real.rpow_natCast, div_lt_iff₀ hM, mul_comm]

lemma cand_nonneg (ha : ∀ i, 0 ≤ a i) (hA : 0 ≤ A) (hM : 0 < M) (i : ℕ) :
    0 ≤ cand a A M m i :=
  Real.rpow_nonneg (div_nonneg (vpt_nonneg ha hA i) hM.le) _

/-- `x θ^i ≤ M θ^m` iff `x ≤ M θ^(m - i)` for `i < m`, `θ > 0`. -/
lemma mul_pow_le_iff {x θ : ℝ} (hθ : 0 < θ) {i : ℕ} (hi : i ≤ m) :
    x * θ ^ i ≤ M * θ ^ m ↔ x ≤ M * θ ^ (m - i) := by
  have h : M * θ ^ m = M * θ ^ (m - i) * θ ^ i := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  rw [h, mul_le_mul_iff_left₀ (pow_pos hθ i)]

lemma mul_pow_lt_iff {x θ : ℝ} (hθ : 0 < θ) {i : ℕ} (hi : i ≤ m) :
    x * θ ^ i < M * θ ^ m ↔ x < M * θ ^ (m - i) := by
  have h : M * θ ^ m = M * θ ^ (m - i) * θ ^ i := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  rw [h, mul_lt_mul_iff_left₀ (pow_pos hθ i)]

/-- Terms beyond `m` are dominated for `θ < 1`. -/
lemma lt_of_gt (hD : Dom a M m) (hM : 0 < M) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {i : ℕ}
    (hi : m < i) : a i * θ ^ i < M * θ ^ m :=
  calc a i * θ ^ i ≤ M * θ ^ i := mul_le_mul_of_nonneg_right (hD.le i) (pow_nonneg hθ0.le _)
    _ < M * θ ^ m := mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hθ0 hθ1 hi) hM

variable (p : ℕ)

/-- **The critical radius** (Arzdorf, Cor. 2.23, Def. 2.30). Let `a` have maximum `M` attained
first at `m ≥ 1`, `0 < A < M`, `a₀ = 0`, and let the terms at positive indices `i < m` divisible by
`p` lie strictly below the segment from `P'₀ = (0, A)` to `P_m = (m, M)`. Then there are
`0 < θ₀ < 1` and `l < m` such that the index `m` strictly dominates on `(θ₀, 1)`, and at `θ₀`
either `A = M θ₀^m` (Artin–Schreier case) or `A < M θ₀^m` and `l` is the smallest dominant index,
`0 < l`, `p ∤ l` (purely inseparable case). -/
theorem exists_crit (hD : Dom a M m) (hm : 0 < m) (hA : 0 < A) (hAM : A < M)
    (ha0 : a 0 = 0) (hpm : ¬ p ∣ m)
    (hprec : ∀ i, 0 < i → i < m → p ∣ i → a i ^ m < A ^ (m - i) * M ^ i) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ θ₀ < 1 ∧ (∃ i < m, vpt a A i = M * θ₀ ^ (m - i)) ∧
      (∀ θ, θ₀ < θ → θ < 1 → (∀ i ≠ m, a i * θ ^ i < M * θ ^ m) ∧ A < M * θ ^ m) ∧
      (∀ i, a i * θ₀ ^ i ≤ M * θ₀ ^ m) ∧ A ≤ M * θ₀ ^ m ∧
      (∀ i, 0 < i → p ∣ i → a i * θ₀ ^ i < M * θ₀ ^ m) ∧
      (A = M * θ₀ ^ m ∨ ∃ l, 0 < l ∧ l < m ∧ ¬ p ∣ l ∧ A < M * θ₀ ^ m ∧
        a l * θ₀ ^ l = M * θ₀ ^ m ∧ ∀ i < l, a i * θ₀ ^ i < M * θ₀ ^ m) := by
  classical
  have hM : 0 < M := hA.trans hAM
  have ha := hD.nonneg
  set θ₀ := crit a A M m hm with hθ₀def
  have hmem : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.2 hm
  have hcand0 : cand a A M m 0 ≤ θ₀ := Finset.le_sup' (cand a A M m) hmem
  have hcand : ∀ i < m, cand a A M m i ≤ θ₀ := fun i hi ↦
    Finset.le_sup' (cand a A M m) (Finset.mem_range.2 hi)
  have hθ₀0' : 0 ≤ θ₀ := (cand_nonneg ha hA.le hM 0).trans hcand0
  -- `θ₀ > 0`: the virtual candidate is positive
  have hθ₀0 : 0 < θ₀ := by
    refine lt_of_lt_of_le ?_ hcand0
    exact Real.rpow_pos_of_pos (div_pos (by simp [vpt, hA]) hM) _
  -- `θ₀ < 1`
  have hθ₀1 : θ₀ < 1 := by
    obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup' ⟨0, hmem⟩ (cand a A M m)
    replace hieq : θ₀ = cand a A M m i := hieq
    rw [hieq, cand_lt_iff ha hA.le hM (Finset.mem_range.1 hi) zero_le_one, one_pow, mul_one]
    unfold vpt
    split_ifs
    · exact hAM
    · exact hD.lt i (Finset.mem_range.1 hi)
  -- every candidate is `≤ θ₀`: in terms of the polygon
  have hle : ∀ i < m, vpt a A i ≤ M * θ₀ ^ (m - i) := fun i hi ↦
    (cand_le_iff ha hA.le hM hi hθ₀0').1 (hcand i hi)
  have hAle : A ≤ M * θ₀ ^ m := by simpa [vpt] using hle 0 hm
  have hale : ∀ i, a i * θ₀ ^ i ≤ M * θ₀ ^ m := by
    intro i
    rcases lt_trichotomy i m with hi | rfl | hi
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [ha0, zero_mul]; exact mul_nonneg hM.le (pow_nonneg hθ₀0' _)
      · have := hle i hi
        rw [vpt, if_neg hi0.ne'] at this
        exact (mul_pow_le_iff hθ₀0 hi.le).2 this
    · rw [hD.eq]
    · exact (lt_of_gt hD hM hθ₀0 hθ₀1 hi).le
  -- `p`-indices are strictly below
  have hplt : ∀ i, 0 < i → p ∣ i → a i * θ₀ ^ i < M * θ₀ ^ m := by
    intro i hi0 hpi
    rcases lt_or_ge i m with hi | hi
    · rw [mul_pow_lt_iff hθ₀0 hi.le]
      have h1 := hprec i hi0 hi hpi
      have h2 : A ^ (m - i) * M ^ i ≤ (M * θ₀ ^ (m - i)) ^ m := by
        have : A ^ (m - i) ≤ (M * θ₀ ^ m) ^ (m - i) := pow_le_pow_left₀ hA.le hAle _
        calc A ^ (m - i) * M ^ i ≤ (M * θ₀ ^ m) ^ (m - i) * M ^ i :=
              mul_le_mul_of_nonneg_right this (pow_nonneg hM.le _)
          _ = (M * θ₀ ^ (m - i)) ^ m := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m (m - i)]
              have : M ^ (m - i) * M ^ i = M ^ m := by
                rw [← pow_add, Nat.sub_add_cancel hi.le]
              rw [← this]
              ring
      exact lt_of_pow_lt_pow_left₀ m (mul_nonneg hM.le (pow_nonneg hθ₀0' _)) (h1.trans_le h2)
    · rcases eq_or_lt_of_le hi with rfl | hi
      · exact absurd hpi hpm
      · exact lt_of_gt hD hM hθ₀0 hθ₀1 hi
  have hatt : ∃ i < m, vpt a A i = M * θ₀ ^ (m - i) := by
    obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup' ⟨0, hmem⟩ (cand a A M m)
    replace hieq : θ₀ = cand a A M m i := hieq
    have him := Finset.mem_range.1 hi
    refine ⟨i, him, ?_⟩
    rw [hieq, cand, Real.rpow_inv_natCast_pow (div_nonneg (vpt_nonneg ha hA.le i) hM.le)
      (Nat.sub_ne_zero_of_lt him), mul_div_cancel₀ _ hM.ne']
  refine ⟨θ₀, hθ₀0, hθ₀1, hatt, fun θ hθ hθ1 ↦ ?_, hale, hAle, hplt, ?_⟩
  · have hθ0 : 0 < θ := hθ₀0.trans hθ
    have hlt : ∀ i < m, vpt a A i < M * θ ^ (m - i) := fun i hi ↦
      (cand_lt_iff ha hA.le hM hi hθ0.le).1 ((hcand i hi).trans_lt hθ)
    refine ⟨fun i hi ↦ ?_, by simpa [vpt] using hlt 0 hm⟩
    rcases lt_or_gt_of_ne hi with hi | hi
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [ha0, zero_mul]; exact mul_pos hM (pow_pos hθ0 _)
      · have := hlt i hi
        rw [vpt, if_neg hi0.ne'] at this
        exact (mul_pow_lt_iff hθ0 hi.le).2 this
    · exact lt_of_gt hD hM hθ0 hθ1 hi
  · rcases eq_or_lt_of_le hAle with hAeq | hAlt
    · exact Or.inl hAeq
    right
    obtain ⟨i₀, hi₀, hieq⟩ := Finset.exists_mem_eq_sup' ⟨0, hmem⟩ (cand a A M m)
    replace hieq : θ₀ = cand a A M m i₀ := hieq
    have hi₀m := Finset.mem_range.1 hi₀
    have hge : M * θ₀ ^ (m - i₀) ≤ vpt a A i₀ := by
      have := (cand_lt_iff ha hA.le hM hi₀m hθ₀0').not.1 (by rw [hieq]; exact lt_irrefl _)
      exact not_lt.1 this
    have hi₀0 : i₀ ≠ 0 := by
      rintro rfl
      simp only [vpt, Nat.sub_zero] at hge
      exact absurd hAlt (not_lt.2 hge)
    have hex : ∃ i, 0 < i ∧ i < m ∧ a i * θ₀ ^ i = M * θ₀ ^ m := by
      refine ⟨i₀, Nat.pos_of_ne_zero hi₀0, hi₀m, le_antisymm (hale i₀) ?_⟩
      rw [vpt, if_neg hi₀0] at hge
      have : M * θ₀ ^ m = M * θ₀ ^ (m - i₀) * θ₀ ^ i₀ := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi₀m.le]
      rw [this]
      exact mul_le_mul_of_nonneg_right hge (pow_nonneg hθ₀0' _)
    set l := Nat.find hex with hl
    obtain ⟨hl0, hlm, hleq⟩ := Nat.find_spec hex
    refine ⟨l, hl0, hlm, fun hpl ↦ ?_, hAlt, hleq, fun i hi ↦ ?_⟩
    · exact absurd hleq (hplt l hl0 hpl).ne
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [ha0, zero_mul]; exact mul_pos hM (pow_pos hθ₀0 _)
      · refine lt_of_le_of_ne (hale i) fun heq ↦ ?_
        exact Nat.find_min hex hi ⟨hi0, hi.trans hlm, heq⟩

end Polygon

/-! ### Power series at a radius -/

section Series

open PTaylor KummerDisc

variable {C : Type*} [NormedField C]

/-- The term `‖gᵢ‖ ‖l‖^i` of `g` at the radius `‖l‖`. -/
noncomputable def term (g : PowerSeries C) (l : C) (i : ℕ) : ℝ := ‖coeff i g‖ * ‖l‖ ^ i

lemma term_nonneg (g : PowerSeries C) (l : C) (i : ℕ) : 0 ≤ term g l i :=
  mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

lemma term_eq_nnnorm (g : PowerSeries C) (l : C) (i : ℕ) :
    term g l i = ‖coeff i (rescale l g)‖₊ := by
  rw [term, coeff_rescale, coe_nnnorm, norm_mul, norm_pow, mul_comm]

lemma bnd_rescale {h : PowerSeries C} (hh : Bnd h 1) {l : C} (hl : ‖l‖ ≤ 1) :
    Bnd (rescale l h) 1 := fun i ↦ by
  rw [coeff_rescale, nnnorm_mul, nnnorm_pow]
  exact mul_le_one' (pow_le_one₀ zero_le (by exact_mod_cast hl)) (hh i)

lemma term_le_pow {g : PowerSeries C} (hg : Bnd g 1) (l : C) (i : ℕ) :
    term g l i ≤ ‖l‖ ^ i :=
  mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (by exact_mod_cast hg i)

/-- **The maximum is attained at a radius `< 1`.** -/
theorem exists_dom {g : PowerSeries C} (hg : Bnd g 1) {l : C} (hl : ‖l‖ < 1)
    {i₀ : ℕ} (hi₀ : 0 < term g l i₀) : ∃ M m, 0 < M ∧ Dom (term g l) M m := by
  classical
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hi₀ hl
  have hsmall : ∀ i, N ≤ i → term g l i < term g l i₀ := fun i hi ↦
    (term_le_pow hg l i).trans_lt
      ((pow_le_pow_of_le_one (norm_nonneg _) hl.le hi).trans_lt hN)
  have hi₀N : i₀ < N := by
    by_contra h
    exact lt_irrefl _ (hsmall i₀ (not_lt.1 h))
  have hne : (Finset.range N).Nonempty := ⟨i₀, Finset.mem_range.2 hi₀N⟩
  set M := (Finset.range N).sup' hne (term g l)
  have hle : ∀ i, term g l i ≤ M := by
    intro i
    rcases lt_or_ge i N with hi | hi
    · exact Finset.le_sup' (term g l) (Finset.mem_range.2 hi)
    · exact (hsmall i hi).le.trans (Finset.le_sup' (term g l) (Finset.mem_range.2 hi₀N))
  have hex : ∃ i, term g l i = M := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hne (term g l)
    exact ⟨i, hi.symm⟩
  refine ⟨M, Nat.find hex, hi₀.trans_le (hle i₀), ⟨term_nonneg g l, Nat.find_spec hex, hle,
    fun i hi ↦ lt_of_le_of_ne (hle i) fun h ↦ Nat.find_min hex hi h⟩⟩

variable [IsUltrametricDist C] (p : ℕ) [hp : Fact p.Prime]

/-- **Recognition of best approximations at a radius** (K2 rescaled). -/
theorem not_better_at {f h h' : PowerSeries C} (hh : Bnd h 1) (hh' : Bnd h' 1) {l : C}
    (hl : ‖l‖ ≤ 1) {M : ℝ} {m : ℕ} (hM : ‖(p : C)‖ ^ p < M ^ (p - 1)) (hm : ¬ p ∣ m)
    (hall : ∀ i, term (f - h ^ p) l i ≤ M) (heq : term (f - h ^ p) l m = M) :
    ¬ ((∀ i, term (f - h' ^ p) l i ≤ M) ∧ term (f - h' ^ p) l m < M) := by
  have hM0 : 0 ≤ M := heq ▸ term_nonneg _ _ _
  set M' : ℝ≥0 := ⟨M, hM0⟩
  have hM' : ‖(p : C)‖₊ ^ p < M' ^ (p - 1) := by
    rw [← NNReal.coe_lt_coe]; push_cast; exact hM
  have key := not_better (C := C) p (f := rescale l f) (h := rescale l h) (h' := rescale l h')
    (M := M') (m := m) hM' hm (bnd_rescale hh hl) (bnd_rescale hh' hl)
    (fun i ↦ by
      rw [← map_pow, ← map_sub, ← NNReal.coe_le_coe, ← term_eq_nnnorm]; exact hall i)
    (by rw [← map_pow, ← map_sub]; ext; rw [← term_eq_nnnorm]; exact heq)
  rintro ⟨h1, h2⟩
  refine key ⟨fun i ↦ ?_, ?_⟩
  · rw [← map_pow, ← map_sub, ← NNReal.coe_le_coe, ← term_eq_nnnorm]; exact h1 i
  · rw [← map_pow, ← map_sub, ← NNReal.coe_lt_coe, ← term_eq_nnnorm]; exact h2

omit hp in
lemma bnd_sub_pow {f h : PowerSeries C} (hf : Bnd f 1) (hh : Bnd h 1) : Bnd (f - h ^ p) 1 :=
  hf.sub ((hh.pow p).mono (by rw [one_pow]))

/-! ### The bounds of the `p`-Taylor expansion -/

variable {γ : C} (hγ : γ ^ (p - 1) = -(p : C)) (hp0 : (p : C) ≠ 0)

omit [IsUltrametricDist C] hp in
include hγ in
lemma norm_gamma_pow : ‖γ‖ ^ (p - 1) = ‖(p : C)‖ := by
  rw [← norm_pow, hγ, norm_neg]

omit [IsUltrametricDist C] in
include hγ hp0 in
lemma gamma_ne_zero : γ ≠ 0 := by
  rintro rfl
  rw [zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt), eq_comm, neg_eq_zero] at hγ
  exact hp0 hγ

include hγ in
lemma norm_gamma_le_one : ‖γ‖ ≤ 1 := by
  have h := norm_gamma_pow p hγ
  have h1 : ‖(p : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C p
  rw [← h] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Nat.sub_ne_zero_of_lt hp.out.one_lt)).1 h1

omit [IsUltrametricDist C] in
include hγ hp0 in
/-- `pBound C p n = ‖γ‖ ^ (p - 1/pⁿ) = A ^ (1 - 1/p^(n+1))`, `A = ‖γ‖^p`. -/
theorem pBound_eq (n : ℕ) :
    (pBound C p n : ℝ) = ‖γ‖ ^ ((p : ℝ) - ((p : ℝ) ^ n)⁻¹) := by
  have hγ0 : 0 < ‖γ‖ := norm_pos_iff.2 (gamma_ne_zero p hγ hp0)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  induction n with
  | zero =>
    rw [pBound, coe_nnnorm, ← norm_gamma_pow p hγ, ← Real.rpow_natCast, hp1, pow_zero, inv_one]
  | succ n ih =>
    rw [pBound, NNReal.coe_mul, NNReal.coe_rpow, ih, coe_nnnorm, ← norm_gamma_pow p hγ,
      ← Real.rpow_natCast, hp1, ← Real.rpow_mul hγ0.le, ← Real.rpow_add hγ0]
    congr 1
    field_simp
    ring

include hγ hp0 in
lemma le_pBound (n : ℕ) : ‖γ‖ ^ p ≤ (pBound C p n : ℝ) := by
  have hγ0 : 0 < ‖γ‖ := norm_pos_iff.2 (gamma_ne_zero p hγ hp0)
  rw [pBound_eq p hγ hp0, ← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_ge hγ0 (norm_gamma_le_one p hγ) ?_
  have : 0 ≤ ((p : ℝ) ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg p) n)
  linarith

omit [IsUltrametricDist C] in
include hγ hp0 in
lemma exists_pBound_lt {ε : ℝ} (hε : ‖γ‖ ^ p < ε) : ∃ n, (pBound C p n : ℝ) < ε := by
  have hγ0 : ‖γ‖ ≠ 0 := norm_ne_zero_iff.2 (gamma_ne_zero p hγ hp0)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hexp : Tendsto (fun n : ℕ ↦ (p : ℝ) - ((p : ℝ) ^ n)⁻¹) atTop (𝓝 (p : ℝ)) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp1))
    simpa using (tendsto_const_nhds (x := (p : ℝ))).sub this
  have hlim : Tendsto (fun n : ℕ ↦ (pBound C p n : ℝ)) atTop (𝓝 (‖γ‖ ^ p)) := by
    rw [← Real.rpow_natCast]
    simp_rw [pBound_eq p hγ hp0]
    exact (Real.continuousAt_const_rpow hγ0).tendsto.comp hexp
  exact (hlim.eventually (gt_mem_nhds hε)).exists

/-! ### K1: precise approximations -/

include hγ hp0 in
/-- **Precise approximations exist** (Arzdorf, Prop. 2.2, Cor. 2.16, 2.23, at a radius
`‖l‖ < 1`). For `f` with integral coefficients either `f` is approximable by `p`-th powers up to
every bound `> A = ‖γ‖^p` at the radius `‖l‖` (the degenerate case), or there is a *precise*
approximation `h`: `g = f - h^p` has `g₀ = 0`, maximum `M > A` at the radius `‖l‖` attained first
at an index `m` prime to `p`, and the terms at positive indices `i < m` divisible by `p` lie
strictly below the segment from `(0, A)` to `(m, M)`. -/
theorem exists_precise {f : PowerSeries C} (hf : Bnd f 1) [IsAlgClosed C] {l : C}
    (hl : ‖l‖ < 1) :
    (∀ ε, ‖γ‖ ^ p < ε → ∃ h : PowerSeries C, Bnd h 1 ∧ coeff 0 (f - h ^ p) = 0 ∧
        ∀ i, term (f - h ^ p) l i ≤ ε) ∨
      ∃ h : PowerSeries C, ∃ M : ℝ, ∃ m : ℕ, Bnd h 1 ∧ coeff 0 (f - h ^ p) = 0 ∧
        Dom (term (f - h ^ p) l) M m ∧ ¬ p ∣ m ∧ ‖γ‖ ^ p < M ∧
        ∀ i, 0 < i → i < m → p ∣ i →
          term (f - h ^ p) l i ^ m < (‖γ‖ ^ p) ^ (m - i) * M ^ i := by
  classical
  choose H hH1 hH0 hHp using fun n ↦ exists_pTaylor p hf n
  set A : ℝ := ‖γ‖ ^ p
  have hA0 : 0 < A := pow_pos (norm_pos_iff.2 (gamma_ne_zero p hγ hp0)) p
  have hl1 : ‖l‖ ≤ 1 := hl.le
  -- terms at `p`-indices are bounded by the level bound
  have hpterm : ∀ n j, term (f - H n ^ p) l (p * j) ≤ pBound C p n := fun n j ↦
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hl1)).trans
      (by exact_mod_cast hHp n j)
  by_cases hdeg : ∀ n i, term (f - H n ^ p) l i ≤ pBound C p n
  · left
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pBound_lt p hγ hp0 hε
    exact ⟨H n, hH1 n, hH0 n, fun i ↦ (hdeg n i).trans hn.le⟩
  right
  push Not at hdeg
  obtain ⟨n₀, i₀, hi₀⟩ := hdeg
  have hBA : ∀ n, A ≤ pBound C p n := le_pBound p hγ hp0
  have hG : ∀ n, Bnd (f - H n ^ p) 1 := fun n ↦ bnd_sub_pow p hf (hH1 n)
  obtain ⟨M, m, hM0, hD⟩ := exists_dom (hG n₀) hl ((pBound C p n₀).2.trans_lt hi₀)
  have hBM₀ : (pBound C p n₀ : ℝ) < M := hi₀.trans_le (hD.le i₀)
  have hpm : ¬ p ∣ m := by
    rintro ⟨j, rfl⟩
    exact absurd (hpterm n₀ j) (not_le.2 (hD.eq ▸ hBM₀))
  have hAM : A < M := (hBA n₀).trans_lt hBM₀
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h ↦ hpm (h ▸ dvd_zero p)
  -- `‖p‖^p < M'^(p-1)` for `M' > A`
  have hpM : ∀ M' : ℝ, A < M' → ‖(p : C)‖ ^ p < M' ^ (p - 1) := fun M' hM' ↦ by
    have h1 : ‖(p : C)‖ ^ p = A ^ (p - 1) := by
      rw [← norm_gamma_pow p hγ, ← pow_mul, ← pow_mul, mul_comm]
    rw [h1]
    exact pow_lt_pow_left₀ hM' hA0.le (Nat.sub_ne_zero_of_lt hp.out.one_lt)
  -- a level `n` with `pBound n ^ m < A^(m-1) M`
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  set ε : ℝ := (A ^ (m - 1) * M) ^ ((m : ℝ)⁻¹)
  have hAε : A < ε := by
    rw [Real.lt_rpow_inv_iff_of_pos hA0.le (mul_nonneg (pow_nonneg hA0.le _) hM0.le) hmR,
      Real.rpow_natCast]
    calc A ^ m = A ^ (m - 1) * A := by rw [← pow_succ, Nat.sub_add_cancel hm0]
      _ < A ^ (m - 1) * M := mul_lt_mul_of_pos_left hAM (pow_pos hA0 _)
  obtain ⟨n, hn⟩ := exists_pBound_lt p hγ hp0 (hAε : ‖γ‖ ^ p < ε)
  set B : ℝ := (pBound C p n : ℝ)
  have hB0 : 0 ≤ B := (pBound C p n).2
  have hBm : B ^ m < A ^ (m - 1) * M := by
    have := (Real.lt_rpow_inv_iff_of_pos hB0
      (mul_nonneg (pow_nonneg hA0.le (m - 1)) hM0.le) hmR).1 hn
    rwa [Real.rpow_natCast] at this
  have hBM : B < M := by
    refine lt_of_pow_lt_pow_left₀ m hM0.le (hBm.trans_le ?_)
    calc A ^ (m - 1) * M ≤ M ^ (m - 1) * M :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0.le hAM.le _) hM0.le
      _ = M ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm0]
  -- the data of level `n` coincide with those of level `n₀` (K2 in both directions)
  set a := term (f - H n₀ ^ p) l
  set a' := term (f - H n ^ p) l
  have hnb := not_better_at p (f := f) (hH1 n₀) (hH1 n) hl1 (hpM M hAM) hpm hD.le hD.eq
  have hpos : ∃ i, 0 < a' i := by
    by_cases hall : ∀ i, a' i ≤ M
    · exact ⟨m, hM0.trans_le (not_lt.1 fun h ↦ hnb ⟨hall, h⟩)⟩
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact ⟨i, hM0.trans hi⟩
  obtain ⟨i₁, hi₁⟩ := hpos
  obtain ⟨M', m', hM'0, hD'⟩ := exists_dom (hG n) hl hi₁
  have hMM' : M ≤ M' := by
    by_contra h
    push Not at h
    exact hnb ⟨fun i ↦ (hD'.le i).trans h.le, (hD'.le m).trans_lt h⟩
  have hpm' : ¬ p ∣ m' := by
    rintro ⟨j, rfl⟩
    exact absurd (hpterm n j) (not_le.2 (hD'.eq ▸ hBM.trans_le hMM'))
  have hnb' := not_better_at p (f := f) (hH1 n) (hH1 n₀) hl1 (hpM M' (hAM.trans_le hMM')) hpm'
    hD'.le hD'.eq
  have ham' : M' ≤ a m' := not_lt.1 fun h ↦ hnb' ⟨fun i ↦ (hD.le i).trans hMM', h⟩
  have hMeq : M' = M := le_antisymm (ham'.trans (hD.le m')) hMM'
  have hmm' : m ≤ m' := by
    by_contra h
    push Not at h
    exact absurd (hD.lt m' h) (not_lt.2 (hMeq ▸ ham'))
  have ha'm : M ≤ a' m := not_lt.1 fun h ↦ hnb ⟨fun i ↦ (hD'.le i).trans hMeq.le, h⟩
  have hm'm : m' ≤ m := by
    by_contra h
    push Not at h
    exact absurd (hD'.lt m h) (not_lt.2 (hMeq.symm ▸ ha'm))
  have hmeq : m' = m := le_antisymm hm'm hmm'
  subst hmeq hMeq
  refine ⟨H n, M', m', hH1 n, hH0 n, hD', hpm', hAM, fun i hi0 him hpi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := hpi
  calc a' (p * j) ^ m' ≤ B ^ m' := pow_le_pow_left₀ (term_nonneg _ _ _) (hpterm n j) _
    _ < A ^ (m' - 1) * M' := hBm
    _ ≤ A ^ (m' - p * j) * M' ^ (p * j) := by
      have h1 : A ^ (m' - 1) = A ^ (m' - p * j) * A ^ (p * j - 1) := by
        rw [← pow_add]; congr 1; omega
      have h2 : M' ^ (p * j) = M' ^ (p * j - 1) * M' := by
        rw [← pow_succ]; congr 1; omega
      rw [h1, h2, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA0.le _)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0.le hAM.le _) hM'0.le

/-! ### K4: the critical radius of a precise approximation -/

omit [IsUltrametricDist C] hp in
lemma term_mul (g : PowerSeries C) (l l' : C) (i : ℕ) :
    term g (l * l') i = term g l i * ‖l'‖ ^ i := by
  rw [term, term, norm_mul, mul_pow, mul_assoc]

omit [IsUltrametricDist C] in
include hγ hp0 in
/-- **The critical radius** (Arzdorf, Cor. 2.23, Prop. 2.28, Def. 2.30, at a radius `‖l‖ < 1`).
For a precise approximation `g = f - h^p` with data `(M, m)` at the radius `‖l‖`, there is
`l₀` with `0 < ‖l₀‖ < 1` such that at every radius `‖l l'‖`, `‖l₀‖ < ‖l'‖ < 1`, the index `m`
strictly dominates (with value `> A`), and at the critical radius `‖l l₀‖` all terms are bounded
by the `m`-th, the terms at positive `p`-indices strictly, and either the value is `A`
(Artin–Schreier case) or it is `> A` and the smallest dominant index `k` satisfies `0 < k < m`,
`p ∤ k` (purely inseparable case). -/
theorem exists_critRadius [IsAlgClosed C] {g : PowerSeries C} {l : C} {M : ℝ}
    {m : ℕ} (hD : Dom (term g l) M m) (hpm : ¬ p ∣ m) (hAM : ‖γ‖ ^ p < M)
    (hg0 : coeff 0 g = 0)
    (hprec : ∀ i, 0 < i → i < m → p ∣ i → term g l i ^ m < (‖γ‖ ^ p) ^ (m - i) * M ^ i) :
    ∃ l₀ : C, 0 < ‖l₀‖ ∧ ‖l₀‖ < 1 ∧
      (∀ l' : C, ‖l₀‖ < ‖l'‖ → ‖l'‖ < 1 →
        (∀ i ≠ m, term g (l * l') i < term g (l * l') m) ∧ ‖γ‖ ^ p < term g (l * l') m) ∧
      (∀ i, term g (l * l₀) i ≤ term g (l * l₀) m) ∧ ‖γ‖ ^ p ≤ term g (l * l₀) m ∧
      (∀ i, 0 < i → p ∣ i → term g (l * l₀) i < term g (l * l₀) m) ∧
      (‖γ‖ ^ p = term g (l * l₀) m ∨ ∃ k, 0 < k ∧ k < m ∧ ¬ p ∣ k ∧
        ‖γ‖ ^ p < term g (l * l₀) m ∧ term g (l * l₀) k = term g (l * l₀) m ∧
        ∀ i < k, term g (l * l₀) i < term g (l * l₀) m) := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h ↦ hpm (h ▸ dvd_zero p)
  have hA0 : 0 < ‖γ‖ ^ p := pow_pos (norm_pos_iff.2 (gamma_ne_zero p hγ hp0)) p
  have ha0 : term g l 0 = 0 := by rw [term, hg0, norm_zero, zero_mul]
  obtain ⟨θ₀, hθ₀0, hθ₀1, ⟨i₀, hi₀m, hi₀⟩, hdom, hle, hAle, hplt, hcase⟩ :=
    exists_crit p hD hm0 hA0 hAM ha0 hpm hprec
  have hM0 : 0 < M := hA0.trans hAM
  -- `θ₀` is a norm
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : C, ‖l₀‖ = θ₀ := by
    have hgm : coeff m g * l ^ m ≠ 0 := by
      intro h
      have : M = ‖coeff m g * l ^ m‖ := by rw [← hD.eq, term, norm_mul, norm_pow]
      rw [h, norm_zero] at this
      exact hM0.ne' this
    have hMn : M = ‖coeff m g * l ^ m‖ := by rw [← hD.eq, term, norm_mul, norm_pow]
    obtain ⟨c, hc⟩ : ∃ c : C, ‖c‖ = vpt (term g l) (‖γ‖ ^ p) i₀ / M := by
      by_cases h0 : i₀ = 0
      · refine ⟨γ ^ p / (coeff m g * l ^ m), ?_⟩
        rw [norm_div, norm_pow, ← hMn, vpt, if_pos h0]
      · refine ⟨coeff i₀ g * l ^ i₀ / (coeff m g * l ^ m), ?_⟩
        rw [norm_div, ← hMn, vpt, if_neg h0, term, norm_mul, norm_pow]
    have hk : m - i₀ ≠ 0 := Nat.sub_ne_zero_of_lt hi₀m
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hk)
    refine ⟨b, (pow_left_inj₀ (norm_nonneg b) hθ₀0.le hk).1 ?_⟩
    rw [← norm_pow, hb, hc, hi₀, mul_div_cancel_left₀ _ hM0.ne']
  have hterm : ∀ (l' : C) i, term g (l * l') i = term g l i * ‖l'‖ ^ i := term_mul g l
  have hMm : ∀ (l' : C), term g (l * l') m = M * ‖l'‖ ^ m := fun l' ↦ by rw [hterm, hD.eq]
  refine ⟨l₀, hl₀ ▸ hθ₀0, hl₀ ▸ hθ₀1, fun l' h1 h2 ↦ ?_, fun i ↦ ?_, ?_, fun i hi hpi ↦ ?_, ?_⟩
  · obtain ⟨H1, H2⟩ := hdom ‖l'‖ (hl₀ ▸ h1) h2
    exact ⟨fun i hi ↦ by rw [hterm, hMm]; exact H1 i hi, by rw [hMm]; exact H2⟩
  · rw [hterm, hMm, hl₀]; exact hle i
  · rw [hMm, hl₀]; exact hAle
  · rw [hterm, hMm, hl₀]; exact hplt i hi hpi
  · rcases hcase with h | ⟨k, hk0, hkm, hpk, hA, hkeq, hlt⟩
    · left; rw [hMm, hl₀]; exact h
    · right
      refine ⟨k, hk0, hkm, hpk, by rw [hMm, hl₀]; exact hA, by rw [hterm, hMm, hl₀]; exact hkeq,
        fun i hi ↦ by rw [hterm, hMm, hl₀]; exact hlt i hi⟩

end Series

end CriticalRadius

end SemistableReduction
