/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Wild

/-!
# The Artin–Schreier regime at a type-3 radius (Phase 2): termination

Blueprint §9.10a (I.3), Phase 2. Let `M` be the closure of `C(y)`, `‖y‖ ∉ |C^×|`, `π ∈ C` with
`π^(p-1) = -p`, `λ² = π`, `T = ‖λ‖⁻¹` and `ε₀ = max ‖λ‖ ‖π‖^(p-1) < 1`. Suppose
`u₀ / h^p = 1 + π^p c` with `‖c‖ ≤ T`. Approximate `c` by a Laurent polynomial `F`
(`‖c - F‖ ≤ ε₀`). For a term of `F` at an exponent `i` divisible by `p` replace `h` by
`h (1 + π b)` with `b^p - b` the term (`b = β y^{i/p}` for `i ≠ 0`, `b ∈ C` for `i = 0`); then
`c` changes by `-(b^p - b)` up to an error `≤ ε₀`, and `F` by `-(b^p - b)`. The measure
`Σ_{i ∈ supp F} (v_p(i) + 1)` drops, so the process terminates (`phase2`): either `‖c‖ < 1`, or
`‖c‖ > 1` and the dominant monomial of `c` has an exponent prime to `p`.
-/

open Finset

namespace SemistableReduction

namespace Type3

variable {C M : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [NormedField M] [IsUltrametricDist M] [NormedAlgebra C M]

/-- The weight of an exponent: `v_p(i) + 1` for `i ≠ 0`, `1` for `i = 0`. -/
def expWeight (p : ℕ) (i : ℤ) : ℕ := if i = 0 then 1 else padicValNat p i.natAbs + 1

/-- The termination measure of a Laurent polynomial. -/
noncomputable def lmeasure (p : ℕ) (F : ℤ →₀ C) : ℕ := ∑ i ∈ F.support, expWeight p i

lemma expWeight_pos (p : ℕ) (i : ℤ) : 0 < expWeight p i := by
  unfold expWeight; split_ifs <;> omega

lemma expWeight_div {p : ℕ} (hp : p.Prime) {i : ℤ} (hi : i ≠ 0) (hpi : (p : ℤ) ∣ i) :
    expWeight p (i / p) + 1 = expWeight p i := by
  haveI := Fact.mk hp
  have hip : i / p ≠ 0 := by
    intro h
    obtain ⟨k, rfl⟩ := hpi
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero)] at h
    exact hi (by rw [h, mul_zero])
  obtain ⟨k, rfl⟩ := hpi
  rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero)] at hip ⊢
  unfold expWeight
  rw [if_neg hip, if_neg hi, Int.natAbs_mul, Int.natAbs_natCast,
    padicValNat.mul hp.ne_zero (Int.natAbs_ne_zero.2 hip), padicValNat_self]
  ring

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma lmeasure_add_single_le (p : ℕ) (G : ℤ →₀ C) (j : ℤ) (β : C) :
    lmeasure p (G + Finsupp.single j β) ≤ lmeasure p G + expWeight p j := by
  classical
  unfold lmeasure
  calc ∑ i ∈ (G + Finsupp.single j β).support, expWeight p i
      ≤ ∑ i ∈ insert j G.support, expWeight p i := by
        refine Finset.sum_le_sum_of_subset fun i hi ↦ ?_
        rcases Finset.mem_union.1 (Finsupp.support_add hi) with h | h
        · exact Finset.mem_insert_of_mem h
        · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h
          split_ifs at h with hji
          · exact hji ▸ Finset.mem_insert_self _ _
          · exact absurd rfl h
    _ ≤ expWeight p j + ∑ i ∈ G.support, expWeight p i := by
        by_cases hj : j ∈ G.support
        · rw [Finset.insert_eq_of_mem hj]; omega
        · rw [Finset.sum_insert hj]
    _ = _ := add_comm _ _

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma lmeasure_erase (p : ℕ) (F : ℤ →₀ C) {i : ℤ} (hi : i ∈ F.support) :
    lmeasure p (F.erase i) + expWeight p i = lmeasure p F := by
  classical
  unfold lmeasure
  rw [Finsupp.support_erase, Finset.sum_erase_add _ _ hi]

section Step

variable {p : ℕ} (hp : p.Prime) {π lam : C} (hπ : π ^ (p - 1) = -(p : C)) (hlam : lam ^ 2 = π)
  (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
include hp hπ hlam hπ0 hπ1

omit [IsAlgClosed C] [IsUltrametricDist C] hπ in
/-- The numerical facts about `T = ‖λ‖⁻¹` and `ε₀`. -/
lemma as_consts : 0 < ‖lam‖ ∧ ‖lam‖ < 1 ∧ 1 ≤ ‖lam‖⁻¹ ∧ ‖π‖ * ‖lam‖⁻¹ = ‖lam‖ ∧
    ‖π‖ ^ p * ‖lam‖⁻¹ ^ 2 = ‖π‖ ^ (p - 1) ∧ max ‖lam‖ (‖π‖ ^ (p - 1)) < 1 := by
  have hl2 : ‖lam‖ ^ 2 = ‖π‖ := by rw [← norm_pow, hlam]
  have hl0 : 0 < ‖lam‖ := by
    rcases (norm_nonneg lam).lt_or_eq with h | h
    · exact h
    · rw [← h] at hl2; simp at hl2; exact absurd (norm_eq_zero.1 hl2.symm) hπ0
  have hl1 : ‖lam‖ < 1 := by nlinarith
  refine ⟨hl0, hl1, one_le_inv₀ hl0 |>.2 hl1.le, ?_, ?_, max_lt hl1
    (pow_lt_one₀ (norm_nonneg _) hπ1 (by have := hp.two_le; omega))⟩
  · rw [← hl2]; field_simp
  · obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_le; omega⟩
    rw [hq, Nat.add_sub_cancel, pow_succ, ← hl2]
    field_simp

omit [IsUltrametricDist C] in
/-- **One Artin–Schreier step.** -/
theorem as_step {y : M} (hy : IsValTrans C y) {u₀ h c : M} (hh : ‖h‖ = 1)
    (hc : u₀ / h ^ p = 1 + algebraMap C M π ^ p * c) (hcT : ‖c‖ ≤ ‖lam‖⁻¹) {F : ℤ →₀ C}
    (hF : ‖c - lev y F‖ ≤ max ‖lam‖ (‖π‖ ^ (p - 1))) {i : ℤ} (hi : i ∈ F.support)
    (hpi : (p : ℤ) ∣ i) :
    ∃ (h' c' : M) (F' : ℤ →₀ C), ‖h'‖ = 1 ∧ u₀ / h' ^ p = 1 + algebraMap C M π ^ p * c' ∧
      ‖c'‖ ≤ ‖lam‖⁻¹ ∧ ‖c' - lev y F'‖ ≤ max ‖lam‖ (‖π‖ ^ (p - 1)) ∧
        lmeasure p F' < lmeasure p F := by
  classical
  obtain ⟨hl0, hl1, hT1, hπT, hπT2, hε0⟩ := as_consts hp hlam hπ0 hπ1
  set T := ‖lam‖⁻¹
  set ε₀ := max ‖lam‖ (‖π‖ ^ (p - 1))
  have hlevF : ‖lev y F‖ ≤ T := by
    have := IsUltrametricDist.norm_add_le_max c (-(c - lev y F))
    rw [norm_neg, show c + -(c - lev y F) = lev y F by ring] at this
    exact this.trans (max_le hcT (hF.trans (hε0.le.trans hT1)))
  have htm : tm y F i ≤ T := (tm_le hy F i).trans hlevF
  -- the correction `b` and the new Laurent polynomial `G`
  obtain ⟨b, G, hbG, hb, hμ⟩ : ∃ (b : M) (G : ℤ →₀ C), lev y G = lev y F - (b ^ p - b) ∧
      max 1 ‖b‖ ^ p ≤ T ∧ lmeasure p G < lmeasure p F := by
    have hsplit : lev y F = lev y (F.erase i) + mono y (F i) i := by
      rw [← lev_single, ← lev_add, add_comm, Finsupp.single_add_erase]
    have hmerase := lmeasure_erase p F hi
    by_cases hi0 : i = 0
    · subst hi0
      obtain ⟨b₀, hb₀⟩ := IsAlgClosed.exists_root
        (Polynomial.X ^ p - Polynomial.X - Polynomial.C (F 0)) (by
          rw [Polynomial.degree_sub_C (by
            rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
              simp [hp.one_lt, hp.pos])]
          rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
            simp [hp.one_lt, hp.ne_zero])
      have hb₀' : b₀ ^ p - b₀ = F 0 := by
        simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C] at hb₀
        linear_combination hb₀
      refine ⟨algebraMap C M b₀, F.erase 0, ?_, ?_, ?_⟩
      · rw [hsplit, mono, zpow_zero, mul_one, ← hb₀', map_sub, map_pow]
        ring
      · have hn : ‖algebraMap C M b₀ ^ p - algebraMap C M b₀‖ ≤ T := by
          rw [← map_pow, ← map_sub, norm_algebraMap', hb₀']
          simpa [tm] using htm
        rcases le_or_gt ‖algebraMap C M b₀‖ 1 with h1 | h1
        · rw [max_eq_left h1, one_pow]; exact hT1
        · rw [max_eq_right h1.le]
          have hlt : ‖algebraMap C M b₀‖ < ‖algebraMap C M b₀ ^ p‖ := by
            rw [norm_pow]
            exact lt_self_pow₀ h1 hp.one_lt
          have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
            (x := algebraMap C M b₀ ^ p) (y := -algebraMap C M b₀) (by rw [norm_neg]; exact hlt.ne')
          rw [norm_neg, max_eq_left hlt.le, ← sub_eq_add_neg] at this
          rw [← norm_pow, ← this]
          exact hn
      · have := expWeight_pos p 0
        omega
    · obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (F i) hp.pos
      set bb := mono y β (i / p)
      have hbp : bb ^ p = mono y (F i) i := by
        simp only [bb]
        rw [mono_pow, hβ, Int.mul_ediv_cancel' hpi]
      refine ⟨bb, F.erase i + Finsupp.single (i / p) β, ?_, ?_, ?_⟩
      · rw [lev_add, lev_single, hsplit, hbp]
        ring
      · have h1 : ‖bb‖ ^ p ≤ T := by rw [← norm_pow, hbp, norm_mono]; exact htm
        rcases le_or_gt ‖bb‖ 1 with h2 | h2
        · rw [max_eq_left h2, one_pow]; exact hT1
        · rw [max_eq_right h2.le]; exact h1
      · have h1 := lmeasure_add_single_le p (F.erase i) (i / p) β
        have h2 := expWeight_div hp hi0 hpi
        omega
  -- numerical bounds on `b`
  have hmax1 : 1 ≤ max 1 ‖b‖ := le_max_left _ _
  have hbT : ‖b‖ ≤ T :=
    (le_max_right 1 ‖b‖).trans ((le_self_pow₀ hmax1 hp.ne_zero).trans hb)
  have hbpb : ‖b ^ p - b‖ ≤ T := by
    refine (norm_sub_le_max' _ _).trans (max_le ?_ hbT)
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖b‖) p).trans hb
  set π' := algebraMap C M π
  have hπ'n : ‖π'‖ = ‖π‖ := norm_algebraMap' M π
  have hπ' : π' ^ (p - 1) = -(p : M) := by
    rw [← map_pow, hπ, map_neg, map_natCast]
  have hπ'0 : π' ≠ 0 := (map_ne_zero _).2 hπ0
  have hπp : ‖π' ^ p‖ = ‖π‖ ^ p := by rw [norm_pow, hπ'n]
  have hπp0 : 0 < ‖π‖ ^ p := pow_pos (norm_pos_iff.2 hπ0) p
  have hmid : ‖pmid p π' b‖ ≤ ‖π‖ ^ (p + 1) * T := by
    refine (norm_pmid_le hp hπ' (hπ'n ▸ hπ1.le) b).trans ?_
    rw [hπ'n]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (pow_le_pow_right₀ hmax1 (Nat.sub_le p 1)).trans hb
  set D := (1 + π' * b) ^ p with hD
  have hDexp : D = 1 + π' ^ p * (b ^ p - b) + pmid p π' b := one_add_pi_pow hp hπ' b
  have hD1 : ‖D - 1‖ ≤ ‖π‖ ^ p * T := by
    rw [hDexp, show 1 + π' ^ p * (b ^ p - b) + pmid p π' b - 1 =
      π' ^ p * (b ^ p - b) + pmid p π' b by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, hπp]; exact mul_le_mul_of_nonneg_left hbpb hπp0.le
    · refine hmid.trans ?_
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hπp0.le hπ1.le) (by positivity)
  have hπpT : ‖π‖ ^ p * T < 1 := by
    calc ‖π‖ ^ p * T ≤ ‖π‖ * T := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact pow_le_of_le_one (norm_nonneg _) hπ1.le hp.ne_zero
      _ = ‖lam‖ := hπT
      _ < 1 := hl1
  have hDn : ‖D‖ = 1 := norm_eq_one_of_norm_sub_one_lt (hD1.trans_lt hπpT)
  have hD0 : D ≠ 0 := by intro h0; rw [h0, norm_zero] at hDn; exact zero_ne_one hDn
  have hub : ‖1 + π' * b‖ = 1 := by
    refine norm_eq_one_of_norm_sub_one_lt ?_
    rw [add_sub_cancel_left, norm_mul, hπ'n]
    calc ‖π‖ * ‖b‖ ≤ ‖π‖ * T := mul_le_mul_of_nonneg_left hbT (norm_nonneg _)
      _ < 1 := hπT ▸ hl1
  have hub0 : 1 + π' * b ≠ 0 := by intro h0; rw [h0, norm_zero] at hub; exact zero_ne_one hub
  set N := c - (b ^ p - b) - pmid p π' b / π' ^ p with hN
  have hmidπ : ‖pmid p π' b / π' ^ p‖ ≤ ‖lam‖ := by
    rw [norm_div, hπp, div_le_iff₀ hπp0, ← hπT]
    calc ‖pmid p π' b‖ ≤ ‖π‖ ^ (p + 1) * T := hmid
      _ = ‖π‖ * T * ‖π‖ ^ p := by ring
  have hNT : ‖N‖ ≤ T :=
    (norm_sub_le_max' _ _).trans (max_le ((norm_sub_le_max' _ _).trans (max_le hcT hbpb))
      (hmidπ.trans (hl1.le.trans hT1)))
  set h' := h * (1 + π' * b)
  set c' := N / D
  have hh' : ‖h'‖ = 1 := by rw [norm_mul, hh, hub, one_mul]
  have hc' : u₀ / h' ^ p = 1 + π' ^ p * c' := by
    have hhp : h ^ p ≠ 0 := pow_ne_zero _ (by intro h0; rw [h0, norm_zero] at hh; simp at hh)
    have e1 : u₀ / h' ^ p = (u₀ / h ^ p) / D := by
      simp only [h', hD, mul_pow]; field_simp
    have hNπ : π' ^ p * N = π' ^ p * c - (D - 1) := by
      rw [hN, hDexp]
      field_simp
      ring
    rw [e1, hc, show π' ^ p * c' = π' ^ p * N / D by simp only [c', mul_div_assoc], hNπ]
    field_simp
    ring
  refine ⟨h', c', G, hh', hc', ?_, ?_, hμ⟩
  · simp only [c']; rw [norm_div, hDn, div_one]; exact hNT
  · -- `c' - G = (c - F) + N (1 - D) / D - pmid b / π^p`
    have e2 : c' - lev y G = (c - lev y F) + (N * (1 - D) / D - pmid p π' b / π' ^ p) := by
      simp only [c', hbG]
      field_simp
      rw [hN]
      field_simp
      ring
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hF ((norm_sub_le_max' _ _).trans
      (max_le ?_ (hmidπ.trans (le_max_left _ _)))))
    rw [norm_div, hDn, div_one, norm_mul, norm_sub_rev 1 D]
    calc ‖N‖ * ‖D - 1‖ ≤ T * (‖π‖ ^ p * T) := mul_le_mul hNT hD1 (norm_nonneg _) (by positivity)
      _ = ‖π‖ ^ p * T ^ 2 := by ring
      _ = ‖π‖ ^ (p - 1) := hπT2
      _ ≤ ε₀ := le_max_right _ _

omit [IsUltrametricDist C] hp hπ hlam hπ0 hπ1 in
/-- The dominant monomial of a Laurent polynomial dominates the rest. -/
lemma norm_lev_sub_mono_lt {y : M} (hy : IsValTrans C y) {F : ℤ →₀ C} {n : ℤ} (hn0 : F n ≠ 0)
    (hn : ‖lev y F‖ = tm y F n) (hdom : ∀ m, m ≠ n → tm y F m < tm y F n) :
    ‖lev y F - mono y (F n) n‖ < ‖lev y F‖ := by
  classical
  rw [← lev_single, ← lev_sub, hn]
  set g := F - Finsupp.single n (F n)
  rcases eq_or_ne g 0 with hg | hg
  · rw [hg, lev_zero, norm_zero]
    exact mul_pos (norm_pos_iff.2 hn0) (zpow_pos hy.norm_pos _)
  obtain ⟨m, hm0, hm, -⟩ := exists_dom hy hg
  have hmn : m ≠ n := by
    rintro rfl
    exact hm0 (by simp [g])
  rw [hm]
  have : tm y g m = tm y F m := by simp [tm, g, hmn]
  rw [this]
  exact hdom m hmn

omit [IsUltrametricDist C] in
/-- **Phase 2: termination of the Artin–Schreier iteration.** -/
theorem phase2 {y : M} (hy : IsValTrans C y) {u₀ : M} :
    ∀ (n : ℕ) (h c : M) (F : ℤ →₀ C), lmeasure p F = n → ‖h‖ = 1 →
      u₀ / h ^ p = 1 + algebraMap C M π ^ p * c → ‖c‖ ≤ ‖lam‖⁻¹ →
      ‖c - lev y F‖ ≤ max ‖lam‖ (‖π‖ ^ (p - 1)) →
      ∃ h' c' : M, ‖h'‖ = 1 ∧ u₀ / h' ^ p = 1 + algebraMap C M π ^ p * c' ∧
        (‖c'‖ < 1 ∨ (1 < ‖c'‖ ∧ ∃ a : C, a ≠ 0 ∧ ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ ∃ ε : M, ‖ε‖ < 1 ∧
          c' = algebraMap C M a * y ^ m * (1 + ε))) := by
  classical
  obtain ⟨hl0, hl1, hT1, -, -, hε0⟩ := as_consts hp hlam hπ0 hπ1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h c F hn hh hc hcT hF
  by_cases hex : ∃ i ∈ F.support, (p : ℤ) ∣ i
  · obtain ⟨i, hi, hpi⟩ := hex
    obtain ⟨h', c', F', hh', hc', hcT', hF', hμ⟩ :=
      as_step hp hπ hlam hπ0 hπ1 hy hh hc hcT hF hi hpi
    exact ih _ (hn ▸ hμ) h' c' F' rfl hh' hc' hcT' hF'
  push Not at hex
  refine ⟨h, c, hh, hc, ?_⟩
  rcases lt_or_ge ‖c‖ 1 with hc1 | hc1
  · exact Or.inl hc1
  right
  set ε₀ := max ‖lam‖ (‖π‖ ^ (p - 1))
  have hlc : ‖lev y F‖ = ‖c‖ := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := c) (y := -(c - lev y F))
      (by rw [norm_neg]; exact (hF.trans_lt (hε0.trans_le hc1)).ne')
    rwa [norm_neg, max_eq_left (hF.trans (hε0.le.trans hc1)),
      show c + -(c - lev y F) = lev y F by ring] at this
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [lev_zero, norm_zero] at hlc
    linarith
  obtain ⟨m, hm0, hm, hdom⟩ := exists_dom hy hF0
  have hmF : m ∈ F.support := Finsupp.mem_support_iff.2 hm0
  have hpm := hex m hmF
  have hm00 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero _)
  have hc1' : 1 < ‖c‖ := by
    refine lt_of_le_of_ne hc1 fun h1 ↦ ?_
    apply hy.ne_norm_mul_zpow hm0 hm00 1
    rw [norm_one, h1, ← hlc, hm]
    rfl
  refine ⟨hc1', F m, hm0, m, hpm, c / mono y (F m) m - 1, ?_, ?_⟩
  · have hmn : ‖mono y (F m) m‖ = ‖c‖ := by rw [norm_mono, ← hlc, hm]; rfl
    have hmono0 : mono y (F m) m ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hmn; linarith
    rw [show c / mono y (F m) m - 1 = (c - mono y (F m) m) / mono y (F m) m by
      field_simp, norm_div, hmn, div_lt_one (by linarith)]
    have h1 := norm_lev_sub_mono_lt hy hm0 hm hdom
    rw [hlc] at h1
    have := IsUltrametricDist.norm_add_le_max (c - lev y F) (lev y F - mono y (F m) m)
    rw [show c - lev y F + (lev y F - mono y (F m) m) = c - mono y (F m) m by ring] at this
    exact this.trans_lt (max_lt (hF.trans_lt (hε0.trans hc1')) h1)
  · have hmono0 : mono y (F m) m ≠ 0 := by
      rw [mono]
      exact mul_ne_zero ((map_ne_zero _).2 hm0) (zpow_ne_zero _ hy.ne_zero)
    rw [add_sub_cancel, ← mono]
    field_simp

end Step

end Type3

end SemistableReduction
