/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LaurentSplit

/-!
# Lifting sections of the special fibre

Blueprint §9.9, S7⁺.5. For `m ≫ 0`, every section of `O(m (x̄)_∞)` on the special fibre of the
normalization of `ℙ¹_{O_C}` in `F` (an element `ā = x̄ᵐ b̄` with `a` in the chart ring at `0` and
`b` in the chart ring at `∞`) is the reduction of some `f ∈ L(m (x)_∞)` of norm `≤ 1`
(`exists_lift`): integral Serre vanishing.

Proof: in the chart basis `s` (S7⁺.2) the coordinates of `d = a - xᵐ b` are rational functions
regular on the unit circle (`circRing`, S7⁺.3) of Gauss norm `‖d‖ < 1`; split them (S7⁺.4) into a
part regular on `|x| ≤ 1` and a part regular on `|x| ≥ 1`, and move the first part to `a`, the
second to `xᵐ b`. Poles are controlled place by place.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability CurvePlace

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C]

section Reflect

lemma roots_reflect_lt {q : C[X]} (hq0 : q ≠ 0) {N : ℕ} (hN : q.natDegree ≤ N)
    (hq : ∀ α ∈ q.roots, 1 < ‖α‖) : ∀ α ∈ (reflect N q).roots, ‖α‖ < 1 := by
  intro α hα
  have hr0 : reflect N q ≠ 0 := by simpa [reflect_eq_zero_iff] using hq0
  rcases eq_or_ne α 0 with rfl | h0
  · simp
  have hroot : eval α (reflect N q) = 0 := (mem_roots hr0).1 hα
  letI : Invertible α⁻¹ := invertibleOfNonzero (inv_ne_zero h0)
  have h := (eval₂_reflect_eq_zero_iff (RingHom.id C) α⁻¹ N q hN).1 (by
    rw [invOf_eq_inv, inv_inv]; exact hroot)
  have := hq α⁻¹ ((mem_roots hq0).2 h)
  rw [norm_inv] at this
  exact (one_lt_inv₀ (norm_pos_iff.2 h0)).1 this

lemma roots_reflect_gt {q : C[X]} (hq0 : q ≠ 0) (hq : ∀ α ∈ q.roots, ‖α‖ < 1) :
    ∀ α ∈ (reflect q.natDegree q).roots, 1 < ‖α‖ := by
  intro α hα
  have hr0 : reflect q.natDegree q ≠ 0 := by simpa [reflect_eq_zero_iff] using hq0
  have hroot : eval α (reflect q.natDegree q) = 0 := (mem_roots hr0).1 hα
  have h0 : α ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero,
      coeff_natDegree, leadingCoeff_eq_zero] at hroot
    exact hq0 hroot
  letI : Invertible α⁻¹ := invertibleOfNonzero (inv_ne_zero h0)
  have h := (eval₂_reflect_eq_zero_iff (RingHom.id C) α⁻¹ q.natDegree q le_rfl).1 (by
    rw [invOf_eq_inv, inv_inv]; exact hroot)
  have := hq α⁻¹ ((mem_roots hq0).2 h)
  rw [norm_inv] at this
  exact (inv_lt_one₀ (norm_pos_iff.2 h0)).1 this

end Reflect

section Circ

variable (C) in
/-- The rational functions regular on the unit circle `|x| = 1`: `P / (Q_out Q_in)` with the
roots of `Q_out` in `|α| > 1` and those of `Q_in` in `|α| < 1`. -/
def circRing : Subring (RatFunc C) where
  carrier := {φ | ∃ P Qo Qi : C[X], Qo ≠ 0 ∧ Qi ≠ 0 ∧ (∀ α ∈ Qo.roots, 1 < ‖α‖) ∧
    (∀ α ∈ Qi.roots, ‖α‖ < 1) ∧
      φ = algebraMap C[X] (RatFunc C) P / algebraMap C[X] (RatFunc C) (Qo * Qi)}
  mul_mem' := by
    rintro _ _ ⟨P, Qo, Qi, hQo, hQi, ho, hi, rfl⟩ ⟨P', Qo', Qi', hQo', hQi', ho', hi', rfl⟩
    refine ⟨P * P', Qo * Qo', Qi * Qi', mul_ne_zero hQo hQo', mul_ne_zero hQi hQi', ?_, ?_, ?_⟩
    · intro α hα
      rw [roots_mul (mul_ne_zero hQo hQo'), Multiset.mem_add] at hα
      exact hα.elim (ho α) (ho' α)
    · intro α hα
      rw [roots_mul (mul_ne_zero hQi hQi'), Multiset.mem_add] at hα
      exact hα.elim (hi α) (hi' α)
    · rw [div_mul_div_comm, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
      congr 1
      ring
  one_mem' := ⟨1, 1, 1, one_ne_zero, one_ne_zero, by simp, by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨P, Qo, Qi, hQo, hQi, ho, hi, rfl⟩ ⟨P', Qo', Qi', hQo', hQi', ho', hi', rfl⟩
    refine ⟨P * Qo' * Qi' + P' * Qo * Qi, Qo * Qo', Qi * Qi', mul_ne_zero hQo hQo',
      mul_ne_zero hQi hQi', ?_, ?_, ?_⟩
    · intro α hα
      rw [roots_mul (mul_ne_zero hQo hQo'), Multiset.mem_add] at hα
      exact hα.elim (ho α) (ho' α)
    · intro α hα
      rw [roots_mul (mul_ne_zero hQi hQi'), Multiset.mem_add] at hα
      exact hα.elim (hi α) (hi' α)
    · have h1 : algebraMap C[X] (RatFunc C) Qo ≠ 0 := by simpa using hQo
      have h2 : algebraMap C[X] (RatFunc C) Qi ≠ 0 := by simpa using hQi
      have h3 : algebraMap C[X] (RatFunc C) Qo' ≠ 0 := by simpa using hQo'
      have h4 : algebraMap C[X] (RatFunc C) Qi' ≠ 0 := by simpa using hQi'
      rw [div_add_div _ _ (by rw [map_mul]; exact mul_ne_zero h1 h2)
        (by rw [map_mul]; exact mul_ne_zero h3 h4)]
      simp only [map_mul, map_add]
      congr 1 <;> ring
  zero_mem' := ⟨0, 1, 1, one_ne_zero, one_ne_zero, by simp, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨P, Qo, Qi, hQo, hQi, ho, hi, rfl⟩
    exact ⟨-P, Qo, Qi, hQo, hQi, ho, hi, by simp [neg_div]⟩

lemma algebraMap_mem_circRing (P : C[X]) : algebraMap C[X] (RatFunc C) P ∈ circRing C :=
  ⟨P, 1, 1, one_ne_zero, one_ne_zero, by simp, by simp, by simp⟩

lemma inv_mem_circRing_out {Q : C[X]} (hQ : Q ≠ 0) (h : ∀ α ∈ Q.roots, 1 < ‖α‖) :
    (algebraMap C[X] (RatFunc C) Q)⁻¹ ∈ circRing C :=
  ⟨1, Q, 1, hQ, one_ne_zero, h, by simp, by simp⟩

lemma inv_mem_circRing_in {Q : C[X]} (hQ : Q ≠ 0) (h : ∀ α ∈ Q.roots, ‖α‖ < 1) :
    (algebraMap C[X] (RatFunc C) Q)⁻¹ ∈ circRing C :=
  ⟨1, 1, Q, one_ne_zero, hQ, by simp, h, by simp⟩

lemma X_mem_circRing : (RatFunc.X : RatFunc C) ∈ circRing C := by
  simpa using algebraMap_mem_circRing (C := C) X

lemma X_inv_mem_circRing : (RatFunc.X : RatFunc C)⁻¹ ∈ circRing C := by
  simpa using inv_mem_circRing_in (C := C) X_ne_zero (by simp)

lemma aeval_mem_circRing {φ : RatFunc C} (hφ : φ ∈ circRing C) (P : C[X]) :
    aeval φ P ∈ circRing C := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ ↦ ?_
  rw [Algebra.smul_def]
  refine mul_mem ?_ (pow_mem hφ _)
  simpa using algebraMap_mem_circRing (C := C) (Polynomial.C (P.coeff i))

lemma inv_aeval_X_inv_mem_circRing {q : C[X]} (hq : q ≠ 0) (h : ∀ α ∈ q.roots, 1 < ‖α‖) :
    (aeval (RatFunc.X : RatFunc C)⁻¹ q)⁻¹ ∈ circRing C := by
  rw [aeval_X_inv, mul_inv, inv_pow, inv_inv]
  refine mul_mem (inv_mem_circRing_in (by simpa using hq) ?_) (pow_mem X_mem_circRing _)
  exact roots_reflect_lt hq le_rfl h

end Circ

variable [IsUltrametricDist C]

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "vC" => NormedField.valuation (K := C)

section Places

variable {F : Type*} [Field F] [Algebra C F]

omit [IsUltrametricDist C] in
/-- An element integral over a ring whose image lies in the valuation ring of `v` lies in it. -/
lemma valuation_le_one_of_isIntegral {R : Type*} [CommRing R] [Algebra R F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}
    (hR : ∀ r : R, v (algebraMap R F r) ≤ 1) {f : F} (hf : IsIntegral R f) : v f ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hf
  by_contra hlt
  push Not at hlt
  have hn : p.natDegree ≠ 0 := by
    intro hn
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    rw [Monic, leadingCoeff_C] at hm
    simp [hm] at hp
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hp
  apply_fun v at hp
  simp only [Valuation.map_neg, map_pow] at hp
  refine (ne_of_lt (v.map_sum_lt (g := v f ^ p.natDegree) ?_ ?_)) hp
  · simp [hn, (hlt.trans' zero_lt_one).ne']
  · simp only [Finset.mem_range, map_mul, map_pow]
    intro i hi
    exact mul_lt_of_le_one_of_lt (hR _) (pow_lt_pow_right₀ hlt hi)

variable [IsAlgClosed C] [IsCurveFunctionField C F]

omit [IsUltrametricDist C] in
lemma adjoin_le_V (P : CurvePlace C F) {t : F} (ht : t ∈ P.V) (r : Algebra.adjoin C {t}) :
    P.valuation (algebraMap _ F r) ≤ 1 := by
  rw [P.valuation_le_one_iff]
  obtain ⟨r, hr⟩ := r
  change r ∈ P.V
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact ht
  | algebraMap c => exact P.algebraMap_mem c
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

omit [IsUltrametricDist C] in
lemma mem_V_of_isIntegral (P : CurvePlace C F) {t f : F} (ht : t ∈ P.V)
    (hf : IsIntegral (Algebra.adjoin C {t}) f) : f ∈ P.V :=
  P.valuation_le_one_iff.1 (valuation_le_one_of_isIntegral (adjoin_le_V P ht) hf)

omit [IsUltrametricDist C] in
lemma aeval_mem_V (P : CurvePlace C F) {y : F} (hy : y ∈ P.V) (Q : C[X]) : aeval y Q ∈ P.V :=
  P.valuation_le_one_iff.1 (valuation_aeval_le_one P.valuation_algebraMap_le_one
    (P.valuation_le_one_iff.2 hy) Q)

omit [IsUltrametricDist C] in
/-- `Q(y)` is a unit at `P` if `Q` does not vanish at the residue of `y`. -/
lemma valuation_aeval_eq_one (P : CurvePlace C F) {y : F} (hy : y ∈ P.V) {Q : C[X]}
    (hQ : Q.eval (P.res y) ≠ 0) : P.valuation (aeval y Q) = 1 := by
  set c := P.res y
  set R := (Q - Polynomial.C (Q.eval c)) /ₘ (X - Polynomial.C c)
  have hR : (X - Polynomial.C c) * R = Q - Polynomial.C (Q.eval c) :=
    mul_divByMonic_eq_iff_isRoot.2 (by simp)
  have h : aeval y Q = algebraMap C F (Q.eval c) + (y - algebraMap C F c) * aeval y R := by
    have := congrArg (aeval y) hR
    simp only [map_mul, _root_.map_sub, aeval_X, aeval_C] at this
    rw [this]
    ring
  rw [h, Valuation.map_add_eq_of_lt_left (v := P.valuation)]
  · exact valuation_algebraMap_eq_one P.valuation_algebraMap_le_one hQ
  · rw [valuation_algebraMap_eq_one P.valuation_algebraMap_le_one hQ, map_mul]
    exact mul_lt_one_of_lt_of_le (P.valuation_sub_res_lt_one hy)
      (P.valuation_le_one_iff.2 (aeval_mem_V P hy R))

omit [IsUltrametricDist C] in
/-- The residue of an inverse. -/
lemma res_inv (P : CurvePlace C F) {y : F} (hy : y ∈ P.V) (h0 : P.res y ≠ 0) :
    y⁻¹ ∈ P.V ∧ P.res y⁻¹ = (P.res y)⁻¹ := by
  set c := P.res y
  have hlt := P.valuation_sub_res_lt_one hy
  have hc1 : P.valuation (algebraMap C F c) = 1 :=
    valuation_algebraMap_eq_one P.valuation_algebraMap_le_one h0
  have hy1 : P.valuation y = 1 := by
    have hlt' : P.valuation (y - algebraMap C F c) < P.valuation (algebraMap C F c) := by
      rw [hc1]; exact hlt
    have : y = algebraMap C F c + (y - algebraMap C F c) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left (v := P.valuation) hlt', hc1]
  have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hy1
  have hyinv : y⁻¹ ∈ P.V := P.valuation_le_one_iff.1 (by rw [map_inv₀, hy1, inv_one])
  refine ⟨hyinv, P.res_eq_of_valuation_sub_lt_one ?_⟩
  have hc0 : algebraMap C F c ≠ 0 := by simpa using h0
  have : y⁻¹ - algebraMap C F c⁻¹ = (algebraMap C F c - y) * (y⁻¹ * algebraMap C F c⁻¹) := by
    rw [map_inv₀]
    field_simp
  rw [this]
  simp only [map_mul, map_inv₀, hy1, hc1, inv_one, mul_one]
  rw [← Valuation.map_neg, neg_sub]
  exact hlt

omit [IsUltrametricDist C] in
/-- An element integral over `C[t]` has `t^{-D} f` integral over `C[t⁻¹]` for some `D`. -/
lemma exists_pow_mul_isIntegral {t f : F}
    (hf : IsIntegral (Algebra.adjoin C {t}) f) :
    ∃ D : ℕ, IsIntegral (Algebra.adjoin C {t⁻¹}) (t⁻¹ ^ D * f) := by
  refine ⟨poleNorm C f, isIntegral_of_forall_mem fun P hP ↦ ?_⟩
  by_cases ht : t ∈ P.V
  · exact mul_mem (pow_mem hP _) (mem_V_of_isIntegral P ht hf)
  · rw [← P.valuation_le_one_iff, map_mul, map_pow, map_inv₀, P.valuation_eq_exp_poleOrder ht]
    have h1 := P.one_le_poleOrder ht
    have h2 := (P.valuation_le_exp_poleOrder f).trans
      (exp_le_exp.2 (by exact_mod_cast poleOrder_le_poleNorm P f :
        (P.poleOrder f : ℤ) ≤ poleNorm C f))
    calc (exp (P.poleOrder t : ℤ))⁻¹ ^ poleNorm C f * P.valuation f ≤
        (exp (P.poleOrder t : ℤ))⁻¹ ^ poleNorm C f * exp (poleNorm C f : ℤ) := by gcongr
      _ ≤ 1 := by
        rw [← exp_neg, ← exp_nsmul, ← exp_add, ← exp_zero, exp_le_exp, smul_neg, nsmul_eq_mul]
        have : (1 : ℤ) ≤ P.poleOrder t := by exact_mod_cast h1
        nlinarith [Int.natCast_nonneg (poleNorm C f)]

end Places

end GaussFibre

end SemistableReduction
