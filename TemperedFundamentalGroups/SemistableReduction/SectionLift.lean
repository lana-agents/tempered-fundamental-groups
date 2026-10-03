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

omit [IsUltrametricDist C] in
/-- `R(y)/Q(y)` is regular at `P` if `y` is and the roots of `Q` lie outside `|α| ≤ ‖ȳ‖`. -/
lemma div_mem_V (P : CurvePlace C F) {y : F} (hy : y ∈ P.V) (hyr : ‖P.res y‖ ≤ 1) {Q : C[X]}
    (hQ : Q ≠ 0) (hroots : ∀ α ∈ Q.roots, 1 < ‖α‖) (R : C[X]) : aeval y R / aeval y Q ∈ P.V := by
  have hev : Q.eval (P.res y) ≠ 0 := fun h ↦
    (not_lt.2 hyr) (hroots _ ((mem_roots hQ).2 h))
  rw [← P.valuation_le_one_iff, map_div₀, valuation_aeval_eq_one P hy hev, div_one,
    P.valuation_le_one_iff]
  exact aeval_mem_V P hy R

omit [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField C F] in
/-- `r(x)/Q(x) = r̃(x⁻¹)/Q̃(x⁻¹)` with the reflections at `deg Q`. -/
lemma aeval_div_eq_reflect {x : F} (hx : x ≠ 0) {r Q : C[X]}
    (hr : r.natDegree < Q.natDegree ∨ r = 0) :
    aeval x r / aeval x Q =
      aeval x⁻¹ (reflect Q.natDegree r) / aeval x⁻¹ (reflect Q.natDegree Q) := by
  letI : Invertible x := invertibleOfNonzero hx
  have hr' : r.natDegree ≤ Q.natDegree := by
    rcases hr with h | h
    · exact h.le
    · simp [h]
  have h1 := eval₂_reflect_mul_pow (algebraMap C F) x Q.natDegree r hr'
  have h2 := eval₂_reflect_mul_pow (algebraMap C F) x Q.natDegree Q le_rfl
  rw [invOf_eq_inv] at h1 h2
  rw [aeval_def, aeval_def, aeval_def, aeval_def, ← h1, ← h2,
    mul_div_mul_right _ _ (pow_ne_zero _ hx)]

end Places

section Lift

variable [IsAlgClosed C] [CharZero C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] [Fintype (Ext C F)]

attribute [local instance] isCurveFunctionField_F

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F]
  [Fintype (Ext C F)] in
lemma xF_ne_zero : xF C F ≠ 0 := fun h ↦
  transcendental_xF (C := C) (F := F) (h ▸ isAlgebraic_zero)

omit [CharZero C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
lemma pow_mem_intRing_x (k : ℕ) : xF C F ^ k ∈ intRing C F (xF C F) :=
  pow_mem (show xF C F ∈ intRing C F (xF C F) from ⟨isIntegral_algebraMap (x := (⟨_, Algebra.self_mem_adjoin_singleton C (xF C F)⟩ :
    Algebra.adjoin C {xF C F})), gnorm_le_iff.2 fun w ↦ (valuation_xF w).le⟩) k

omit [CharZero C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
lemma pow_mem_intRing_x_inv (k : ℕ) : (xF C F)⁻¹ ^ k ∈ intRing C F (xF C F)⁻¹ :=
  pow_mem (show (xF C F)⁻¹ ∈ intRing C F (xF C F)⁻¹ from ⟨isIntegral_algebraMap (x := (⟨_, Algebra.self_mem_adjoin_singleton C (xF C F)⁻¹⟩ :
    Algebra.adjoin C {(xF C F)⁻¹})), gnorm_le_iff.2 fun w ↦ (valuation_xF_inv w).le⟩) k

omit [CharZero C] in
/-- Elements of the chart ring at `∞` times a power of `x` lie in the chart ring at `0`. -/
lemma exists_pow_mul_mem_intRing_x {f : F} (hf : f ∈ intRing C F (xF C F)⁻¹) :
    ∃ D : ℕ, xF C F ^ D * f ∈ intRing C F (xF C F) := by
  obtain ⟨D, hD⟩ := exists_pow_mul_isIntegral (C := C) hf.1
  rw [inv_inv] at hD
  refine ⟨D, hD, (gnorm_mul_le _ _).trans (mul_le_one' ?_ hf.2)⟩
  exact gnorm_le_iff.2 fun w ↦ by rw [map_pow, valuation_xF, one_pow]

omit [CharZero C] in
/-- Elements of the chart ring at `0` times a power of `x⁻¹` lie in the chart ring at `∞`. -/
lemma exists_pow_mul_mem_intRing_x_inv {f : F} (hf : f ∈ intRing C F (xF C F)) :
    ∃ D : ℕ, (xF C F)⁻¹ ^ D * f ∈ intRing C F (xF C F)⁻¹ := by
  obtain ⟨D, hD⟩ := exists_pow_mul_isIntegral (C := C) hf.1
  refine ⟨D, hD, (gnorm_mul_le _ _).trans (mul_le_one' ?_ hf.2)⟩
  exact gnorm_le_iff.2 fun w ↦ by rw [map_pow, valuation_xF_inv, one_pow]

/-- **Lifting sections of the special fibre** (S7⁺.5, integral Serre vanishing): for `m ≫ 0`,
if `a` lies in the chart ring at `0`, `b` in the chart ring at `∞` and `ā = x̄ᵐ b̄` on every
residue curve, then some `f ∈ L(m (x)_∞)` of norm `≤ 1` has `f̄ = ā`. -/
theorem exists_lift {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι (RatFunc C) F}
    (hb : Orth C b) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ a ∈ intRing C F (xF C F),
      ∀ b' ∈ intRing C F (xF C F)⁻¹,
        (∀ w : Ext C F, red C a w = red C (xF C F) w ^ m * red C b' w) →
        ∃ f ∈ rrSpace (m • poleDivisor C (xF C F)), gnorm C f ≤ 1 ∧
          ∀ w : Ext C F, red C f w = red C a w := by
  classical
  set x := xF C F
  set ι' : C[X] →+* RatFunc C := algebraMap C[X] (RatFunc C)
  have hx0 : x ≠ 0 := xF_ne_zero
  have hcX : IsCoord F (RatFunc.X : RatFunc C) := isCoord_X
  have hcXi : IsCoord F (RatFunc.X : RatFunc C)⁻¹ := isCoord_X_inv
  have hXi : algebraMap (RatFunc C) F (RatFunc.X)⁻¹ = x⁻¹ := algebraMap_X_inv
  -- polynomials in `x` and `x⁻¹`
  have hevX (P : C[X]) : algebraMap (RatFunc C) F (ι' P) = aeval x P := by
    rw [← aeval_X_ratFunc, ← aeval_coord]
  have hevXi (P : C[X]) :
      algebraMap (RatFunc C) F (aeval (RatFunc.X : RatFunc C)⁻¹ P) = aeval x⁻¹ P := by
    rw [← aeval_coord, hXi]
  -- the chart bases
  obtain ⟨n, s, hs, hsi, hspan⟩ := exists_chartBasis hcX b hb
  obtain ⟨n', t, ht, hti, htspan⟩ := exists_chartBasis hcXi b hb
  have hti' (l : Fin n') : t l ∈ intRing C F x⁻¹ := hXi ▸ hti l
  -- `x^K tₗ` in the chart ring at `0`
  choose D hD using fun l ↦ exists_pow_mul_mem_intRing_x (hti' l)
  set K := Finset.univ.sup D
  have hK (l : Fin n') : x ^ K * t l ∈ intRing C F x := by
    have : x ^ K * t l = x ^ (K - D l) * (x ^ D l * t l) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := D) (Finset.mem_univ l))]
    rw [this]
    exact mul_mem (pow_mem_intRing_x _) (hD l)
  choose ρ hρ0 hρ π hπ using fun l ↦ exists_disc_coords hcX hs hsi hspan (hK l)
  -- `x^{-K'} sⱼ` in the chart ring at `∞`
  choose D' hD' using fun j ↦ exists_pow_mul_mem_intRing_x_inv (hsi j)
  set K' := Finset.univ.sup D'
  have hK' (j : Fin n) : x⁻¹ ^ K' * s j ∈ intRing C F x⁻¹ := by
    have : x⁻¹ ^ K' * s j = x⁻¹ ^ (K' - D' j) * (x⁻¹ ^ D' j * s j) := by
      rw [← mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := D') (Finset.mem_univ j))]
    rw [this]
    exact mul_mem (pow_mem_intRing_x_inv _) (hD' j)
  refine ⟨K', fun m hm a ha b' hb' hred ↦ ?_⟩
  -- coordinates of `a` and `b'`
  obtain ⟨qa, hqa0, hqa, pa, hpa⟩ := exists_disc_coords hcX hs hsi hspan ha
  obtain ⟨qb, hqb0, hqb, pb, hpb⟩ := exists_disc_coords hcXi ht hti htspan (hXi ▸ hb')
  rw [hXi] at hpb
  have hqa' : aeval x qa ≠ 0 := aeval_coord_ne_zero hcX hqa0
  have hqb' : aeval x⁻¹ qb ≠ 0 := hXi ▸ aeval_coord_ne_zero hcXi hqb0
  have hρ' (l : Fin n') : aeval x (ρ l) ≠ 0 := aeval_coord_ne_zero hcX (hρ0 l)
  -- the coordinates
  set ca : Fin n → RatFunc C := fun j ↦ ι' (pa j) * (ι' qa)⁻¹
  set cb : Fin n' → RatFunc C := fun l ↦
    aeval (RatFunc.X : RatFunc C)⁻¹ (pb l) * (aeval (RatFunc.X : RatFunc C)⁻¹ qb)⁻¹
  set θ : Fin n' → Fin n → RatFunc C := fun l j ↦
    (RatFunc.X : RatFunc C)⁻¹ ^ K * (ι' (π l j) * (ι' (ρ l))⁻¹)
  set χ : Fin n → RatFunc C := fun j ↦ ca j - RatFunc.X ^ m * ∑ l, cb l * θ l j
  have hXF : algebraMap (RatFunc C) F RatFunc.X = x := rfl
  have ha' : a = ∑ j, ca j • s j := by
    have : a = (aeval x qa)⁻¹ * (aeval x qa * a) := by
      rw [← mul_assoc, inv_mul_cancel₀ hqa', one_mul]
    rw [this, hpa, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [ca, Algebra.smul_def, map_mul, map_inv₀, hevX]
    ring
  have hb'' : b' = ∑ l, cb l • t l := by
    have : b' = (aeval x⁻¹ qb)⁻¹ * (aeval x⁻¹ qb * b') := by
      rw [← mul_assoc, inv_mul_cancel₀ hqb', one_mul]
    rw [this, hpb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [cb, Algebra.smul_def, map_mul, map_inv₀, hevXi]
    ring
  have htl (l : Fin n') : t l = ∑ j, θ l j • s j := by
    have : t l = x⁻¹ ^ K * (aeval x (ρ l))⁻¹ * (aeval x (ρ l) * (x ^ K * t l)) := by
      calc t l = (x⁻¹ * x) ^ K * ((aeval x (ρ l))⁻¹ * aeval x (ρ l)) * t l := by
            rw [inv_mul_cancel₀ hx0, one_pow, inv_mul_cancel₀ (hρ' l), one_mul, one_mul]
        _ = _ := by ring
    rw [this, hπ l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [θ, Algebra.smul_def, map_mul, map_inv₀, map_pow, hevX, hXF]
    ring
  have hd : a - x ^ m * b' = ∑ j, χ j • s j := by
    have hxm : x ^ m * b' = ∑ j, (RatFunc.X ^ m * ∑ l, cb l * θ l j) • s j := by
      rw [hb'']
      simp_rw [htl, Finset.smul_sum, smul_smul, Finset.mul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Algebra.smul_def, map_mul, map_pow, hXF]
      ring
    rw [hxm, ha', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← sub_smul]
  -- the coordinates are regular on the unit circle
  have hχ (j : Fin n) : χ j ∈ circRing C := by
    refine sub_mem (mul_mem (algebraMap_mem_circRing _) (inv_mem_circRing_out hqa0 hqa))
      (mul_mem (pow_mem X_mem_circRing _) (sum_mem fun l _ ↦ mul_mem ?_ ?_))
    · exact mul_mem (aeval_mem_circRing X_inv_mem_circRing _)
        (inv_aeval_X_inv_mem_circRing hqb0 hqb)
    · exact mul_mem (pow_mem X_inv_mem_circRing _) (mul_mem (algebraMap_mem_circRing _)
        (inv_mem_circRing_out (hρ0 l) (hρ l)))
  -- `‖a - xᵐ b'‖ < 1`
  have hb'w (w : Ext C F) : w.1 b' ≤ 1 := (le_gnorm w b').trans hb'.2
  have haw (w : Ext C F) : w.1 a ≤ 1 := (le_gnorm w a).trans ha.2
  have hxmw (w : Ext C F) : w.1 (x ^ m * b') ≤ 1 := by
    rw [map_mul, map_pow, valuation_xF, one_pow, one_mul]; exact hb'w w
  have hdn : gnorm C (a - x ^ m * b') < 1 := (gnorm_lt_iff one_pos).2 fun w ↦ by
    have hle : w.1 (a - x ^ m * b') ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le (haw w) (hxmw w))
    refine (red_eq_zero_iff hle).1 ?_
    rw [red_sub (haw w) (hxmw w), red_mul (by rw [map_pow, valuation_xF, one_pow]) (hb'w w),
      red_pow (valuation_xF w).le, hred w, sub_self]
  have hχn (j : Fin n) : gauss1 C (χ j) < 1 := by
    refine lt_of_le_of_lt ?_ hdn
    rw [hd, hs]
    exact Finset.le_sup (f := fun j ↦ gauss1 C (χ j)) (Finset.mem_univ j)
  -- split the coordinates
  have hsplit (j : Fin n) : ∃ Qo Qi Pp r : C[X], Qo ≠ 0 ∧ Qi ≠ 0 ∧
      (∀ α ∈ Qo.roots, 1 < ‖α‖) ∧ (∀ α ∈ Qi.roots, ‖α‖ < 1) ∧
      (r.natDegree < Qi.natDegree ∨ r = 0) ∧ χ j = ι' Pp / ι' Qo + ι' r / ι' Qi ∧
      gauss1 C (ι' Pp / ι' Qo) ≤ gauss1 C (χ j) ∧ gauss1 C (ι' r / ι' Qi) ≤ gauss1 C (χ j) := by
    obtain ⟨P, Qo, Qi, hQo, hQi, ho, hi, hP⟩ := hχ j
    obtain ⟨Pp, r, hr, heq, h1, h2⟩ := exists_laurent_split P hQo hQi ho hi
    exact ⟨Qo, Qi, Pp, r, hQo, hQi, ho, hi, hr, hP.trans heq, hP ▸ h1, hP ▸ h2⟩
  choose Qo Qi Pp r hQo hQi ho hi hr hχeq hn1 hn2 using hsplit
  set φp : Fin n → RatFunc C := fun j ↦ ι' (Pp j) / ι' (Qo j)
  set φm : Fin n → RatFunc C := fun j ↦ ι' (r j) / ι' (Qi j)
  set f := a - ∑ j, φp j • s j
  have hpn : gnorm C (∑ j, φp j • s j) < 1 := by
    rw [hs]
    exact (Finset.sup_lt_iff one_pos).2 fun j _ ↦ (hn1 j).trans_lt (hχn j)
  have hf2 : f = x ^ m * b' + ∑ j, φm j • s j := by
    have : a - x ^ m * b' = ∑ j, φp j • s j + ∑ j, φm j • s j := by
      rw [hd, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← add_smul, hχeq j]
    simp only [f]
    linear_combination this
  refine ⟨f, ?_, (gnorm_sub_le _ _).trans (max_le ha.2 hpn.le), fun w ↦ ?_⟩
  swap
  · have hpw : w.1 (∑ j, φp j • s j) < 1 := (le_gnorm w _).trans_lt hpn
    rw [red_sub (haw w) hpw.le, (red_eq_zero_iff hpw.le).2 hpw, sub_zero]
  -- poles
  rw [mem_rrSpace]
  intro P
  rw [Finsupp.smul_apply, poleDivisor_apply, nsmul_eq_mul]
  by_cases hA : x ∈ P.V ∧ ‖P.res x‖ ≤ 1
  · have hfP : f ∈ P.V := by
      refine sub_mem (mem_V_of_isIntegral P hA.1 ha.1) (sum_mem fun j _ ↦ ?_)
      rw [Algebra.smul_def]
      refine mul_mem ?_ (mem_V_of_isIntegral P hA.1 (hsi j).1)
      simp only [φp, map_div₀, hevX]
      exact div_mem_V P hA.1 hA.2 (hQo j) (ho j) (Pp j)
    refine (P.valuation_le_one_iff.2 hfP).trans ?_
    rw [← exp_zero, exp_le_exp]
    positivity
  have hy : x⁻¹ ∈ P.V ∧ ‖P.res x⁻¹‖ ≤ 1 := by
    by_cases hxV : x ∈ P.V
    · have hr : 1 < ‖P.res x‖ := by
        push Not at hA
        exact hA hxV
      have h0 : P.res x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hr
        exact absurd hr (by norm_num)
      obtain ⟨h1, h2⟩ := res_inv P hxV h0
      refine ⟨h1, ?_⟩
      rw [h2, norm_inv]
      exact inv_le_one_of_one_le₀ hr.le
    · have h1 : x⁻¹ ∈ P.V := (P.V.mem_or_inv_mem x).resolve_left hxV
      have h2 : P.res x⁻¹ = 0 := P.res_eq_of_valuation_sub_lt_one (by
        rw [map_zero, sub_zero, map_inv₀, P.valuation_eq_exp_poleOrder hxV, ← exp_neg,
          ← exp_zero, exp_lt_exp]
        have := P.one_le_poleOrder hxV
        omega)
      exact ⟨h1, by rw [h2, norm_zero]; exact zero_le_one⟩
  have hgP : x⁻¹ ^ m * f ∈ P.V := by
    rw [hf2, mul_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hx0, one_pow, one_mul,
      Finset.mul_sum]
    refine add_mem (mem_V_of_isIntegral P hy.1 hb'.1) (sum_mem fun j _ ↦ ?_)
    have hm' : m = (m - K') + K' := (Nat.sub_add_cancel hm).symm
    have : x⁻¹ ^ m * (φm j • s j) =
        x⁻¹ ^ (m - K') * algebraMap (RatFunc C) F (φm j) * (x⁻¹ ^ K' * s j) := by
      conv_lhs => rw [hm']
      rw [Algebra.smul_def, pow_add]
      ring
    rw [this]
    refine mul_mem (mul_mem (pow_mem hy.1 _) ?_) (mem_V_of_isIntegral P hy.1 (hK' j).1)
    simp only [φm, map_div₀, hevX]
    rw [aeval_div_eq_reflect hx0 (hr j)]
    exact div_mem_V P hy.1 hy.2 (by simpa [reflect_eq_zero_iff] using hQi j)
      (roots_reflect_gt (hQi j) (hi j)) _
  have hfeq : f = x ^ m * (x⁻¹ ^ m * f) := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0, one_pow, one_mul]
  rw [hfeq, map_mul, map_pow]
  calc P.valuation x ^ m * P.valuation (x⁻¹ ^ m * f) ≤ P.valuation x ^ m * 1 := by
        gcongr
        exact P.valuation_le_one_iff.2 hgP
    _ ≤ exp (P.poleOrder x : ℤ) ^ m := by
        rw [mul_one]
        gcongr
        exact P.valuation_le_exp_poleOrder x
    _ = exp ((m : ℤ) * P.poleOrder x) := by rw [← exp_nsmul, nsmul_eq_mul]

end Lift

end GaussFibre

end SemistableReduction
