/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourValued
import TemperedFundamentalGroups.SemistableReduction.TypeFourAssembly

/-!
# Choosing a good topological generator

Blueprint §9.12, leaf T4, part (G). Let `ξ'` be a valuation of `F` (finite over `C(x)`) over a
type-4 point and `s ∈ F` with `C(s)` dense in `(F, ξ')` (`CoordDense`). We replace `s` by a
generator `s'` which is moreover **integral over `C[x]`**, with **`x` integral over `C[s']`**.

* `NearRel`, `near_aeval`, `near_div`: if `|δ| ≤ q |s - α|` for every root `α` of `P`, then
  `P(s + δ) = P(s) (1 + w)` with `|w| ≤ q` (factor `P` over the algebraically closed `C`);
* **`coordDense_of_near`** (density is open): if `|s - b| ≥ r` for all `b ∈ C` and
  `|s' - s| ≤ q r`, `q < 1`, then `C(s')` is dense too: the map `R(s) ↦ R(s')` moves elements by a
  factor `≤ q`, and an iteration converges;
* `exists_const_near` (the case `inf_b |s - b| = 0`): then `C` itself is dense;
* `exists_integral_near` (integral elements are dense): `y = a / d(x)` with `a` integral and
  `d(x) = γ (1 - u)`, `|u| < 1` (`IsTypeFour.nearConst`), and `1 / (1 - u) ≈ Σ uⁱ`;
* `isIntegral_add_pow` (degree trick): for `s₁` integral over `C[x]` and `M` larger than the
  degrees of the coefficients of an integral equation, `x` is integral over `C[s₁ + λ x^M]`;
* **`exists_good_coord`**.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open Splitting GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section Near

variable {F : Type*} [Field F] [Algebra C F] (ξ' : Valuation F ℝ≥0)

/-- `z' = z (1 + w)` with `|w| ≤ q`. -/
def NearRel (q : ℝ≥0) (z z' : F) : Prop := ∃ w : F, z' = z * (1 + w) ∧ ξ' w ≤ q

variable {ξ'}

omit [Algebra C F] in
lemma NearRel.refl (q : ℝ≥0) (z : F) : NearRel ξ' q z z := ⟨0, by ring, by simp⟩

omit [Algebra C F] in
lemma NearRel.mul {q : ℝ≥0} (hq : q ≤ 1) {z₁ z₁' z₂ z₂' : F} (h₁ : NearRel ξ' q z₁ z₁')
    (h₂ : NearRel ξ' q z₂ z₂') : NearRel ξ' q (z₁ * z₂) (z₁' * z₂') := by
  obtain ⟨w₁, rfl, hw₁⟩ := h₁
  obtain ⟨w₂, rfl, hw₂⟩ := h₂
  refine ⟨w₁ + w₂ + w₁ * w₂, by ring, ?_⟩
  refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
    (max_le hw₁ hw₂)) ?_)
  rw [map_mul]
  exact (mul_le_mul' hw₁ hw₂).trans (mul_le_of_le_one_left' hq)

omit [Algebra C F] in
lemma NearRel.val_eq {q : ℝ≥0} (hq : q < 1) {z z' : F} (h : NearRel ξ' q z z') :
    ξ' z' = ξ' z := by
  obtain ⟨w, rfl, hw⟩ := h
  rw [map_mul, add_comm, Valuation.map_add_eq_of_lt_right _ (by rw [map_one]; exact hw.trans_lt hq),
    map_one, mul_one]

omit [IsUltrametricDist C] in
lemma near_aeval {q : ℝ≥0} (hq : q ≤ 1) (s δ : F) (P : C[X])
    (hP : ∀ α ∈ P.roots, ξ' δ ≤ q * ξ' (s - algebraMap C F α)) :
    NearRel ξ' q (aeval s P) (aeval (s + δ) P) := by
  classical
  by_cases hδ : δ = 0
  · rw [hδ, add_zero]; exact NearRel.refl q _
  have key : ∀ m : Multiset C, (∀ α ∈ m, ξ' δ ≤ q * ξ' (s - algebraMap C F α)) →
      NearRel ξ' q (aeval s (m.map fun a ↦ X - Polynomial.C a).prod)
        (aeval (s + δ) (m.map fun a ↦ X - Polynomial.C a).prod) := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
      intro _
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one]
      exact NearRel.refl q 1
    | cons α m ih =>
      intro hm
      simp only [Multiset.mem_cons, forall_eq_or_imp] at hm
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
      refine NearRel.mul hq ?_ (ih hm.2)
      simp only [map_sub, aeval_X, aeval_C]
      have hsα : s - algebraMap C F α ≠ 0 := by
        intro h0
        have := hm.1
        rw [h0, map_zero, mul_zero, le_zero_iff, Valuation.zero_iff] at this
        exact hδ this
      refine ⟨δ / (s - algebraMap C F α), by field_simp; ring, ?_⟩
      rw [map_div₀, div_le_iff₀ ((Valuation.pos_iff _).2 hsα)]
      exact hm.1
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := P)),
    map_mul, map_mul]
  exact NearRel.mul hq (by rw [aeval_C, aeval_C]; exact NearRel.refl q _) (key _ hP)

omit [IsUltrametricDist C] in
/-- `P / Q` moves by a factor `≤ q` under `s ↦ s + δ`. -/
lemma near_div {q : ℝ≥0} (hq : q < 1) (s δ : F) {P Q : C[X]}
    (hP : ∀ α ∈ P.roots, ξ' δ ≤ q * ξ' (s - algebraMap C F α))
    (hQ : ∀ α ∈ Q.roots, ξ' δ ≤ q * ξ' (s - algebraMap C F α)) (hQ0 : aeval s Q ≠ 0) :
    aeval (s + δ) Q ≠ 0 ∧
      ξ' (aeval (s + δ) P / aeval (s + δ) Q - aeval s P / aeval s Q) ≤
        q * ξ' (aeval s P / aeval s Q) := by
  obtain ⟨w₁, h₁, hw₁⟩ := near_aeval hq.le s δ P hP
  obtain ⟨w₂, h₂, hw₂⟩ := near_aeval hq.le s δ Q hQ
  have h1w : ξ' (1 + w₂) = 1 := by
    rw [add_comm, Valuation.map_add_eq_of_lt_right _ (by rw [map_one]; exact hw₂.trans_lt hq),
      map_one]
  have h1w0 : (1 + w₂) ≠ 0 := fun h ↦ by rw [h, map_zero] at h1w; exact zero_ne_one h1w
  refine ⟨by rw [h₂]; exact mul_ne_zero hQ0 h1w0, ?_⟩
  rw [h₁, h₂, show aeval s P * (1 + w₁) / (aeval s Q * (1 + w₂)) - aeval s P / aeval s Q =
      aeval s P / aeval s Q * ((w₁ - w₂) / (1 + w₂)) by field_simp; ring,
    map_mul, mul_comm q]
  refine mul_le_mul' le_rfl ?_
  rw [map_div₀, h1w, div_one]
  exact (Valuation.map_sub _ _ _).trans (max_le hw₁ hw₂)

end Near

/-! ### Rational functions of a generator -/

section Rat

omit [IsUltrametricDist C] [IsAlgClosed C]

variable {F : Type*} [Field F] [Algebra C F]

/-- `z` is a rational function of `s` with coefficients in `C`. -/
def IsRatOf (s z : F) : Prop := ∃ P Q : C[X], aeval s Q ≠ 0 ∧ z = aeval s P / aeval s Q

lemma isRatOf_zero (s : F) : IsRatOf (C := C) s 0 := ⟨0, 1, by simp, by simp⟩

lemma IsRatOf.add {s z z' : F} (h : IsRatOf (C := C) s z) (h' : IsRatOf (C := C) s z') :
    IsRatOf (C := C) s (z + z') := by
  obtain ⟨P, Q, hQ, rfl⟩ := h
  obtain ⟨P', Q', hQ', rfl⟩ := h'
  refine ⟨P * Q' + P' * Q, Q * Q', by rw [map_mul]; exact mul_ne_zero hQ hQ', ?_⟩
  rw [map_add, map_mul, map_mul, map_mul]
  field_simp

lemma coordDense_iff (ξ' : Valuation F ℝ≥0) (s : F) :
    CoordDense C ξ' s ↔ ∀ y : F, ∀ ε : ℝ≥0, 0 < ε → ∃ z, IsRatOf (C := C) s z ∧ ξ' (y - z) < ε := by
  constructor
  · intro h y ε hε
    obtain ⟨P, Q, hQ, h⟩ := h y ε hε
    exact ⟨_, ⟨P, Q, hQ, rfl⟩, h⟩
  · intro h y ε hε
    obtain ⟨z, ⟨P, Q, hQ, rfl⟩, h⟩ := h y ε hε
    exact ⟨P, Q, hQ, h⟩

end Rat

/-! ### Density is open -/

section Open

variable {F : Type*} [Field F] [Algebra C F] {ξ' : Valuation F ℝ≥0}

omit [IsUltrametricDist C] in
/-- **Density is open.** If `|s - b| ≥ r` for all `b ∈ C`, `C(s)` is dense and `|s' - s| ≤ q r`
with `q < 1`, then `C(s')` is dense. -/
theorem coordDense_of_near {s s' : F} (hs : CoordDense C ξ' s) {r q : ℝ≥0} (hq0 : 0 < q)
    (hq : q < 1) (hr : ∀ b : C, r ≤ ξ' (s - algebraMap C F b)) (hss : ξ' (s' - s) ≤ q * r) :
    CoordDense C ξ' s' := by
  have hroot : ∀ (P : C[X]), ∀ α ∈ P.roots, ξ' (s' - s) ≤ q * ξ' (s - algebraMap C F α) :=
    fun P α _ ↦ hss.trans (mul_le_mul' le_rfl (hr α))
  have hs' : s' = s + (s' - s) := by ring
  -- one step of the iteration
  have hstep : ∀ y : F, ∃ z, IsRatOf (C := C) s' z ∧ ξ' (y - z) ≤ q * ξ' y := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, isRatOf_zero s', by simp [hy]⟩
    have hε : 0 < q * ξ' y := mul_pos hq0 ((Valuation.pos_iff _).2 hy)
    obtain ⟨P, Q, hQ, hPQ⟩ := hs y _ hε
    obtain ⟨hQ', hmove⟩ := near_div hq s (s' - s) (hroot P) (hroot Q) hQ
    rw [← hs'] at hQ' hmove
    refine ⟨aeval s' P / aeval s' Q, ⟨P, Q, hQ', rfl⟩, ?_⟩
    have hR : ξ' (aeval s P / aeval s Q) ≤ ξ' y := by
      rw [show aeval s P / aeval s Q = y - (y - aeval s P / aeval s Q) by ring]
      refine (Valuation.map_sub _ _ _).trans (max_le le_rfl ?_)
      exact hPQ.le.trans (mul_le_of_le_one_left' hq.le)
    rw [show y - aeval s' P / aeval s' Q = (y - aeval s P / aeval s Q) -
      (aeval s' P / aeval s' Q - aeval s P / aeval s Q) by ring]
    exact (Valuation.map_sub _ _ _).trans (max_le hPQ.le (hmove.trans (mul_le_mul' le_rfl hR)))
  -- iterate
  have hiter : ∀ k : ℕ, ∀ y : F, ∃ z, IsRatOf (C := C) s' z ∧ ξ' (y - z) ≤ q ^ k * ξ' y := by
    intro k
    induction k with
    | zero => exact fun y ↦ ⟨0, isRatOf_zero s', by simp⟩
    | succ k ih =>
      intro y
      obtain ⟨z₁, hz₁, h₁⟩ := hstep y
      obtain ⟨z₂, hz₂, h₂⟩ := ih (y - z₁)
      refine ⟨z₁ + z₂, hz₁.add hz₂, ?_⟩
      rw [show y - (z₁ + z₂) = y - z₁ - z₂ by ring]
      refine h₂.trans ?_
      rw [pow_succ, mul_assoc]
      exact mul_le_mul' le_rfl h₁
  refine (coordDense_iff ξ' s').2 fun y ε hε ↦ ?_
  by_cases hy : ξ' y = 0
  · exact ⟨0, isRatOf_zero s', by rwa [sub_zero, hy]⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε ((zero_le).lt_of_ne (Ne.symm hy))) hq
  obtain ⟨z, hz, h⟩ := hiter k y
  refine ⟨z, hz, h.trans_lt ?_⟩
  rwa [lt_div_iff₀ ((zero_le).lt_of_ne (Ne.symm hy))] at hk

omit [IsUltrametricDist C] in
/-- **If `s` comes arbitrarily close to constants, `C` is dense.** -/
theorem exists_const_near {s : F} (hs : CoordDense C ξ' s)
    (h0 : ∀ ε : ℝ≥0, 0 < ε → ∃ b : C, ξ' (s - algebraMap C F b) < ε) (y : F) {ε : ℝ≥0}
    (hε : 0 < ε) : ∃ c : C, ξ' (y - algebraMap C F c) < ε := by
  classical
  obtain ⟨P, Q, hQ, hPQ⟩ := hs y ε hε
  have haeval : ∀ (b : C) (R : C[X]), aeval (algebraMap C F b) R = algebraMap C F (R.eval b) :=
    fun b R ↦ by rw [aeval_algebraMap_apply, aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self,
      map_id]
  by_cases hsC : ∃ α : C, s = algebraMap C F α
  · obtain ⟨α, rfl⟩ := hsC
    refine ⟨P.eval α / Q.eval α, ?_⟩
    rwa [map_div₀, ← haeval, ← haeval]
  push Not at hsC
  have hpos : ∀ α : C, 0 < ξ' (s - algebraMap C F α) := fun α ↦
    (Valuation.pos_iff _).2 (sub_ne_zero.2 (hsC α))
  -- a lower bound for the distances from `s` to the roots
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ≥0, 0 < m ∧ ∀ α ∈ P.roots.toFinset ∪ Q.roots.toFinset,
      m ≤ ξ' (s - algebraMap C F α) := by
    rcases (P.roots.toFinset ∪ Q.roots.toFinset).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨_, (Finset.lt_inf'_iff h).2 fun α _ ↦ hpos α, fun α hα ↦ Finset.inf'_le _ hα⟩
  set R := aeval s P / aeval s Q
  set M := max (ξ' y) ε
  have hM : 0 < M := lt_max_of_lt_right hε
  set q := ε / (2 * M)
  have hq0 : 0 < q := div_pos hε (mul_pos two_pos hM)
  have hqM : q * M < ε := by
    rw [div_mul_eq_mul_div, mul_comm 2 M, ← div_div, mul_div_assoc, div_self hM.ne', mul_one]
    exact NNReal.half_lt_self hε.ne'
  have hq1 : q < 1 := by
    rw [div_lt_one (mul_pos two_pos hM)]
    calc ε ≤ M := le_max_right _ _
      _ < 2 * M := by rw [two_mul]; exact lt_add_of_pos_left _ hM
  obtain ⟨b, hb⟩ := h0 (q * m) (mul_pos hq0 hm0)
  have hroot : ∀ (T : C[X]), (T = P ∨ T = Q) → ∀ α ∈ T.roots,
      ξ' (algebraMap C F b - s) ≤ q * ξ' (s - algebraMap C F α) := by
    intro T hT α hα
    rw [← Valuation.map_neg, neg_sub]
    refine hb.le.trans (mul_le_mul' le_rfl (hm α ?_))
    rcases hT with rfl | rfl
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.2 hα)
    · exact Finset.mem_union_right _ (Multiset.mem_toFinset.2 hα)
  obtain ⟨-, hmove⟩ := near_div hq1 s (algebraMap C F b - s) (hroot P (Or.inl rfl))
    (hroot Q (Or.inr rfl)) hQ
  rw [add_sub_cancel, haeval, haeval, ← map_div₀] at hmove
  refine ⟨P.eval b / Q.eval b, ?_⟩
  have hR : ξ' R ≤ M := by
    rw [show R = y - (y - R) by ring]
    exact (Valuation.map_sub _ _ _).trans (max_le_max le_rfl hPQ.le)
  rw [show y - algebraMap C F (P.eval b / Q.eval b) =
    (y - R) - (algebraMap C F (P.eval b / Q.eval b) - R) by ring]
  exact (Valuation.map_sub _ _ _).trans_lt (max_lt hPQ
    (hmove.trans_lt ((mul_le_mul' le_rfl hR).trans_lt hqM)))

end Open

/-! ### Integral elements are dense; the degree trick -/

section Integral

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
lemma isIntegral_adjoin_of_mem {z : F} (hz : z ∈ Algebra.adjoin C {xF C F}) :
    IsIntegral (Algebra.adjoin C {xF C F}) z :=
  isIntegral_algebraMap (R := Algebra.adjoin C {xF C F}) (x := ⟨z, hz⟩)

/-- **Integral elements are dense** at a type-4 point. -/
theorem exists_integral_near {ξ' : Valuation F ℝ≥0}
    (hξ : IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) (y : F) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ y₁ : F, IsIntegral (Algebra.adjoin C {xF C F}) y₁ ∧ ξ' (y - y₁) < ε := by
  classical
  letI : Algebra C[X] F :=
    ((algebraMap (RatFunc C) F).comp (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := IsLocalization.isAlgebraic (RatFunc C) (nonZeroDivisors C[X])
  haveI := Algebra.IsAlgebraic.trans C[X] (RatFunc C) F
  obtain ⟨d, hd0, hdint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := C[X]) y).exists_integral_multiple
  have hpoly : ∀ P : C[X], algebraMap C[X] F P = aeval (xF C F) P := fun P ↦
    (GaussFibre.aeval_xF P).symm
  set a : F := d • y
  have ha : a = aeval (xF C F) d * y := by
    change d • y = _
    rw [Algebra.smul_def, hpoly]
  have haint : IsIntegral (Algebra.adjoin C {xF C F}) a :=
    IsIntegral.map_of_comp_eq (aeval (⟨xF C F, Algebra.self_mem_adjoin_singleton C _⟩ :
      Algebra.adjoin C {xF C F})).toRingHom (RingHom.id F)
      (by ext P <;> simp [hpoly]) hdint
  set φ : RatFunc C := algebraMap C[X] (RatFunc C) d
  have hφ0 : φ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hd0
  have hφF : algebraMap (RatFunc C) F φ = aeval (xF C F) d := (hpoly d).symm ▸ rfl
  obtain ⟨γ, hγ, hnear⟩ := hξ.nearConst hφ0
  have hcomap : ∀ ψ, ξ' (algebraMap (RatFunc C) F ψ) = ξ'.comap (algebraMap (RatFunc C) F) ψ :=
    fun ψ ↦ rfl
  have hC : ∀ c : C, ξ' (algebraMap C F c) = ‖c‖₊ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, hcomap, hξ.map_C,
      NormedField.valuation_apply]
  set u : F := 1 - algebraMap C F γ⁻¹ * aeval (xF C F) d
  have hu : ξ' u < 1 := by
    have : u = algebraMap C F γ⁻¹ * algebraMap (RatFunc C) F (algebraMap C (RatFunc C) γ - φ) := by
      rw [map_sub, ← IsScalarTower.algebraMap_apply, hφF, mul_sub, ← map_mul,
        inv_mul_cancel₀ hγ, map_one]
    rw [this, map_mul, hC, hcomap, ← Valuation.map_neg, neg_sub, nnnorm_inv,
      inv_mul_lt_iff₀ (nnnorm_pos.2 hγ), mul_one]
    exact hnear
  have hdu : aeval (xF C F) d = algebraMap C F γ * (1 - u) := by
    simp only [u, sub_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_mul]
  have hu1 : ξ' (1 - u) = 1 := by
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_neg, map_one]),
      map_one]
  have hu10 : (1 - u) ≠ 0 := fun h ↦ by rw [h, map_zero] at hu1; exact zero_ne_one hu1
  by_cases ha0 : a = 0
  · refine ⟨0, isIntegral_zero, ?_⟩
    have hy : y = 0 := by
      rw [ha, hdu] at ha0
      rcases mul_eq_zero.1 ha0 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h ((_root_.map_ne_zero _).2 hγ)
        · exact absurd h hu10
      · exact h
    rw [hy, sub_zero, map_zero]
    exact hε
  have hapos : 0 < ξ' a := (Valuation.pos_iff _).2 ha0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (mul_pos hε (nnnorm_pos.2 hγ)) hapos) hu
  refine ⟨a * algebraMap C F γ⁻¹ * ∑ i ∈ Finset.range N, u ^ i, ?_, ?_⟩
  · have huint : IsIntegral (Algebra.adjoin C {xF C F}) u := by
      refine isIntegral_adjoin_of_mem (Subalgebra.sub_mem _ (Subalgebra.one_mem _) ?_)
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Polynomial.aeval_mem_adjoin_singleton C _)
    refine (haint.mul (isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ _))).mul ?_
    exact IsIntegral.sum _ fun i _ ↦ huint.pow i
  · have hγF : algebraMap C F γ ≠ 0 := (_root_.map_ne_zero _).2 hγ
    have hy : y = a * algebraMap C F γ⁻¹ * (1 - u)⁻¹ := by
      rw [ha, hdu, map_inv₀]
      field_simp
    have hgeom := mul_neg_geom_sum u N
    have hsum : ∑ i ∈ Finset.range N, u ^ i = (1 - u ^ N) * (1 - u)⁻¹ := by
      rw [← hgeom]; field_simp
    rw [hy, ← mul_sub, hsum, show (1 - u)⁻¹ - (1 - u ^ N) * (1 - u)⁻¹ = u ^ N * (1 - u)⁻¹ by
      ring]
    simp only [map_mul, map_inv₀, map_pow, hu1, hC, inv_one, mul_one]
    rw [lt_div_iff₀ hapos] at hN
    calc ξ' a * ‖γ‖₊⁻¹ * ξ' u ^ N = ‖γ‖₊⁻¹ * (ξ' u ^ N * ξ' a) := by ring
      _ < ‖γ‖₊⁻¹ * (ε * ‖γ‖₊) := mul_lt_mul_of_pos_left hN (inv_pos.2 (nnnorm_pos.2 hγ))
      _ = ε := by rw [mul_comm ε, ← mul_assoc, inv_mul_cancel₀ (nnnorm_pos.2 hγ).ne', one_mul]

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
/-- **The degree trick.** If `s₁` is integral over `C[x]`, then for `M` large and every `l ≠ 0`,
`x` is integral over `C[s₁ + l x^M]`: substituting `s₁ = s₂ - l x^M` into an integral equation of
`s₁` gives a polynomial equation for `x` over `C[s₂]` with leading coefficient `(-l)^m`. -/
theorem isIntegral_add_pow {s₁ : F} (hs₁ : IsIntegral (Algebra.adjoin C {xF C F}) s₁) :
    ∃ M : ℕ, 0 < M ∧ ∀ l : C, l ≠ 0 →
      IsIntegral (Algebra.adjoin C {s₁ + algebraMap C F l * xF C F ^ M}) (xF C F) := by
  classical
  obtain ⟨f, hfm, hf⟩ := hs₁
  have hcoef : ∀ i, ∃ g : C[X], aeval (xF C F) g = (f.coeff i : F) := by
    intro i
    have : (f.coeff i : F) ∈ (aeval (R := C) (xF C F)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (f.coeff i).2
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩
  choose g hg using hcoef
  set m := f.natDegree
  set D := (Finset.range (m + 1)).sup fun i ↦ (g i).natDegree
  refine ⟨D + 1, Nat.succ_pos _, fun l hl ↦ ?_⟩
  set M := D + 1
  set s₂ := s₁ + algebraMap C F l * xF C F ^ M
  set sB : Algebra.adjoin C {s₂} := ⟨s₂, Algebra.self_mem_adjoin_singleton C _⟩
  set lB : Algebra.adjoin C {s₂} := algebraMap C (Algebra.adjoin C {s₂}) l
  have hlB : lB ≠ 0 := fun h ↦ hl ((algebraMap C F).injective (by
    rw [map_zero]; exact congrArg Subtype.val h))
  set T : (Algebra.adjoin C {s₂})[X] := Polynomial.C sB - Polynomial.C lB * X ^ M
  set H : (Algebra.adjoin C {s₂})[X] :=
    ∑ i ∈ Finset.range (m + 1), (g i).map (algebraMap C (Algebra.adjoin C {s₂})) * T ^ i
  -- `x` is a root of `H`
  have hT : aeval (xF C F) T = s₁ := by
    simp only [T, map_sub, map_mul, map_pow, aeval_C, aeval_X, sB, lB, s₂]
    change s₁ + algebraMap C F l * xF C F ^ M - algebraMap C F l * xF C F ^ M = s₁
    ring
  have hroot : aeval (xF C F) H = 0 := by
    simp only [H, map_sum, map_mul, map_pow, hT, Polynomial.aeval_map_algebraMap, hg]
    rw [← hf, eval₂_eq_sum_range]
    rfl
  -- the degree of `T`
  have hTdeg : T.natDegree = M := by
    rw [natDegree_sub_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow M lB hlB]
    rw [natDegree_C]; exact Nat.succ_pos _
  have hTlead : T.leadingCoeff = -lB := by
    rw [leadingCoeff_sub_of_degree_lt', leadingCoeff_C_mul_X_pow]
    refine degree_lt_degree ?_
    rw [natDegree_C, natDegree_C_mul_X_pow M lB hlB]; exact Nat.succ_pos _
  -- `m ≥ 1`
  have hm : 1 ≤ m := by
    by_contra h
    have h0 : f.natDegree = 0 := by omega
    rw [eq_one_of_monic_natDegree_zero hfm h0, eval₂_one] at hf
    exact one_ne_zero hf
  have hgm : g m = 1 := by
    have h1 : aeval (xF C F) (g m) = aeval (xF C F) (1 : C[X]) := by
      rw [hg, hfm.coeff_natDegree, map_one]; rfl
    exact (transcendental_iff_injective.1 (GaussFibre.transcendental_xF (C := C) (F := F))) h1
  -- the lower terms have smaller degree
  set S : (Algebra.adjoin C {s₂})[X] :=
    ∑ i ∈ Finset.range m, (g i).map (algebraMap C (Algebra.adjoin C {s₂})) * T ^ i
  have hHS : H = S + T ^ m := by
    simp only [H, S, Finset.sum_range_succ, hgm, Polynomial.map_one, one_mul]
  have hSdeg : S.natDegree < (T ^ m).natDegree := by
    rw [natDegree_pow, hTdeg]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := D + (m - 1) * M)
      fun i hi ↦ ?_) ?_
    · have hi' := Finset.mem_range.1 hi
      refine (natDegree_mul_le).trans (add_le_add ?_ ?_)
      · refine (natDegree_map_le).trans ?_
        exact Finset.le_sup (f := fun i ↦ (g i).natDegree) (Finset.mem_range.2 (by omega))
      · refine (natDegree_pow_le).trans ?_
        rw [hTdeg]
        exact Nat.mul_le_mul_right _ (by omega)
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hM : M = D + 1 := rfl
      rw [hk, Nat.add_sub_cancel, hM]
      nlinarith
  have hHlead : H.leadingCoeff = (-lB) ^ m := by
    rw [hHS, leadingCoeff_add_of_degree_lt (degree_lt_degree hSdeg), leadingCoeff_pow, hTlead]
  -- normalize
  have hu : IsUnit ((-lB) ^ m) := by
    have : (-lB) ^ m = algebraMap C (Algebra.adjoin C {s₂}) ((-l) ^ m) := by simp [lB]
    rw [this]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ (neg_ne_zero.2 hl))).map _
  refine ⟨Polynomial.C (↑hu.unit⁻¹ : Algebra.adjoin C {s₂}) * H, ?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, hHlead]
    exact hu.val_inv_mul
  · rw [← aeval_def, map_mul, hroot, mul_zero]

omit [IsUltrametricDist C] [FiniteDimensional (RatFunc C) F] [Algebra (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
/-- An element algebraic over the algebraically closed `C` is a constant. -/
lemma exists_eq_algebraMap_of_isAlgebraic {y : F} (hy : IsAlgebraic C y) :
    ∃ α : C, algebraMap C F α = y :=
  minpoly.mem_range_of_degree_eq_one C y
    (IsAlgClosed.degree_eq_one_of_irreducible C (minpoly.irreducible hy.isIntegral))

/-- **A good topological generator**: if `C(s)` is dense in `(F, ξ')`, there is `s'` with
`C(s')` dense, `s'` transcendental over `C`, integral over `C[x]`, and `x` integral over `C[s']`.
If `s` comes arbitrarily close to constants, `C` is dense and `s' = x`; otherwise `s'` is an
integral approximation of `s` (`exists_integral_near`) corrected by `l x^M` (degree trick), close
enough to `s` for density (`coordDense_of_near`). -/
theorem exists_good_coord {ξ' : Valuation F ℝ≥0}
    (hξ : IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) {s : F} (hs : CoordDense C ξ' s) :
    ∃ s' : F, CoordDense C ξ' s' ∧ Transcendental C s' ∧
      IsIntegral (Algebra.adjoin C {xF C F}) s' ∧
      IsIntegral (Algebra.adjoin C {s'}) (xF C F) := by
  have hC : ∀ c : C, ξ' (algebraMap C F c) = ‖c‖₊ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, ← Valuation.comap_apply, hξ.map_C,
      NormedField.valuation_apply]
  by_cases h0 : ∀ ε : ℝ≥0, 0 < ε → ∃ b : C, ξ' (s - algebraMap C F b) < ε
  · refine ⟨xF C F, fun y ε hε ↦ ?_, GaussFibre.transcendental_xF, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := exists_const_near hs h0 y hε
      exact ⟨Polynomial.C c, 1, by simp, by simpa using hc⟩
    · exact isIntegral_adjoin_of_mem (Algebra.self_mem_adjoin_singleton C _)
    · exact isIntegral_algebraMap
        (x := (⟨_, Algebra.self_mem_adjoin_singleton C (xF C F)⟩ : Algebra.adjoin C {xF C F}))
  push Not at h0
  obtain ⟨r, hr0, hr⟩ := h0
  set q : ℝ≥0 := 1 / 2 with hq
  have hq0 : 0 < q := by norm_num [hq]
  have hq1 : q < 1 := by norm_num [hq]
  obtain ⟨s₁, hs₁, hs₁s⟩ := exists_integral_near hξ s (mul_pos hq0 hr0)
  obtain ⟨M, -, hM⟩ := isIntegral_add_pow hs₁
  have hx0 : 0 < ξ' (xF C F) := (Valuation.pos_iff _).2 fun h ↦
    GaussFibre.transcendental_xF (C := C) (F := F) (h ▸ isAlgebraic_zero)
  obtain ⟨l, hl0, hl⟩ := NormedField.exists_norm_lt C
    (r := ((q * r / ξ' (xF C F) ^ M : ℝ≥0) : ℝ)) (by
      exact_mod_cast div_pos (mul_pos hq0 hr0) (pow_pos hx0 M))
  have hl' : ‖l‖₊ * ξ' (xF C F) ^ M < q * r := by
    rw [← lt_div_iff₀ (pow_pos hx0 M)]
    exact_mod_cast hl
  set s' := s₁ + algebraMap C F l * xF C F ^ M
  have hclose : ξ' (s' - s) < q * r := by
    rw [show s' - s = -(s - s₁) + algebraMap C F l * xF C F ^ M by ring]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt (by rwa [Valuation.map_neg]) ?_)
    rwa [map_mul, map_pow, hC]
  refine ⟨s', coordDense_of_near hs hq0 hq1 hr hclose.le, ?_, ?_,
    hM l (norm_pos_iff.1 hl0)⟩
  · intro halg
    obtain ⟨α, hα⟩ := exists_eq_algebraMap_of_isAlgebraic halg
    have := hr α
    rw [hα, ← Valuation.map_neg, neg_sub] at this
    exact absurd (this.trans_lt (hclose.trans (mul_lt_of_lt_one_left hr0 hq1))) (lt_irrefl _)
  · refine hs₁.add ((isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ l)).mul
      (IsIntegral.pow ?_ M))
    exact isIntegral_adjoin_of_mem (Algebra.self_mem_adjoin_singleton C _)

end Integral

end TypeFour

end SemistableReduction
