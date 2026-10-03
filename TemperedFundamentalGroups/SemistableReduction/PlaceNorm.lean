/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SpecialFibre

/-!
# Norm specialization at a place of a curve

Blueprint §9.9, W7 layer S6 (ii). Let `k` be algebraically closed, `κ / k` a function field of one
variable and `x ∈ κ ∖ k`. Let `Z = {Q : x(Q) = 0}` be the zeros of `x`, with orders
`e_Q = ord_Q x` (`Σ_{Q ∈ Z} e_Q = [κ : k(x)]`, R5). For `f ∈ κ` regular at all `Q ∈ Z`, the norm
`N_{κ/k(x)}(f)` is regular at `x = 0` and

  `N_{κ/k(x)}(f)(0) = ∏_{Q ∈ Z} f(Q) ^ e_Q` (`res_norm_eq_prod`).

No separability of `κ / k(x)` is needed (the residue extensions of a wild cover are often purely
inseparable). Proof: a **ramified orthonormal basis**. For `Q ∈ Z` and `j < e_Q` choose
`b_{Q,j}` with `ord_Q b_{Q,j} = j` and `ord_{Q'} b_{Q,j} ≥ N` for `Q' ≠ Q` (weak approximation,
`exists_valuation_eq_and_le`, `N > max e_Q`). Elements `a ∈ k(x)ˣ` have `ord_Q a = e_Q · o(a)`
for all `Q ∈ Z` (`exists_zpow_of_mem_adjoin`). If `μ` is the least `o(a_i)` of a nonzero family
of coefficients and `j₀` the least `j` with `o(a_{Q₀,j}) = μ` in a block `Q₀` where `μ` is attained,
then `ord_{Q₀} (Σ aᵢ bᵢ) = e_{Q₀} μ + j₀` (the minimum is unique: the `j < e_Q` are distinct
modulo `e_Q`, other blocks have order `≥ N`). Hence the `b_{Q,j}` are independent, a basis
(`Σ e_Q = [κ : k(x)]`), coordinates of elements regular on `Z` are regular at `0`, and the matrix
of `f` reduces at `x = 0` to a lower triangular matrix with diagonal entries `f(Q)` (`e_Q` times).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ)

lemma res_mul {y z : κ} (hy : y ∈ Q.V) (hz : z ∈ Q.V) : Q.res (y * z) = Q.res y * Q.res z := by
  refine Q.res_eq_of_valuation_sub_lt_one ?_
  have : y * z - algebraMap k κ (Q.res y * Q.res z) =
      (y - algebraMap k κ (Q.res y)) * z + algebraMap k κ (Q.res y) *
        (z - algebraMap k κ (Q.res z)) := by rw [map_mul]; ring
  rw [this]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_) <;> rw [map_mul]
  · exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (Q.valuation_sub_res_lt_one hy)
      (Q.valuation_le_one_iff.2 hz)
  · exact mul_lt_one_of_nonneg_of_lt_one_right (Q.valuation_algebraMap_le_one _) zero_le
      (Q.valuation_sub_res_lt_one hz)

lemma res_one : Q.res (1 : κ) = 1 := by simpa using Q.res_algebraMap (1 : k)

lemma res_zero : Q.res (0 : κ) = 0 := by simpa using Q.res_algebraMap (0 : k)

lemma res_eq_zero_of_lt_one {y : κ} (hy : Q.valuation y < 1) : Q.res y = 0 :=
  Q.res_eq_of_valuation_sub_lt_one (by simpa using hy)

end CurvePlace

namespace PlaceNorm

open CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

variable (k) in
/-- The zeros of `x`: the support of the pole divisor of `x⁻¹`. -/
noncomputable def zeros (x : κ) : Finset (CurvePlace k κ) := (poleDivisor k x⁻¹).support

/-- The order `e_Q = ord_Q x` of a zero `Q` of `x`. -/
noncomputable def ord (x : κ) (Q : CurvePlace k κ) : ℕ := Q.poleOrder x⁻¹

lemma mem_zeros {x : κ} {Q : CurvePlace k κ} : Q ∈ zeros k x ↔ x⁻¹ ∉ Q.V := by
  rw [zeros, Finsupp.mem_support_iff, poleDivisor_apply, Ne, Nat.cast_eq_zero,
    Q.poleOrder_eq_zero_iff]

lemma one_le_ord {x : κ} {Q : CurvePlace k κ} (hQ : Q ∈ zeros k x) : 1 ≤ ord x Q :=
  Q.one_le_poleOrder (mem_zeros.1 hQ)

lemma valuation_x {x : κ} {Q : CurvePlace k κ} (hQ : Q ∈ zeros k x) :
    Q.valuation x = exp (-(ord x Q : ℤ)) := by
  have h := Q.valuation_eq_exp_poleOrder (mem_zeros.1 hQ)
  rw [map_inv₀] at h
  rw [ord, exp_neg, ← h, inv_inv]

lemma valuation_x_lt_one {x : κ} {Q : CurvePlace k κ} (hQ : Q ∈ zeros k x) :
    Q.valuation x < 1 := by
  rw [valuation_x hQ, ← exp_zero, exp_lt_exp]
  have := one_le_ord hQ
  omega

/-- `Σ_{Q ∈ Z} e_Q = [κ : k(x)]` (R5). -/
theorem sum_ord {x : κ} (hx : x ∉ (algebraMap k κ).range) :
    ∑ Q ∈ zeros k x, ord x Q = Module.finrank k⟮x⟯ κ := by
  have hx' : x⁻¹ ∉ (algebraMap k κ).range := by
    rintro ⟨c, hc⟩
    exact hx ⟨c⁻¹, by rw [map_inv₀, hc, inv_inv]⟩
  have h := degree_poleDivisor hx'
  rw [adjoin_inv_eq] at h
  rw [Finsupp.degree_apply] at h
  simp only [poleDivisor_apply] at h
  rw [zeros]
  exact_mod_cast h

/-! ### Exponents of elements of `k(x)` -/

variable {x : κ}

lemma exists_exponent (hx0 : x ≠ 0) (a : k⟮x⟯) (ha : a ≠ 0) :
    ∃ o : ℤ, ∀ Q ∈ zeros k x, Q.valuation (a : κ) = exp (-(ord x Q : ℤ) * o) := by
  obtain ⟨o, ho⟩ := exists_zpow_of_mem_adjoin hx0 a.2 (by simpa using ha)
  refine ⟨o, fun Q hQ ↦ ?_⟩
  rw [ho Q (valuation_x_lt_one hQ), valuation_x hQ, ← exp_zsmul, smul_eq_mul, mul_comm]

open Classical in
/-- The exponent `o(a)` with `ord_Q a = e_Q · o(a)` for all zeros `Q` of `x` (`0` for `a = 0`). -/
noncomputable def expo (x : κ) (a : k⟮x⟯) : ℤ :=
  if h : x ≠ 0 ∧ a ≠ 0 then (exists_exponent h.1 a h.2).choose else 0

lemma valuation_eq_expo (hx0 : x ≠ 0) {a : k⟮x⟯} (ha : a ≠ 0) {Q : CurvePlace k κ}
    (hQ : Q ∈ zeros k x) : Q.valuation (a : κ) = exp (-(ord x Q : ℤ) * expo x a) := by
  rw [expo, dif_pos ⟨hx0, ha⟩]
  exact (exists_exponent hx0 a ha).choose_spec Q hQ

/-! ### The ramified orthonormal basis -/

variable (k x) in
/-- Indices `(Q, j)`, `Q ∈ Z`, `j < e_Q`. -/
abbrev Idx : Type _ := Σ Q : zeros k x, Fin (ord x Q.1)

section Basis

variable (hx0 : x ≠ 0) {N : ℕ} (hN : ∀ Q ∈ zeros k x, ord x Q ≤ N) {b : Idx k x → κ}
  (hb1 : ∀ i : Idx k x, i.1.1.valuation (b i) = exp (-(i.2 : ℤ)))
  (hb2 : ∀ (i : Idx k x) (Q : zeros k x), Q ≠ i.1 → Q.1.valuation (b i) ≤ exp (-(N : ℤ)))
include hx0 hN hb1 hb2

/-- **The key valuation computation.** If `μ` is the least exponent of the nonzero coefficients
and `j₀` the least index of the block `Q₀` with exponent `μ`, then
`ord_{Q₀} (Σ aᵢ bᵢ) = e_{Q₀} μ + j₀`. -/
theorem valuation_sum_eq (a : Idx k x → k⟮x⟯) (μ : ℤ) (Q0 : zeros k x) (j0 : Fin (ord x Q0.1))
    (h0 : a ⟨Q0, j0⟩ ≠ 0) (hμ : expo x (a ⟨Q0, j0⟩) = μ)
    (hmin : ∀ i, a i ≠ 0 → μ ≤ expo x (a i))
    (hfirst : ∀ j : Fin (ord x Q0.1), j < j0 → a ⟨Q0, j⟩ ≠ 0 → μ < expo x (a ⟨Q0, j⟩)) :
    Q0.1.valuation (∑ i, (a i : κ) * b i) = exp (-((ord x Q0.1 : ℤ) * μ + j0)) := by
  classical
  have hval (i : Idx k x) (hi : a i ≠ 0) : Q0.1.valuation ((a i : κ) * b i) =
      exp (-(ord x Q0.1 : ℤ) * expo x (a i)) * Q0.1.valuation (b i) := by
    rw [map_mul, valuation_eq_expo hx0 hi Q0.2]
  have hlt0 : (j0 : ℤ) < ord x Q0.1 := by exact_mod_cast j0.2
  have hb0 : Q0.1.valuation (b ⟨Q0, j0⟩) = exp (-(j0 : ℤ)) := hb1 ⟨Q0, j0⟩
  rw [Valuation.map_sum_eq_of_lt (v := Q0.1.valuation) (s := Finset.univ)
    (f := fun i ↦ (a i : κ) * b i) (Finset.mem_univ ⟨Q0, j0⟩) fun i hi ↦ ?_]
  · rw [hval _ h0, hb0, hμ, ← exp_add]
    congr 1
    ring
  · have hne : i ≠ ⟨Q0, j0⟩ := Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hi).2
    rw [hval _ h0, hb0, hμ, ← exp_add]
    by_cases hai : a i = 0
    · rw [hai, ZeroMemClass.coe_zero, zero_mul, map_zero]
      exact zero_lt_iff.2 exp_ne_zero
    rw [hval i hai]
    have hmi := hmin i hai
    obtain ⟨Q, j⟩ := i
    by_cases hQQ : Q = Q0
    · subst hQQ
      have hbj : Q.1.valuation (b ⟨Q, j⟩) = exp (-(j : ℤ)) := hb1 ⟨Q, j⟩
      rw [hbj, ← exp_add, exp_lt_exp]
      have hj : j ≠ j0 := fun h ↦ hne (by rw [h])
      rcases lt_or_eq_of_le hmi with hmi | hmi
      · have : (ord x Q.1 : ℤ) * μ + ord x Q.1 ≤ ord x Q.1 * expo x (a ⟨Q, j⟩) := by
          have := mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 hmi)
            (Int.natCast_nonneg (ord x Q.1))
          linarith
        have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg _
        linarith
      · have hjj : j0 < j := by
          rcases lt_or_gt_of_ne hj with h | h
          · exact absurd (hfirst j h hai) (by rw [hmi]; exact lt_irrefl _)
          · exact h
        have : (j0 : ℤ) < j := by exact_mod_cast hjj
        rw [← hmi]
        linarith
    · have hb := hb2 ⟨Q, j⟩ Q0 (Ne.symm hQQ)
      calc exp (-(ord x Q0.1 : ℤ) * expo x (a ⟨Q, j⟩)) * Q0.1.valuation (b ⟨Q, j⟩)
          ≤ exp (-(ord x Q0.1 : ℤ) * expo x (a ⟨Q, j⟩)) * exp (-(N : ℤ)) := by gcongr
        _ < exp (-(ord x Q0.1 : ℤ) * μ + -(j0 : ℤ)) := by
          rw [← exp_add, exp_lt_exp]
          have h1 := mul_le_mul_of_nonneg_left hmi (Int.natCast_nonneg (ord x Q0.1))
          have h2 : (ord x Q0.1 : ℤ) ≤ N := by exact_mod_cast hN Q0.1 Q0.2
          linarith

end Basis

/-- Given a coefficient `a i₁ ≠ 0` of least exponent, the least index `j₀ ≤ i₁.2` of the block of
`i₁` with that exponent. -/
lemma exists_first (a : Idx k x → k⟮x⟯) (i1 : Idx k x) (h1 : a i1 ≠ 0)
    (hmin : ∀ i, a i ≠ 0 → expo x (a i1) ≤ expo x (a i)) :
    ∃ j0 : Fin (ord x i1.1.1), j0 ≤ i1.2 ∧ a ⟨i1.1, j0⟩ ≠ 0 ∧
      expo x (a ⟨i1.1, j0⟩) = expo x (a i1) ∧
      ∀ j : Fin (ord x i1.1.1), j < j0 → a ⟨i1.1, j⟩ ≠ 0 →
        expo x (a i1) < expo x (a ⟨i1.1, j⟩) := by
  classical
  set T := Finset.univ.filter fun j : Fin (ord x i1.1.1) ↦
    a ⟨i1.1, j⟩ ≠ 0 ∧ expo x (a ⟨i1.1, j⟩) = expo x (a i1)
  have hT : i1.2 ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, rfl⟩
  have hTne : T.Nonempty := ⟨_, hT⟩
  obtain ⟨-, hj0a, hj0e⟩ := Finset.mem_filter.1 (T.min'_mem hTne)
  refine ⟨T.min' hTne, T.min'_le _ hT, hj0a, hj0e, fun j hj ha ↦ ?_⟩
  rcases lt_or_eq_of_le (hmin _ ha) with h | h
  · exact h
  · exact absurd (T.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha, h.symm⟩))
      (not_le.2 hj)

/-- A nonzero family of coefficients has a nonzero coefficient of least exponent. -/
lemma exists_min (a : Idx k x → k⟮x⟯) (h : ∃ i, a i ≠ 0) :
    ∃ i1, a i1 ≠ 0 ∧ ∀ i, a i ≠ 0 → expo x (a i1) ≤ expo x (a i) := by
  classical
  set S := Finset.univ.filter fun i ↦ a i ≠ 0
  have hS : S.Nonempty := let ⟨i, hi⟩ := h; ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨i1, hi1, he⟩ := S.exists_min_image (fun i ↦ expo x (a i)) hS
  exact ⟨i1, (Finset.mem_filter.1 hi1).2, fun i hi ↦ he i (Finset.mem_filter.2
    ⟨Finset.mem_univ _, hi⟩)⟩

end PlaceNorm

end SemistableReduction
