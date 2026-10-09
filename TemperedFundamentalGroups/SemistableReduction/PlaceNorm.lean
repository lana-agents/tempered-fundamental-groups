/-
Copyright (c) 2026 LANA Project. All rights reserved.
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

section Consequences

variable (hx0 : x ≠ 0) {N : ℕ} (hN : ∀ Q ∈ zeros k x, ord x Q ≤ N) {b : Idx k x → κ}
  (hb1 : ∀ i : Idx k x, i.1.1.valuation (b i) = exp (-(i.2 : ℤ)))
  (hb2 : ∀ (i : Idx k x) (Q : zeros k x), Q ≠ i.1 → Q.1.valuation (b i) ≤ exp (-(N : ℤ)))
include hx0 hN hb1 hb2

lemma exists_valuation_sum (a : Idx k x → k⟮x⟯) (i1 : Idx k x) (h1 : a i1 ≠ 0)
    (hmin : ∀ i, a i ≠ 0 → expo x (a i1) ≤ expo x (a i)) :
    ∃ j0 : Fin (ord x i1.1.1), j0 ≤ i1.2 ∧ i1.1.1.valuation (∑ i, (a i : κ) * b i) =
      exp (-((ord x i1.1.1 : ℤ) * expo x (a i1) + j0)) := by
  obtain ⟨j0, hj0, ha0, he0, hfirst⟩ := exists_first a i1 h1 hmin
  exact ⟨j0, hj0, valuation_sum_eq hx0 hN hb1 hb2 a _ i1.1 j0 ha0 he0
    (fun i hi ↦ hmin i hi) hfirst⟩

omit hx0 hN hb1 hb2 in
lemma sum_smul_eq (g : Idx k x → k⟮x⟯) : ∑ i, g i • b i = ∑ i, (g i : κ) * b i := by
  simp [Algebra.smul_def]

/-- The `b_{Q,j}` are linearly independent over `k(x)`. -/
theorem linearIndependent : LinearIndependent k⟮x⟯ b := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hgi
  obtain ⟨i1, h1, hm⟩ := exists_min g ⟨i, hgi⟩
  obtain ⟨j0, -, hv⟩ := exists_valuation_sum hx0 hN hb1 hb2 g i1 h1 hm
  rw [← sum_smul_eq, hg, map_zero] at hv
  exact exp_ne_zero hv.symm

/-- **Integrality**: the coordinates of an element regular at all zeros of `x` are regular at
`x = 0`. -/
theorem expo_nonneg (a : Idx k x → k⟮x⟯)
    (hy : ∀ Q ∈ zeros k x, Q.valuation (∑ i, (a i : κ) * b i) ≤ 1) :
    ∀ i, a i ≠ 0 → 0 ≤ expo x (a i) := by
  by_contra! H
  obtain ⟨i, hi, hneg⟩ := H
  obtain ⟨i1, h1, hm⟩ := exists_min a ⟨i, hi⟩
  obtain ⟨j0, -, hv⟩ := exists_valuation_sum hx0 hN hb1 hb2 a i1 h1 hm
  have hle := hy _ i1.1.2
  rw [hv, ← exp_zero, exp_le_exp] at hle
  have hlt := (hm i hi).trans_lt hneg
  have hj : (j0 : ℤ) < ord x i1.1.1 := by exact_mod_cast j0.2
  have : (ord x i1.1.1 : ℤ) * expo x (a i1) ≤ -(ord x i1.1.1 : ℤ) := by
    have := mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 hlt) (Int.natCast_nonneg
      (ord x i1.1.1))
    linarith
  linarith

/-- **Triangularity**: if `y` is regular at all zeros, `ord_{Q₁} y ≥ j₁ + 1` and `ord_Q y ≥ N`
at the other zeros, then the coordinates `a_{Q,j}` with `Q ≠ Q₁` or `j ≤ j₁` vanish at `x = 0`. -/
theorem one_le_expo (a : Idx k x → k⟮x⟯)
    (hy : ∀ Q ∈ zeros k x, Q.valuation (∑ i, (a i : κ) * b i) ≤ 1) (Q1 : zeros k x) (j1 : ℕ)
    (hQ1 : Q1.1.valuation (∑ i, (a i : κ) * b i) ≤ exp (-((j1 : ℤ) + 1)))
    (hother : ∀ Q : zeros k x, Q ≠ Q1 → Q.1.valuation (∑ i, (a i : κ) * b i) ≤ exp (-(N : ℤ))) :
    ∀ i, a i ≠ 0 → (i.1 ≠ Q1 ∨ (i.2 : ℕ) ≤ j1) → 1 ≤ expo x (a i) := by
  intro i hi hcond
  by_contra! hlt
  have hnn := expo_nonneg hx0 hN hb1 hb2 a hy
  have h0 : expo x (a i) = 0 := le_antisymm (Int.lt_add_one_iff.1 hlt) (hnn i hi)
  obtain ⟨j0, hj0, hv⟩ := exists_valuation_sum hx0 hN hb1 hb2 a i hi
    (fun i' hi' ↦ h0 ▸ hnn i' hi')
  rw [h0, mul_zero, zero_add] at hv
  have hjo : (j0 : ℕ) < ord x i.1.1 := j0.2
  by_cases hQ : i.1 = Q1
  · rcases hcond with hc | hc
    · exact hc hQ
    have h := hQ1
    rw [← hQ, hv, exp_le_exp] at h
    have : (j0 : ℕ) ≤ j1 := le_trans (by exact_mod_cast hj0) hc
    omega
  · have h := hother _ hQ
    rw [hv, exp_le_exp] at h
    have := hN _ i.1.2
    omega

end Consequences

/-! ### The norm specialization -/

/-- **Norm specialization at a place** (S6 (ii)). Let `x ∈ κ ∖ k` and `f ∈ κ` regular at all
zeros `Q` of `x`. Then `N_{κ/k(x)}(f)` is regular at every zero `Q₀` of `x`, and its value there
is `∏_Q f(Q) ^ ord_Q x`. -/
theorem res_norm_eq_prod (hx : x ∉ (algebraMap k κ).range) {f : κ}
    (hf : ∀ Q ∈ zeros k x, f ∈ Q.V) {Q₀ : CurvePlace k κ} (hQ₀ : Q₀ ∈ zeros k x) :
    ((Algebra.norm k⟮x⟯ f : k⟮x⟯) : κ) ∈ Q₀.V ∧
      Q₀.res ((Algebra.norm k⟮x⟯ f : k⟮x⟯) : κ) = ∏ Q ∈ zeros k x, Q.res f ^ ord x Q := by
  classical
  have hx0 : x ≠ 0 := fun h ↦ hx ⟨0, by rw [h, map_zero]⟩
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hx)
  set N := ∑ Q ∈ zeros k x, ord x Q
  have hN : ∀ Q ∈ zeros k x, ord x Q ≤ N := fun Q hQ ↦
    Finset.single_le_sum (f := fun Q ↦ ord x Q) (fun _ _ ↦ Nat.zero_le _) hQ
  -- the ramified orthonormal basis
  have hex (i : Idx k x) : ∃ w : κ, i.1.1.valuation w = exp (-(i.2 : ℤ)) ∧
      ∀ Q ∈ zeros k x, Q ≠ i.1.1 → Q.valuation w ≤ exp (-(N : ℤ)) :=
    exists_valuation_eq_and_le i.1.1 (zeros k x) _ (fun _ ↦ exp (-(N : ℤ)))
      fun _ ↦ exp_ne_zero
  choose b hb1 hb2' using hex
  have hb2 : ∀ (i : Idx k x) (Q : zeros k x), Q ≠ i.1 → Q.1.valuation (b i) ≤ exp (-(N : ℤ)) :=
    fun i Q hQ ↦ hb2' i Q.1 Q.2 fun h ↦ hQ (Subtype.ext h)
  have hli := linearIndependent hx0 hN hb1 hb2
  have hcard : Fintype.card (Idx k x) = Module.finrank k⟮x⟯ κ := by
    rw [Fintype.card_sigma, ← sum_ord hx]
    simp only [Fintype.card_fin]
    exact Finset.sum_coe_sort (zeros k x) (fun Q ↦ ord x Q)
  haveI : Nonempty (Idx k x) := by
    rw [← Fintype.card_pos_iff, hcard]
    exact Module.finrank_pos
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ∀ i, B i = b i := fun i ↦ by simp [B]
  -- values of the basis
  have hbQ (i : Idx k x) (Q : CurvePlace k κ) (hQ : Q ∈ zeros k x) : Q.valuation (b i) ≤ 1 := by
    by_cases h : Q = i.1.1
    · subst h
      rw [hb1 i, ← exp_zero, exp_le_exp]
      simp
    · refine (hb2' i Q hQ h).trans ?_
      rw [← exp_zero, exp_le_exp]
      simp
  -- coordinates
  have hcoord (y : κ) : y = ∑ i, (B.repr y i : κ) * b i := by
    conv_lhs => rw [← B.sum_repr y]
    rw [← sum_smul_eq]
    simp [hB]
  have hval_le (y : κ) (hy : ∀ Q ∈ zeros k x, y ∈ Q.V) :
      ∀ Q ∈ zeros k x, Q.valuation (∑ i, (B.repr y i : κ) * b i) ≤ 1 := fun Q hQ ↦ by
    rw [← hcoord y]
    exact Q.valuation_le_one_iff.2 (hy Q hQ)
  have hfb (i : Idx k x) : ∀ Q ∈ zeros k x, f * b i ∈ Q.V := fun Q hQ ↦
    mul_mem (hf Q hQ) (Q.valuation_le_one_iff.1 (hbQ i Q hQ))
  -- the subring of elements of `k(x)` regular at `x = 0`, and the residue map
  let O₀ : Subring k⟮x⟯ :=
    { carrier := {a | (a : κ) ∈ Q₀.V}
      mul_mem' := fun ha hb ↦ by simpa using mul_mem ha hb
      one_mem' := by simp
      add_mem' := fun ha hb ↦ by simpa using add_mem ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha ↦ by simpa using neg_mem (show ((a : k⟮x⟯) : κ) ∈ Q₀.V from ha) }
  let φ : O₀ →+* k :=
    { toFun := fun a ↦ Q₀.res ((a : k⟮x⟯) : κ)
      map_one' := by simpa using Q₀.res_one
      map_mul' := fun a b ↦ by simpa using Q₀.res_mul a.2 b.2
      map_zero' := by simpa using Q₀.res_zero
      map_add' := fun a b ↦ by simpa using Q₀.res_add a.2 b.2 }
  have hmemO (a : k⟮x⟯) (ha : a = 0 ∨ 0 ≤ expo x a) : a ∈ O₀ := by
    rcases ha with rfl | ha
    · exact O₀.zero_mem
    by_cases ha0 : a = 0
    · rw [ha0]; exact O₀.zero_mem
    change ((a : k⟮x⟯) : κ) ∈ Q₀.V
    rw [← Q₀.valuation_le_one_iff, valuation_eq_expo hx0 ha0 hQ₀, ← exp_zero, exp_le_exp]
    have := Int.natCast_nonneg (ord x Q₀)
    nlinarith
  have hres0 (a : k⟮x⟯) (ha : a = 0 ∨ 1 ≤ expo x a) : Q₀.res ((a : k⟮x⟯) : κ) = 0 := by
    rcases ha with rfl | ha
    · simpa using Q₀.res_zero
    by_cases ha0 : a = 0
    · rw [ha0]; simpa using Q₀.res_zero
    refine Q₀.res_eq_zero_of_lt_one ?_
    rw [valuation_eq_expo hx0 ha0 hQ₀, ← exp_zero, exp_lt_exp]
    have := one_le_ord hQ₀
    have h1 : (1 : ℤ) ≤ ord x Q₀ := by exact_mod_cast this
    nlinarith
  -- the matrix of `f`
  have hentry (i i' : Idx k x) : B.repr (f * b i) i' = 0 ∨ 0 ≤ expo x (B.repr (f * b i) i') := by
    by_cases h : B.repr (f * b i) i' = 0
    · exact Or.inl h
    · exact Or.inr (expo_nonneg hx0 hN hb1 hb2 _ (hval_le _ (hfb i)) i' h)
  have hM (i' i : Idx k x) : Algebra.leftMulMatrix B f i' i = B.repr (f * b i) i' := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hB]
  let M' : Matrix (Idx k x) (Idx k x) O₀ := fun i' i ↦
    ⟨Algebra.leftMulMatrix B f i' i, hmemO _ (by rw [hM]; exact hentry i i')⟩
  have hnorm : Algebra.norm k⟮x⟯ f = O₀.subtype M'.det := by
    rw [Algebra.norm_eq_matrix_det B, RingHom.map_det]
    rfl
  refine ⟨by rw [hnorm]; exact M'.det.2, ?_⟩
  have hφdet : Q₀.res ((Algebra.norm k⟮x⟯ f : k⟮x⟯) : κ) = (M'.map φ).det := by
    rw [hnorm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  rw [hφdet]
  -- the reduced matrix is lower triangular with diagonal `f(Q)`
  have hcol (i : Idx k x) : ∀ i', (i' = i ∨ i'.1 ≠ i.1 ∨ (i'.2 : ℕ) ≤ i.2) →
      Q₀.res ((B.repr (f * b i) i' : k⟮x⟯) : κ) =
        if i' = i then i.1.1.res f else 0 := by
    intro i' hi'
    set c := i.1.1.res f
    set y := f * b i - algebraMap k κ c * b i
    have hy : y = f * b i - (algebraMap k k⟮x⟯ c) • B i := by
      rw [hB, Algebra.smul_def]
      simp [y]
    have hrepr : B.repr y i' = B.repr (f * b i) i' -
        if i' = i then algebraMap k k⟮x⟯ c else 0 := by
      rw [hy, _root_.map_sub, map_smul, B.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
        Finsupp.single_apply]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    have hyV : ∀ Q ∈ zeros k x, y ∈ Q.V := fun Q hQ ↦
      sub_mem (hfb i Q hQ) (mul_mem (Q.algebraMap_mem c) (Q.valuation_le_one_iff.1 (hbQ i Q hQ)))
    have hfc : i.1.1.valuation (f - algebraMap k κ c) ≤ exp (-1) :=
      WithZero.le_exp_of_lt_exp_add_one (by
        rw [show (-1 : ℤ) + 1 = 0 by ring, exp_zero]
        exact i.1.1.valuation_sub_res_lt_one (hf _ i.1.2))
    have hyfac : y = (f - algebraMap k κ c) * b i := by simp [y]; ring
    have h1 := one_le_expo hx0 hN hb1 hb2 (B.repr y) (by
        intro Q hQ; rw [← hcoord y]; exact Q.valuation_le_one_iff.2 (hyV Q hQ)) i.1 i.2
      (by
        rw [← hcoord y, hyfac, map_mul, hb1 i]
        calc i.1.1.valuation (f - algebraMap k κ c) * exp (-(i.2 : ℤ))
            ≤ exp (-1) * exp (-(i.2 : ℤ)) := by gcongr
          _ = exp (-((i.2 : ℕ) + 1 : ℤ)) := by rw [← exp_add]; congr 1; ring)
      (by
        intro Q hQ
        rw [← hcoord y, hyfac, map_mul]
        calc Q.1.valuation (f - algebraMap k κ c) * Q.1.valuation (b i)
            ≤ 1 * exp (-(N : ℤ)) := by
              gcongr
              · exact Q.1.valuation_le_one_iff.2 (sub_mem (hf _ Q.2) (Q.1.algebraMap_mem c))
              · exact hb2 i Q hQ
          _ = exp (-(N : ℤ)) := one_mul _)
    have hzero : Q₀.res ((B.repr y i' : k⟮x⟯) : κ) = 0 := by
      refine hres0 _ ?_
      by_cases h0 : B.repr y i' = 0
      · exact Or.inl h0
      refine Or.inr (h1 i' h0 ?_)
      rcases hi' with rfl | h | h
      · exact Or.inr le_rfl
      · exact Or.inl h
      · exact Or.inr h
    rw [hrepr] at hzero
    have hmem1 : ((B.repr (f * b i) i' : k⟮x⟯) : κ) ∈ Q₀.V := hmemO _ (hentry i i')
    split_ifs with hii
    · have hsplit : ((B.repr (f * b i) i' : k⟮x⟯) : κ) =
          ((B.repr (f * b i) i' - algebraMap k k⟮x⟯ c : k⟮x⟯) : κ) + algebraMap k κ c := by
        simp
      rw [if_pos hii] at hzero
      have hmem2 : ((B.repr (f * b i) i' - algebraMap k k⟮x⟯ c : k⟮x⟯) : κ) ∈ Q₀.V := by
        have : ((B.repr (f * b i) i' - algebraMap k k⟮x⟯ c : k⟮x⟯) : κ) =
            ((B.repr (f * b i) i' : k⟮x⟯) : κ) - algebraMap k κ c := by simp
        rw [this]
        exact sub_mem hmem1 (Q₀.algebraMap_mem c)
      rw [hsplit, Q₀.res_add hmem2 (Q₀.algebraMap_mem c), hzero, zero_add, Q₀.res_algebraMap]
    · rwa [if_neg hii, sub_zero] at hzero
  -- a linear order on the indices: lexicographic in (block, index)
  let σ := Fintype.equivFin (zeros k x)
  let ρ : Idx k x → Lex (ℕ × ℕ) := fun i ↦ toLex ((σ i.1 : ℕ), (i.2 : ℕ))
  have hρ : Function.Injective ρ := by
    rintro ⟨Q, j⟩ ⟨Q', j'⟩ h
    simp only [ρ, toLex_inj, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hQ : Q = Q' := σ.injective (Fin.ext h1)
    subst hQ
    have : j = j' := Fin.ext h2
    subst this
    rfl
  have hlt (i' i : Idx k x) (h : ρ i' < ρ i) : i' ≠ i ∧ (i'.1 ≠ i.1 ∨ (i'.2 : ℕ) ≤ i.2) := by
    refine ⟨fun he ↦ by rw [he] at h; exact lt_irrefl _ h, ?_⟩
    simp only [ρ, Prod.Lex.toLex_lt_toLex] at h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl fun he ↦ by rw [he] at h; exact lt_irrefl _ h
    · exact Or.inr h2.le
  let e : Idx k x ≃ Set.range ρ := Equiv.ofInjective ρ hρ
  have he (p : Set.range ρ) : ρ (e.symm p) = p := by
    have := e.apply_symm_apply p
    exact congrArg Subtype.val this
  set R := M'.map φ
  have htri : (R.submatrix e.symm e.symm).BlockTriangular OrderDual.toDual := by
    intro p' p h
    have h' : ρ (e.symm p') < ρ (e.symm p) := by
      rw [he, he]
      exact h
    obtain ⟨hne, hcond⟩ := hlt _ _ h'
    change Q₀.res ((Algebra.leftMulMatrix B f (e.symm p') (e.symm p) : k⟮x⟯) : κ) = 0
    rw [hM, hcol _ _ (Or.inr hcond), if_neg hne]
  rw [← Matrix.det_submatrix_equiv_self e.symm R, Matrix.det_of_lowerTriangular _ htri]
  rw [show (∏ p : Set.range ρ, R.submatrix e.symm e.symm p p) = ∏ i, R i i from
    Fintype.prod_equiv e.symm _ _ fun p ↦ rfl]
  have hdiag (i : Idx k x) : R i i = i.1.1.res f := by
    change Q₀.res ((Algebra.leftMulMatrix B f i i : k⟮x⟯) : κ) = _
    rw [hM, hcol i i (Or.inl rfl), if_pos rfl]
  simp_rw [hdiag]
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Finset.prod_coe_sort (zeros k x) (fun Q ↦ Q.res f ^ ord x Q)

end PlaceNorm

end SemistableReduction
