/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Setup.Valuation

/-!
# F. K. Schmidt's theorem for henselian discrete valuation rings

We show that a field `k` which is not separably closed has at most one henselian discrete
valuation ring (`eq_of_isHenselianDVR`); in particular `canonicalValuationSubring k` is this
valuation ring whenever it exists (`canonicalValuationSubring_eq`).

## Main steps

* `HenselianLocalRing.exists_isRoot_of_eval_eq`: **Newton's lemma** in a henselian local ring:
  if `f(r) = f'(r)² c` with `c` in the maximal ideal, then `f` has a root. This is deduced from
  the (monic, simple residue root) definition of henselianity by a reversal trick.
* `ValuationSubring.exists_isRoot_of_valuation_lt`: the same for a henselian valuation subring
  `O` of `k` and `f ∈ k[X]` with coefficients in `O`: if `v(f(r)) < v(f'(r))²`, then `f` has a
  root in `O`.
-/

open Polynomial IsLocalRing

namespace TemperedFundamentalGroups

section Newton

/-- In a local ring, a unit plus an element of the maximal ideal is a unit. -/
lemma isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {u m : R}
    (hu : IsUnit u) (hm : m ∈ maximalIdeal R) : IsUnit (u + m) := by
  by_contra h
  have h' : u + m ∈ maximalIdeal R := (mem_maximalIdeal _).2 h
  have : u ∈ maximalIdeal R := by simpa using sub_mem h' hm
  exact (mem_maximalIdeal _).1 this hu

/-- **Newton's lemma** in a henselian local ring: if `f(r) = f'(r)² c` with `c` in the maximal
ideal, then `f` has a root.

Writing `e = f'(r)` and `tₖ` for the Taylor coefficients of `f` at `r`, a root is `r + e c / w`
where `w` is a unit root of the monic polynomial
`W^(M+2) + W^(M+1) + ∑ₖ tₖ₊₂ eᵏ cᵏ⁺¹ W^(M-k)`, which reduces to `W^(M+1) (W + 1)` modulo the
maximal ideal and hence has a root `w ≡ -1` by henselianity. -/
theorem HenselianLocalRing.exists_isRoot_of_eval_eq {R : Type*} [CommRing R]
    [HenselianLocalRing R] (f : R[X]) (r c : R) (hc : c ∈ maximalIdeal R)
    (hf : f.eval r = f.derivative.eval r ^ 2 * c) : ∃ a, f.IsRoot a := by
  set e := f.derivative.eval r with he
  set T := taylor r f with hT
  set M := f.natDegree with hM
  set b : ℕ → R := fun k ↦ T.coeff (k + 2) * e ^ k * c ^ (k + 1) with hb
  set E : R[X] := ∑ k ∈ Finset.range (M + 1), C (b k) * X ^ (M - k) with hE
  set P : R[X] := X ^ (M + 2) + X ^ (M + 1) + E with hP
  have hbm : ∀ k, b k ∈ maximalIdeal R := fun k ↦
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hc _ (Nat.succ_pos _))
  have hEv : E.eval (-1) ∈ maximalIdeal R := by
    simp only [hE, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_right _ _ (hbm k)
  have hEd : E.derivative.eval (-1) ∈ maximalIdeal R := by
    simp only [hE, derivative_sum, derivative_C_mul_X_pow, eval_finsetSum, eval_mul, eval_C,
      eval_pow, eval_X]
    exact Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hbm k))
  have hEdeg : E ∈ degreeLT R (M + 1) := by
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [mem_degreeLT]
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le (Nat.sub_le _ _)
  have hPm : P.Monic := by
    rw [hP, add_assoc]
    refine (monic_X_pow _).add_of_left ?_
    rw [degree_X_pow]
    have h1 : X ^ (M + 1) + E ∈ degreeLT R (M + 2) :=
      add_mem (mem_degreeLT.2 ((degree_X_pow_le _).trans_lt (by exact_mod_cast Nat.lt_succ_self _)))
        (degreeLT_mono (by omega) hEdeg)
    exact mem_degreeLT.1 h1
  have hPe : P.eval (-1) ∈ maximalIdeal R := by
    have : P.eval (-1) = ((-1) ^ (M + 2) + (-1) ^ (M + 1)) + E.eval (-1) := by simp [hP]
    rw [this, show ((-1 : R) ^ (M + 2) + (-1) ^ (M + 1)) = 0 by ring, zero_add]
    exact hEv
  have hPd : IsUnit (P.derivative.eval (-1)) := by
    have : P.derivative.eval (-1) = -(-1) ^ M + E.derivative.eval (-1) := by
      simp only [hP, derivative_add, derivative_X_pow, eval_add, eval_mul, eval_C, eval_pow,
        eval_X]
      push_cast
      ring
    rw [this]
    exact isUnit_add_of_mem_maximalIdeal ((isUnit_one.neg).pow _).neg hEd
  obtain ⟨w, hw, hw1⟩ := HenselianLocalRing.is_henselian P hPm (-1) hPe hPd
  have hwu : IsUnit w := by
    have := isUnit_add_of_mem_maximalIdeal isUnit_one.neg hw1
    simpa using this
  obtain ⟨z, hwz⟩ := hwu.exists_right_inv
  refine ⟨r + e * c * z, ?_⟩
  have hT0 : T.coeff 0 = e ^ 2 * c := by rw [hT, taylor_coeff_zero, hf]
  have hT1 : T.coeff 1 = e := by rw [hT, taylor_coeff_one]
  have hfe : f.eval (r + e * c * z) =
      ∑ k ∈ Finset.range (M + 1), T.coeff (k + 2) * (e * c * z) ^ (k + 2)
        + e * (e * c * z) + e ^ 2 * c := by
    rw [add_comm r, ← taylor_eval, ← hT,
      eval_eq_sum_range' (n := M + 3) (by rw [hT, natDegree_taylor]; omega),
      Finset.sum_range_succ', Finset.sum_range_succ', hT0, hT1]
    simp
  have hPw : P.eval w =
      w ^ (M + 2) + w ^ (M + 1) + ∑ k ∈ Finset.range (M + 1), b k * w ^ (M - k) := by
    simp [hP, hE, eval_finsetSum]
  have hsum : w ^ (M + 2) * ∑ k ∈ Finset.range (M + 1), T.coeff (k + 2) * (e * c * z) ^ (k + 2) =
      e ^ 2 * c * ∑ k ∈ Finset.range (M + 1), b k * w ^ (M - k) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have key : w ^ (M + 2) * z ^ (k + 2) = w ^ (M - k) := by
      rw [show M + 2 = (M - k) + (k + 2) by omega, pow_add, mul_assoc, ← mul_pow, hwz, one_pow,
        mul_one]
    simp only [hb]
    linear_combination (T.coeff (k + 2) * e ^ (k + 2) * c ^ (k + 2)) * key
  have hmain : w ^ (M + 2) * f.eval (r + e * c * z) = e ^ 2 * c * P.eval w := by
    rw [hfe, hPw]
    linear_combination hsum + (e ^ 2 * c * w ^ (M + 1)) * hwz
  rw [hw.eq_zero, mul_zero] at hmain
  exact (hwu.pow _).mul_right_eq_zero.1 hmain

end Newton

section ValuationSubring

variable {k : Type*} [Field k]

/-- A polynomial over `k` lifts to the valuation subring `O` iff its coefficients lie in `O`. -/
lemma mem_lifts_iff_coeff_mem (O : ValuationSubring k) (P : k[X]) :
    P ∈ lifts (algebraMap O k) ↔ ∀ i, P.coeff i ∈ O := by
  rw [lifts_iff_coeff_lifts]
  refine forall_congr' fun i ↦ ⟨?_, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨x, hx⟩
  rw [← hx]
  exact x.2

lemma coe_eval_valuationSubring {O : ValuationSubring k} (F : O[X]) (r : O) :
    ((F.eval r : O) : k) = (F.map (algebraMap O k)).eval (r : k) := by
  rw [eval_map]
  exact (eval₂_at_apply (algebraMap O k) r).symm

/-- A polynomial with coefficients in `O` takes values in `O` on `O`. -/
lemma eval_mem_of_mem_lifts {O : ValuationSubring k} {P : k[X]}
    (hP : P ∈ lifts (algebraMap O k)) {r : k} (hr : r ∈ O) : P.eval r ∈ O := by
  obtain ⟨Q, rfl⟩ := (mem_lifts _).1 hP
  rw [show r = ((⟨r, hr⟩ : O) : k) from rfl, ← coe_eval_valuationSubring]
  exact SetLike.coe_mem _

/-- Valuation subrings are integrally closed: a root of a monic polynomial with coefficients in
`O` lies in `O`. -/
lemma mem_of_monic_of_eval_eq_zero {O : ValuationSubring k} {P : k[X]}
    (hP : P ∈ lifts (algebraMap O k)) (hm : P.Monic) {r : k} (hr : P.eval r = 0) : r ∈ O := by
  obtain ⟨Q, hQ⟩ := (mem_lifts _).1 hP
  have hQm : Q.Monic := monic_of_injective (IsFractionRing.injective O k) (hQ ▸ hm)
  have : IsIntegral O r := ⟨Q, hQm, by rw [← eval_map, hQ, hr]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  rw [← hy]
  exact y.2

/-- Every polynomial over `k` has a nonzero multiple by an element of `O` with coefficients
in `O`. -/
lemma exists_mul_mem_lifts (O : ValuationSubring k) (P : k[X]) :
    ∃ d : k, d ≠ 0 ∧ d ∈ O ∧ C d * P ∈ lifts (algebraMap O k) := by
  obtain ⟨b, hb, hP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) P
  refine ⟨algebraMap O k b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb,
    b.2, ?_⟩
  rw [← smul_eq_C_mul, algebraMap_smul]
  exact (mem_lifts _).2 ⟨_, hP⟩

/-- **Newton's lemma** for a henselian valuation subring `O` of `k`: if `f ∈ k[X]` has
coefficients in `O`, `r ∈ O` and `v(f(r)) < v(f'(r))²`, then `f` has a root in `O`. -/
theorem exists_eval_eq_zero_of_valuation_lt (O : ValuationSubring k) [HenselianLocalRing O]
    {f : k[X]} (hf : f ∈ lifts (algebraMap O k)) {r : k} (hr : r ∈ O)
    (h : O.valuation (f.eval r) < O.valuation (f.derivative.eval r) ^ 2) :
    ∃ a ∈ O, f.eval a = 0 := by
  obtain ⟨F, rfl⟩ := (mem_lifts _).1 hf
  set e := (F.map (algebraMap O k)).derivative.eval r with he
  have he0 : e ≠ 0 := by
    rintro h0
    rw [h0, map_zero, zero_pow two_ne_zero] at h
    exact not_lt_zero h
  set c := (F.map (algebraMap O k)).eval r / e ^ 2 with hc
  have hcv : O.valuation c < 1 := by
    rw [hc, map_div₀, map_pow]
    exact (div_lt_one₀ (pow_pos (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 he0)) _)).2 h
  have hcO : c ∈ O := (O.valuation_le_one_iff c).1 hcv.le
  have hFc : F.eval ⟨r, hr⟩ = (F.derivative.eval ⟨r, hr⟩) ^ 2 * ⟨c, hcO⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_eval_valuationSubring,
      ← derivative_map]
    rw [← he, hc]
    field_simp
  obtain ⟨a, ha⟩ := HenselianLocalRing.exists_isRoot_of_eval_eq F ⟨r, hr⟩ ⟨c, hcO⟩
    ((O.valuation_lt_one_iff _).2 hcv) hFc
  refine ⟨a, a.2, ?_⟩
  rw [← coe_eval_valuationSubring, ha.eq_zero, ZeroMemClass.coe_zero]

end ValuationSubring

section Independence

variable {k : Type*} [Field k]

/-- Discrete valuation rings have rank one: if `v(x) < 1` and `δ ≠ 0`, then `v(x)ᴺ < v(δ)` for
some `N`. -/
lemma exists_valuation_pow_lt (O : ValuationSubring k) [IsDiscreteValuationRing O] {x δ : k}
    (hx : O.valuation x < 1) (hδ : δ ≠ 0) : ∃ N, O.valuation x ^ N < O.valuation δ := by
  have hδ0 : 0 < O.valuation δ := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hδ)
  by_cases hδO : δ ∈ O
  swap
  · refine ⟨1, ?_⟩
    rw [pow_one]
    exact hx.trans (not_le.1 fun h ↦ hδO ((O.valuation_le_one_iff δ).1 h))
  by_cases hx0 : x = 0
  · exact ⟨1, by simpa [hx0] using hδ0⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hxO : x ∈ O := (O.valuation_le_one_iff x).1 hx.le
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨x, hxO⟩ : O)) (fun h ↦ hx0 (congrArg Subtype.val h)) hπ
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨δ, hδO⟩ : O)) (fun h ↦ hδ (congrArg Subtype.val h)) hπ
  set q := O.valuation π
  have hq1 : q < 1 := (O.valuation_lt_one_iff π).1 ((mem_maximalIdeal π).2 hπ.not_isUnit)
  have hq0 : 0 < q :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 fun h ↦ hπ.ne_zero (Subtype.ext h))
  have hvx : O.valuation x = q ^ m := by
    have := congrArg (fun y : O ↦ O.valuation (y : k)) hu
    simpa [O.valuation_unit] using this
  have hvδ : O.valuation δ = q ^ n := by
    have := congrArg (fun y : O ↦ O.valuation (y : k)) hw
    simpa [O.valuation_unit] using this
  have hm : m ≠ 0 := by
    rintro rfl
    rw [hvx, pow_zero] at hx
    exact lt_irrefl _ hx
  refine ⟨n + 1, ?_⟩
  rw [hvx, hvδ, ← pow_mul]
  exact (pow_le_pow_right_of_le_one' hq1.le (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm))
    ).trans_lt (pow_lt_pow_right_of_lt_one₀ hq0 hq1 (Nat.lt_succ_self n))

/-- A discrete valuation ring of `k` is not all of `k`. -/
lemma ne_top_of_isDiscreteValuationRing (O : ValuationSubring k) [IsDiscreteValuationRing O] :
    O ≠ ⊤ := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  apply hπ.not_isUnit
  have hπ0 : (π : k) ≠ 0 := fun h0 ↦ hπ.ne_zero (Subtype.ext h0)
  have hinv : (π : k)⁻¹ ∈ O := (SetLike.ext_iff.1 h _).2 (ValuationSubring.mem_top _)
  exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hπ0))

/-- Two distinct discrete valuation rings of a field are incomparable (a discrete valuation ring
is maximal among the proper valuation subrings). -/
lemma exists_mem_not_mem_of_ne {O₁ O₂ : ValuationSubring k} [IsDiscreteValuationRing O₁]
    [IsDiscreteValuationRing O₂] (hne : O₁ ≠ O₂) : ∃ a ∈ O₁, a ∉ O₂ := by
  by_contra! h
  exact hne (ValuationSubring.eq_of_le_of_ne_top O₁ h (ne_top_of_isDiscreteValuationRing O₂))

/-- **Approximation** for two distinct discrete valuation rings: there is `u ∈ k` which is
arbitrarily close to `1` for `O₁` and arbitrarily close to `0` for `O₂`. -/
lemma exists_valuation_one_sub_lt {O₁ O₂ : ValuationSubring k} [IsDiscreteValuationRing O₁]
    [IsDiscreteValuationRing O₂] (hne : O₁ ≠ O₂) {δ β : k} (hδ : δ ≠ 0) (hβ : β ≠ 0) :
    ∃ u : k, O₁.valuation (1 - u) < O₁.valuation δ ∧ O₂.valuation u < O₂.valuation β := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_mem_not_mem_of_ne hne
  obtain ⟨b, hb₂, hb₁⟩ := exists_mem_not_mem_of_ne hne.symm
  have hb0 : b ≠ 0 := by rintro rfl; exact hb₁ (zero_mem _)
  have ha0 : a ≠ 0 := by rintro rfl; exact ha₂ (zero_mem _)
  have hv₁b : 1 < O₁.valuation b := not_le.1 fun h ↦ hb₁ ((O₁.valuation_le_one_iff b).1 h)
  have hv₂a : 1 < O₂.valuation a := not_le.1 fun h ↦ ha₂ ((O₂.valuation_le_one_iff a).1 h)
  set x := a / b with hx
  have hx0 : x ≠ 0 := div_ne_zero ha0 hb0
  have hx₁ : O₁.valuation x < 1 := by
    rw [hx, map_div₀, div_lt_one₀ (zero_lt_one.trans hv₁b)]
    exact ((O₁.valuation_le_one_iff a).2 ha₁).trans_lt hv₁b
  have hx₂ : O₂.valuation x⁻¹ < 1 := by
    rw [hx, inv_div, map_div₀, div_lt_one₀ (zero_lt_one.trans hv₂a)]
    exact ((O₂.valuation_le_one_iff b).2 hb₂).trans_lt hv₂a
  obtain ⟨N₁, hN₁⟩ := exists_valuation_pow_lt O₁ hx₁ hδ
  obtain ⟨N₂, hN₂⟩ := exists_valuation_pow_lt O₂ hx₂ hβ
  set y := x ^ (N₁ + N₂ + 1) with hy
  have hy0 : y ≠ 0 := pow_ne_zero _ hx0
  have hy₁ : O₁.valuation y < O₁.valuation δ := by
    rw [hy, map_pow]
    exact (pow_le_pow_right_of_le_one' hx₁.le (by omega)).trans_lt hN₁
  have hy₁' : O₁.valuation y < 1 := by
    rw [hy, map_pow]
    exact pow_lt_one₀ zero_le hx₁ (by omega)
  have hy₂ : O₂.valuation y⁻¹ < O₂.valuation β := by
    rw [hy, ← inv_pow, map_pow]
    exact (pow_le_pow_right_of_le_one' hx₂.le (by omega)).trans_lt hN₂
  have hy₂' : 1 < O₂.valuation y := by
    have : O₂.valuation y⁻¹ < 1 := by
      rw [hy, ← inv_pow, map_pow]
      exact pow_lt_one₀ zero_le hx₂ (by omega)
    rwa [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy0))] at this
  have h1y₁ : O₁.valuation (1 + y) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  have h1y₂ : O₂.valuation (1 + y) = O₂.valuation y :=
    Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])
  have h1y0 : 1 + y ≠ 0 := by
    intro h
    rw [h, map_zero] at h1y₁
    exact zero_ne_one h1y₁
  refine ⟨(1 + y)⁻¹, ?_, ?_⟩
  · have : 1 - (1 + y)⁻¹ = y * (1 + y)⁻¹ := by field_simp; ring
    rw [this, map_mul, map_inv₀, h1y₁, inv_one, mul_one]
    exact hy₁
  · rw [map_inv₀, h1y₂, ← map_inv₀]
    exact hy₂

end Independence

end TemperedFundamentalGroups
