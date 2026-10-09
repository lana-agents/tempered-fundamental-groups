/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Apply

/-!
# The ramified quadratic extension `K(√ϖ)` (Blueprint §10.3.8, `v(q) = 1`, step B1)

Let `O ⊆ K` be a complete discrete valuation ring (characteristic `0`) with uniformizer `ϖ`.

* `RamifiedQuadratic.sqrtϖ`: a square root of `ϖ` in `K̄`;
* `RamifiedQuadratic.K'`: the intermediate field `K(√ϖ)`, of degree `2` (`finrank_K'`);
* `RamifiedQuadratic.O'`: its valuation ring `O_{K'}` (`W10Apply.OE`), a DVR over `O`;
* `RamifiedQuadratic.irreducible_sqrt`: `√ϖ` is a uniformizer of `O'`: every element of the
  maximal ideal has norm at most `‖ϖ‖^{1/2} = ‖√ϖ‖` (spectral norm `= ‖N(x)‖^{1/deg}`).
-/

universe u

open Polynomial IsLocalRing

namespace TemperedFundamentalGroups.RamifiedQuadratic

open SemistableReduction.W10Apply

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)

local notation "C" => AlgebraicClosure K

variable (ϖ) in
/-- The polynomial `X² - ϖ`. -/
abbrev P : K[X] := X ^ 2 - Polynomial.C (ϖ : K)

lemma natDegree_P : (P ϖ).natDegree = 2 := by
  rw [P, natDegree_sub_C, natDegree_X_pow]

lemma monic_P : (P ϖ).Monic := by
  rw [P]; exact monic_X_pow_sub_C _ two_ne_zero

include hϖ in
/-- `X² - ϖ` is irreducible: a root would be an integral square root of `ϖ`. -/
lemma irreducible_P : Irreducible (P ϖ) := by
  have h2 : (P ϖ).natDegree = 2 := natDegree_P
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [h2]; decide) fun r hr ↦ ?_
  rw [IsRoot, P, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  -- `r ∈ O`
  have hrO : r ∈ O := by
    rcases O.mem_or_inv_mem r with h | h
    · exact h
    · have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at hr
        exact hϖ.ne_zero (Subtype.ext hr.symm)
      have hϖO : ((ϖ : K))⁻¹ ∈ O := by
        rw [← hr, ← inv_pow]; exact pow_mem h 2
      exact absurd (IsUnit.of_mul_eq_one (b := ⟨_, hϖO⟩)
        (Subtype.ext (mul_inv_cancel₀ fun h0 ↦ hϖ.ne_zero (Subtype.ext h0)))) hϖ.not_isUnit
  have e : (⟨r, hrO⟩ : O) * ⟨r, hrO⟩ = ϖ := Subtype.ext (by rw [← hr]; push_cast; ring)
  rcases hϖ.isUnit_or_isUnit e.symm with h | h <;>
  · have := (h.mul h)
    rw [e] at this
    exact hϖ.not_isUnit this

variable (ϖ) in
/-- A square root of `ϖ` in `K̄`. -/
def sqrtϖ : C :=
  (IsAlgClosed.exists_root ((P ϖ).map (algebraMap K C))
    (by rw [degree_map, Ne, degree_eq_natDegree (monic_P (ϖ := ϖ)).ne_zero, natDegree_P]
        decide)).choose

lemma sqrtϖ_sq : sqrtϖ ϖ ^ 2 = algebraMap K C ϖ := by
  have h := (IsAlgClosed.exists_root ((P ϖ).map (algebraMap K C))
    (by rw [degree_map, Ne, degree_eq_natDegree (monic_P (ϖ := ϖ)).ne_zero, natDegree_P]
        decide)).choose_spec
  rw [IsRoot, eval_map, ← aeval_def, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

lemma aeval_sqrtϖ : aeval (sqrtϖ ϖ) (P ϖ) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, sqrtϖ_sq, sub_self]

include hϖ in
lemma minpoly_sqrtϖ : minpoly K (sqrtϖ ϖ) = P ϖ :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_P hϖ) aeval_sqrtϖ monic_P).symm

variable (ϖ) in
/-- **`K' = K(√ϖ)`.** -/
def K' : IntermediateField K C := IntermediateField.adjoin K {sqrtϖ ϖ}

instance : FiniteDimensional K (K' ϖ) :=
  IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) (sqrtϖ ϖ))

include hϖ in
lemma finrank_K' : Module.finrank K (K' ϖ) = 2 := by
  rw [K', IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := K) (sqrtϖ ϖ)),
    minpoly_sqrtϖ hϖ, natDegree_P]

variable (ϖ) in
/-- `√ϖ ∈ K'`. -/
def s : K' ϖ := ⟨sqrtϖ ϖ, IntermediateField.mem_adjoin_simple_self K _⟩

lemma isIntegral_s : IsIntegral O (s ϖ) := by
  refine ⟨X ^ 2 - Polynomial.C ϖ, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  apply (algebraMap (K' ϖ) C).injective
  rw [map_zero, ← aeval_def, ← aeval_algebraMap_apply, map_sub, map_pow, aeval_X, aeval_C]
  change sqrtϖ ϖ ^ 2 - _ = 0
  rw [sqrtϖ_sq, sub_eq_zero]
  rfl

variable [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

variable (ϖ) in
/-- **The valuation ring `O' = O_{K'}`.** -/
abbrev O' : ValuationSubring (K' ϖ) := OE O (K' ϖ)

lemma s_mem : s ϖ ∈ O' ϖ := (mem_OE_iff O _ _).2 (isIntegral_s)

variable (ϖ) in
/-- `√ϖ` as an element of `O'`. -/
def sO : O' ϖ := ⟨s ϖ, s_mem⟩

/-! ### Norms -/

section Norm

open DVRNorm

lemma norm_sqrtϖ :
    letI := normedField O; letI := normedFieldAlgCl O;
    ‖sqrtϖ ϖ‖ = ‖(ϖ : K)‖ ^ (1 / 2 : ℝ) := by
  letI := normedField O
  letI := normedFieldAlgCl O
  have h : ‖sqrtϖ ϖ‖ ^ 2 = ‖(ϖ : K)‖ := by
    rw [← norm_pow, sqrtϖ_sq, DVRNorm.norm_algebraMap O]
  rw [← h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

include hϖ in
/-- **Elements of the maximal ideal of `O'` have norm at most `‖ϖ‖^{1/2}`.** -/
lemma norm_le_of_lt_one (x : K' ϖ) (hx0 : x ≠ 0)
    (hx : letI := normedFieldAlgCl O; ‖(x : C)‖ < 1) :
    letI := normedField O; letI := normedFieldAlgCl O;
    ‖(x : C)‖ ≤ ‖(ϖ : K)‖ ^ (1 / 2 : ℝ) := by
  letI := normedField O
  haveI := isUltrametricDist O
  haveI := completeSpace O
  letI := normedFieldAlgCl O
  have hint : IsIntegral K (x : C) := Algebra.IsIntegral.isIntegral _
  set d := (minpoly K (x : C)).natDegree
  have hd1 : 1 ≤ d := minpoly.natDegree_pos hint
  have hd2 : d ≤ 2 := by
    have := minpoly.natDegree_le (A := K) x
    rw [finrank_K' hϖ] at this
    have e : minpoly K (x : C) = minpoly K x :=
      minpoly.algebraMap_eq (algebraMap (K' ϖ) C).injective x
    change (minpoly K (x : C)).natDegree ≤ 2
    rwa [e]
  have hspec : ‖(x : C)‖ = ‖(minpoly K (x : C)).coeff 0‖ ^ (1 / d : ℝ) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := K) C (x : C)
  set a := (minpoly K (x : C)).coeff 0
  have ha0 : a ≠ 0 := by
    have := minpoly.coeff_zero_ne_zero hint (by
      intro h; exact hx0 (Subtype.ext h))
    exact this
  have hd0 : (0 : ℝ) < 1 / d := by positivity
  have ha1 : ‖a‖ < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ ‖a‖ ^ (1 / d : ℝ) := Real.one_le_rpow h hd0.le
    rw [← hspec] at this
    exact absurd hx (not_lt.2 this)
  obtain ⟨haO, ham⟩ := (norm_lt_one_iff O a).1 ha1
  have haϖ : ‖a‖ ≤ ‖(ϖ : K)‖ := by
    have := (mem_maximalIdeal_pow_iff hϖ ⟨a, haO⟩ 1).1 (by rw [pow_one]; exact ham)
    simpa using this
  have hϖ1 : ‖(ϖ : K)‖ < 1 := norm_uniformizer_lt_one hϖ
  have hϖ0 : 0 < ‖(ϖ : K)‖ := norm_uniformizer_pos hϖ
  rw [hspec]
  calc ‖a‖ ^ (1 / d : ℝ) ≤ ‖(ϖ : K)‖ ^ (1 / d : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) haϖ hd0.le
    _ ≤ ‖(ϖ : K)‖ ^ (1 / 2 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_ge hϖ0 hϖ1.le ?_
        have : (d : ℝ) ≤ 2 := by exact_mod_cast hd2
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith

end Norm

variable [CharZero K]

include hϖ in
/-- **`√ϖ` is a uniformizer of `O'`.** -/
theorem irreducible_sqrt : Irreducible (sO ϖ) := by
  letI := DVRNorm.normedField O
  letI := DVRNorm.normedFieldAlgCl O
  haveI : IsDiscreteValuationRing (O' ϖ) := isDiscreteValuationRing_OE O _
  have hs0 : sO ϖ ≠ 0 := by
    intro h
    have h' : sqrtϖ ϖ = 0 := congrArg (fun z : O' ϖ ↦ ((z : K' ϖ) : C)) h
    have := sqrtϖ_sq (ϖ := ϖ)
    rw [h', zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap K C).injective] at this
    exact hϖ.ne_zero (Subtype.ext this)
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible (O' ϖ)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπ'
  have hnorm : ∀ z : O' ϖ, ‖(((z : K' ϖ)) : C)‖ ≤ 1 := fun z ↦ (mem_OE_iff_norm O _ _).1 z.2
  have hunit : ‖(((u : O' ϖ) : K' ϖ) : C)‖ = 1 := by
    refine le_antisymm (hnorm _) ?_
    have h1 := hnorm ((u⁻¹ : (O' ϖ)ˣ) : O' ϖ)
    have h2 : (((u : O' ϖ) : K' ϖ) : C) * ((((u⁻¹ : (O' ϖ)ˣ) : O' ϖ) : K' ϖ) : C) = 1 := by
      exact_mod_cast congrArg (fun z : O' ϖ ↦ (((z : K' ϖ)) : C)) u.mul_inv
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one] at h3
    by_contra hlt
    push Not at hlt
    have : ‖(((u : O' ϖ) : K' ϖ) : C)‖ * ‖((((u⁻¹ : (O' ϖ)ˣ) : O' ϖ) : K' ϖ) : C)‖ < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h1
    linarith
  have hsn : ‖sqrtϖ ϖ‖ = ‖(ϖ : K)‖ ^ (1 / 2 : ℝ) := norm_sqrtϖ
  have hϖ1 : ‖(ϖ : K)‖ < 1 := DVRNorm.norm_uniformizer_lt_one hϖ
  have hϖ0 : 0 < ‖(ϖ : K)‖ := DVRNorm.norm_uniformizer_pos hϖ
  have hπ'0 : (((π' : O' ϖ) : K' ϖ) : C) ≠ 0 := by
    intro h
    exact hπ'.ne_zero (Subtype.ext (Subtype.ext h))
  have hπ'1 : ‖(((π' : O' ϖ) : K' ϖ) : C)‖ < 1 := by
    refine lt_of_le_of_ne (hnorm _) fun h ↦ hπ'.not_isUnit ?_
    -- norm one: the inverse is integral
    have hinv : ((π' : K' ϖ))⁻¹ ∈ O' ϖ := by
      rw [mem_OE_iff_norm]
      have : (((π' : O' ϖ) : K' ϖ) : C)⁻¹ = (((π' : K' ϖ))⁻¹ : K' ϖ) := by simp
      rw [← this, norm_inv, h, inv_one]
    exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩)
      (Subtype.ext (mul_inv_cancel₀ fun h0 ↦ hπ'0 (by rw [h0]; rfl)))
  have hπ'le := norm_le_of_lt_one hϖ _ (fun h0 ↦ hπ'0 (by rw [h0]; rfl)) hπ'1
  have hval : ‖sqrtϖ ϖ‖ = ‖(((π' : O' ϖ) : K' ϖ) : C)‖ ^ n := by
    have := congrArg (fun z : O' ϖ ↦ ‖(((z : K' ϖ)) : C)‖) hu
    change ‖sqrtϖ ϖ‖ = _
    rw [show sqrtϖ ϖ = (((sO ϖ : O' ϖ) : K' ϖ) : C) from rfl, this]
    push_cast
    rw [norm_mul, norm_pow, hunit, one_mul]
  -- `n = 1`
  have hn : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, hsn] at hval
      have : ‖(ϖ : K)‖ ^ (1 / 2 : ℝ) < 1 := Real.rpow_lt_one hϖ0.le hϖ1 (by norm_num)
      linarith
    · rfl
    · exfalso
      have hp0 : 0 ≤ ‖(((π' : O' ϖ) : K' ϖ) : C)‖ := norm_nonneg _
      have h1 : ‖(((π' : O' ϖ) : K' ϖ) : C)‖ ^ (n + 2) ≤
          ‖(((π' : O' ϖ) : K' ϖ) : C)‖ ^ 2 :=
        pow_le_pow_of_le_one hp0 hπ'1.le (by omega)
      have h2 : ‖(((π' : O' ϖ) : K' ϖ) : C)‖ ^ 2 ≤ (‖(ϖ : K)‖ ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hp0 hπ'le 2
      have h3 : (‖(ϖ : K)‖ ^ (1 / 2 : ℝ)) ^ 2 = ‖(ϖ : K)‖ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hϖ0.le]; norm_num
      have h4 : ‖(ϖ : K)‖ < ‖(ϖ : K)‖ ^ (1 / 2 : ℝ) := by
        have := Real.rpow_lt_rpow_of_exponent_gt hϖ0 hϖ1 (show (1 / 2 : ℝ) < 1 by norm_num)
        rwa [Real.rpow_one] at this
      rw [← hval, hsn] at h1
      linarith
  subst hn
  rw [pow_one] at hu
  rw [hu]
  exact (irreducible_isUnit_mul u.isUnit).2 hπ'

end

end TemperedFundamentalGroups.RamifiedQuadratic
