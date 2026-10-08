/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Splitting
import TemperedFundamentalGroups.SemistableReduction.VertexDescent
import TemperedFundamentalGroups.SemistableReduction.GaussFibre

/-!
# Residues and values above a type-4 point

Blueprint §9.12, leaf T4, part (G). Let `ξ` be a valuation of `C(x)` extending the norm of the
algebraically closed `C` without minimal radius (`Splitting.IsTypeFour`: a type-4 point or a
point of `Ĉ ∖ C`).

* `IsTypeFour.exists_sub_lt` (**every nonzero `φ ∈ C(x)` is a constant up to a small error**):
  `ξ(φ - γ) < |γ|` for some `γ ∈ C^×`; for `X - α` take `γ = b - α` with `b` deeper than `α`,
  and the property is multiplicative. Hence the value group of `ξ` is `|C^×|` and its residue
  field is `k`;
* `valuation_aeval_eq_gauss`: if `w(y - c) = max(1, |c|)` for all `c ∈ C`, then `w(Q(y))` is the
  Gauss norm of `Q` (factor `Q` over the algebraically closed `C`);
* **`exists_sub_lt_one`** (the residue field of a finite extension of `(C(x), ξ)` is `k`): for
  `w ∣ ξ` on a finite extension `L` and `w(y) ≤ 1` there is `c ∈ C` with `w(y - c) < 1`. Otherwise
  `w` is the Gauss norm on `C[y]`; but `ȳ` is algebraic over the residue field `k` of `ξ`
  (`not_isResidueTranscendental_of_isAlgebraic`), so a polynomial over `C` with a unit
  coefficient has small value at `y`;
* **`exists_eq_nnnorm`** (the value group of a finite extension of `(C(x), ξ)` is `|C^×|`).
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open GaussLimit Splitting

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

/-! ### Rational functions at a type-4 point -/

section Base

variable {ξ : Valuation (RatFunc C) ℝ≥0}

/-- `φ` is the nonzero constant `γ` up to an error smaller than `|γ|`. -/
def NearConst (ξ : Valuation (RatFunc C) ℝ≥0) (φ : RatFunc C) : Prop :=
  ∃ γ : C, γ ≠ 0 ∧ ξ (φ - algebraMap C (RatFunc C) γ) < ‖γ‖₊

omit [IsAlgClosed C] in
lemma NearConst.val_eq (hξ : IsTypeFour ξ) {φ : RatFunc C} {γ : C}
    (h : ξ (φ - algebraMap C (RatFunc C) γ) < ‖γ‖₊) : ξ φ = ‖γ‖₊ := by
  have hc : ξ (algebraMap C (RatFunc C) γ) = ‖γ‖₊ := by
    rw [hξ.map_C, NormedField.valuation_apply]
  rw [show φ = (φ - algebraMap C (RatFunc C) γ) + algebraMap C (RatFunc C) γ by ring,
    Valuation.map_add_eq_of_lt_right _ (by rwa [hc]), hc]

omit [IsAlgClosed C] in
lemma NearConst.mul (hξ : IsTypeFour ξ) {φ ψ : RatFunc C} (hφ : NearConst ξ φ)
    (hψ : NearConst ξ ψ) : NearConst ξ (φ * ψ) := by
  obtain ⟨γ, hγ, h₁⟩ := hφ
  obtain ⟨δ, hδ, h₂⟩ := hψ
  have hc : ∀ c : C, ξ (algebraMap C (RatFunc C) c) = ‖c‖₊ := fun c ↦ by
    rw [hξ.map_C, NormedField.valuation_apply]
  refine ⟨γ * δ, mul_ne_zero hγ hδ, ?_⟩
  rw [show φ * ψ - algebraMap C (RatFunc C) (γ * δ) =
      φ * (ψ - algebraMap C (RatFunc C) δ) + algebraMap C (RatFunc C) δ *
        (φ - algebraMap C (RatFunc C) γ) by rw [map_mul]; ring, nnnorm_mul]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_) <;> rw [map_mul]
  · rw [NearConst.val_eq hξ h₁]
    exact mul_lt_mul_of_pos_left h₂ (nnnorm_pos.2 hγ)
  · rw [hc, mul_comm ‖γ‖₊]
    exact mul_lt_mul_of_pos_left h₁ (nnnorm_pos.2 hδ)

omit [IsAlgClosed C] in
lemma NearConst.inv (hξ : IsTypeFour ξ) {φ : RatFunc C} (hφ : NearConst ξ φ) :
    NearConst ξ φ⁻¹ := by
  obtain ⟨γ, hγ, h⟩ := hφ
  have hφv := NearConst.val_eq hξ h
  have hφ0 : φ ≠ 0 := fun h0 ↦ by
    rw [h0, map_zero] at hφv
    exact (nnnorm_pos.2 hγ).ne hφv
  have hc : ∀ c : C, ξ (algebraMap C (RatFunc C) c) = ‖c‖₊ := fun c ↦ by
    rw [hξ.map_C, NormedField.valuation_apply]
  refine ⟨γ⁻¹, inv_ne_zero hγ, ?_⟩
  have hγ' : algebraMap C (RatFunc C) γ ≠ 0 := (_root_.map_ne_zero _).2 hγ
  rw [show φ⁻¹ - algebraMap C (RatFunc C) γ⁻¹ =
      -(φ - algebraMap C (RatFunc C) γ) * (φ⁻¹ * (algebraMap C (RatFunc C) γ)⁻¹) by
    rw [map_inv₀]; field_simp; ring]
  rw [map_mul, Valuation.map_neg, map_mul, map_inv₀, map_inv₀, hφv, hc, nnnorm_inv]
  calc ξ (φ - algebraMap C (RatFunc C) γ) * (‖γ‖₊⁻¹ * ‖γ‖₊⁻¹)
      < ‖γ‖₊ * (‖γ‖₊⁻¹ * ‖γ‖₊⁻¹) :=
        mul_lt_mul_of_pos_right h (mul_pos (inv_pos.2 (nnnorm_pos.2 hγ))
          (inv_pos.2 (nnnorm_pos.2 hγ)))
    _ = ‖γ‖₊⁻¹ := by rw [← mul_assoc, mul_inv_cancel₀ (nnnorm_pos.2 hγ).ne', one_mul]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma nearConst_C {c : C} (hc : c ≠ 0) :
    NearConst ξ (algebraMap C (RatFunc C) c) :=
  ⟨c, hc, by rw [sub_self, map_zero]; exact nnnorm_pos.2 hc⟩

omit [IsAlgClosed C] in
lemma nearConst_X_sub_C (hξ : IsTypeFour ξ) (α : C) :
    NearConst ξ (algebraMap C[X] (RatFunc C) (X - Polynomial.C α)) := by
  obtain ⟨b, hb⟩ := hξ.no_min α
  have hrad := radius_eq_nnnorm hξ hb
  have hne := sub_ne_zero_of_radius_lt hξ hb
  refine ⟨b - α, fun h0 ↦ hne (by rw [← neg_sub, h0, neg_zero]), ?_⟩
  rw [show algebraMap C[X] (RatFunc C) (X - Polynomial.C α) - algebraMap C (RatFunc C) (b - α) =
      algebraMap C[X] (RatFunc C) (X - Polynomial.C b) by
    rw [map_sub, map_sub, map_sub, ratFunc_algebraMap_C, ratFunc_algebraMap_C]; ring]
  change radius ξ b < _
  rw [← hrad]
  exact hb

/-- **Every nonzero rational function is a constant up to a small error** at a type-4 point. -/
theorem _root_.SemistableReduction.Splitting.IsTypeFour.nearConst (hξ : IsTypeFour ξ)
    {φ : RatFunc C} (hφ : φ ≠ 0) :
    NearConst ξ φ := by
  have hpoly : ∀ P : C[X], P ≠ 0 → NearConst ξ (algebraMap C[X] (RatFunc C) P) := by
    intro P hP
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := P)),
      map_mul, map_multiset_prod, ratFunc_algebraMap_C]
    refine NearConst.mul hξ (nearConst_C (leadingCoeff_ne_zero.2 hP)) ?_
    induction P.roots using Multiset.induction_on with
    | empty => simpa using nearConst_C (ξ := ξ) (one_ne_zero (α := C))
    | cons α s ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons]
      exact NearConst.mul hξ (nearConst_X_sub_C hξ α) ih
  rw [← RatFunc.num_div_denom φ, div_eq_mul_inv]
  exact NearConst.mul hξ (hpoly _ (RatFunc.num_ne_zero hφ))
    (NearConst.inv hξ (hpoly _ (RatFunc.denom_ne_zero φ)))

/-- The values of a type-4 point are norms of `C`. -/
theorem _root_.SemistableReduction.Splitting.IsTypeFour.exists_eq_nnnorm (hξ : IsTypeFour ξ)
    {φ : RatFunc C} (hφ : φ ≠ 0) :
    ∃ γ : C, γ ≠ 0 ∧ ξ φ = ‖γ‖₊ := by
  obtain ⟨γ, hγ, h⟩ := hξ.nearConst hφ
  exact ⟨γ, hγ, NearConst.val_eq hξ h⟩

/-- The residue field of a type-4 point is `k`: an element of value `≤ 1` is a constant modulo
the maximal ideal. -/
theorem _root_.SemistableReduction.Splitting.IsTypeFour.exists_sub_lt_one (hξ : IsTypeFour ξ)
    {φ : RatFunc C} (hφ : ξ φ ≤ 1) :
    ∃ c : C, ‖c‖ ≤ 1 ∧ ξ (φ - algebraMap C (RatFunc C) c) < 1 := by
  by_cases h1 : ξ φ < 1
  · exact ⟨0, by simp, by rwa [map_zero, sub_zero]⟩
  have hφ1 : ξ φ = 1 := le_antisymm hφ (not_lt.1 h1)
  have hφ0 : φ ≠ 0 := fun h ↦ by rw [h, map_zero] at hφ1; exact zero_ne_one hφ1
  obtain ⟨γ, hγ, h⟩ := hξ.nearConst hφ0
  have := NearConst.val_eq hξ h
  rw [hφ1] at this
  refine ⟨γ, ?_, by rw [this]; exact h⟩
  rw [← coe_nnnorm, ← this, NNReal.coe_one]

end Base

/-! ### Finite extensions -/

section Ext

variable {L : Type*} [Field L] [Algebra (RatFunc C) L] [Algebra C L]
  [IsScalarTower C (RatFunc C) L]

omit [Algebra (RatFunc C) L] [IsScalarTower C (RatFunc C) L] in
/-- If `w(y - c) = max(1, |c|)` for all `c ∈ C`, then `w(Q(y))` is the Gauss norm of `Q`. -/
theorem valuation_aeval_eq_gauss {w : Valuation L ℝ≥0} (hC : ∀ c : C, w (algebraMap C L c) = ‖c‖₊)
    {y : L} (hy : ∀ c : C, w (y - algebraMap C L c) = max 1 ‖c‖₊) (Q : C[X]) :
    w (aeval y Q) = Gauss.sup (NormedField.valuation (K := C)) 1 Q := by
  rw [← GaussFibre.gauss1_algebraMap]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := Q))]
  conv_rhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := Q))]
  simp only [map_mul, map_multiset_prod, Multiset.map_map, aeval_C, ratFunc_algebraMap_C]
  congr 1
  · rw [hC, GaussFibre.gauss1_algebraMap_C]
  · congr 1
    refine Multiset.map_congr rfl fun α _ ↦ ?_
    simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]
    rw [hy, ← map_sub, gaussRat_algebraMap, gauss_X_sub_C, zero_sub,
      Valuation.map_neg, NormedField.valuation_apply, max_comm]
    rfl

variable [FiniteDimensional (RatFunc C) L] {ξ : Valuation (RatFunc C) ℝ≥0}

/-- **The residue field above a type-4 point is `k`.** For a valuation `w` of a finite extension
`L` of `C(x)` over a type-4 point `ξ`, every `y` with `w(y) ≤ 1` is congruent to a constant. -/
theorem exists_sub_lt_one (hξ : IsTypeFour ξ) {w : Valuation L ℝ≥0}
    (hw : w.comap (algebraMap (RatFunc C) L) = ξ) {y : L} (hy : w y ≤ 1) :
    ∃ c : C, ‖c‖ ≤ 1 ∧ w (y - algebraMap C L c) < 1 := by
  classical
  have hwξ : ∀ φ, w (algebraMap (RatFunc C) L φ) = ξ φ := fun φ ↦ by
    rw [← Valuation.comap_apply, hw]
  have hC : ∀ c : C, w (algebraMap C L c) = ‖c‖₊ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) L, hwξ, hξ.map_C,
      NormedField.valuation_apply]
  by_contra! H
  -- `w` is the Gauss norm on `C[y]`
  have hlin : ∀ c : C, w (y - algebraMap C L c) = max 1 ‖c‖₊ := by
    intro c
    by_cases hc : ‖c‖ ≤ 1
    · have h1 := H c hc
      have hc' : ‖c‖₊ ≤ 1 := by exact_mod_cast hc
      rw [max_eq_left hc']
      refine le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hy (by rw [hC]; exact hc')))
        h1
    · have hc' : 1 < ‖c‖₊ := by exact_mod_cast not_le.1 hc
      rw [max_eq_right hc'.le, sub_eq_add_neg, ← map_neg, Valuation.map_add_eq_of_lt_right]
      · rw [hC, nnnorm_neg]
      · rw [hC, nnnorm_neg]; exact hy.trans_lt hc'
  have hgauss := valuation_aeval_eq_gauss hC hlin
  -- the residue of `y` is algebraic over the residue field of `ξ`
  set O := ξ.valuationSubring
  set V := w.valuationSubring
  have hyV : y ∈ V := hy
  have hnot := not_isResidueTranscendental_of_isAlgebraic (O := O) (V := V)
    (Algebra.IsAlgebraic.isAlgebraic (R := RatFunc C) y)
  simp only [IsResidueTranscendental, not_and, not_forall] at hnot
  obtain ⟨P, hP0, hPv⟩ := hnot hyV
  -- replace the coefficients by constants
  have hcoef : ∀ i, ∃ c : C, ‖c‖ ≤ 1 ∧
      ξ ((P.coeff i : RatFunc C) - algebraMap C (RatFunc C) c) < 1 ∧
      (ξ (P.coeff i : RatFunc C) = 1 → ‖c‖ = 1) := by
    intro i
    obtain ⟨c, hc1, hc⟩ := hξ.exists_sub_lt_one (P.coeff i).2
    refine ⟨c, hc1, hc, fun h1 ↦ ?_⟩
    have : ξ (algebraMap C (RatFunc C) c) = 1 := by
      rw [show algebraMap C (RatFunc C) c = (P.coeff i : RatFunc C) -
        ((P.coeff i : RatFunc C) - algebraMap C (RatFunc C) c) by ring,
        Valuation.map_sub_eq_of_lt_left _ (by rwa [h1]), h1]
    rw [hξ.map_C, NormedField.valuation_apply] at this
    rw [← coe_nnnorm, this, NNReal.coe_one]
  choose c hc1 hcs hcu using hcoef
  set Q : C[X] := ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial i (c i)
  have hQcoef : ∀ i, Q.coeff i = if i ∈ Finset.range (P.natDegree + 1) then c i else 0 := by
    intro i
    simp only [Q, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_ite_eq']
  -- `w(P(y) - Q(y)) < 1`
  have hdiff : w (aeval y (P.map (algebraMap O (RatFunc C))) - aeval y Q) < 1 := by
    rw [aeval_eq_sum_range' (n := P.natDegree + 1)
        (natDegree_map_le.trans_lt (Nat.lt_succ_self _)),
      aeval_eq_sum_range' (n := P.natDegree + 1) (by
        refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i hi ↦
          (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) ?_
        omega), ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi ↦ ?_
    rw [coeff_map, hQcoef, if_pos hi, Algebra.smul_def, Algebra.smul_def, ← sub_mul, map_mul,
      map_pow]
    refine mul_lt_one_of_nonneg_of_lt_one_left zero_le ?_ (pow_le_one' hy _)
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) L, ← map_sub, hwξ]
    exact hcs i
  have hPlt : w (aeval y (P.map (algebraMap O (RatFunc C)))) < 1 := by
    have hmem : aeval y (P.map (algebraMap O (RatFunc C))) ∈ V := by
      rw [aeval_eq_sum_range]
      refine Subring.sum_mem _ fun i _ ↦ ?_
      rw [coeff_map, Algebra.smul_def]
      refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hyV _)
      change w _ ≤ 1
      rw [hwξ]
      exact (P.coeff i).2
    have hle : V.valuation (aeval y (P.map (algebraMap O (RatFunc C)))) < 1 :=
      lt_of_le_of_ne ((ValuationSubring.valuation_le_one_iff _ _).2 hmem) hPv
    exact (Valuation.isEquiv_valuation_valuationSubring w).lt_one_iff_lt_one.2 hle
  have hQlt : w (aeval y Q) < 1 := by
    rw [show aeval y Q = aeval y (P.map (algebraMap O (RatFunc C))) -
      (aeval y (P.map (algebraMap O (RatFunc C))) - aeval y Q) by ring]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hPlt hdiff)
  -- but `Q` has a unit coefficient
  obtain ⟨i, hi⟩ : ∃ i, IsLocalRing.residue O (P.coeff i) ≠ 0 := by
    by_contra! h0
    exact hP0 (Polynomial.ext fun i ↦ by rw [coeff_map, h0 i, coeff_zero])
  have hξi : ξ (P.coeff i : RatFunc C) = 1 := by
    have hu : IsUnit (P.coeff i) := by
      by_contra h
      exact hi ((IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
    exact (Valuation.isEquiv_valuation_valuationSubring ξ).eq_one_iff_eq_one.2
      ((ValuationSubring.valuation_eq_one_iff O _).1 hu)
  have hiP : i ≤ P.natDegree := by
    by_contra hlt
    rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hlt), map_zero] at hi
    exact hi rfl
  have hsup : 1 ≤ Gauss.sup (NormedField.valuation (K := C)) 1 Q := by
    refine le_trans (le_of_eq ?_) (Gauss.term_le_sup _ i)
    simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply,
      hQcoef, if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hiP))]
    have := hcu i hξi
    ext
    simp [this]
  rw [hgauss] at hQlt
  exact absurd hQlt (not_lt.2 hsup)

omit [Algebra C L] [IsScalarTower C (RatFunc C) L] in
/-- **The value group above a type-4 point is `|C^×|`.** -/
theorem exists_eq_nnnorm (hξ : IsTypeFour ξ) {w : Valuation L ℝ≥0}
    (hw : w.comap (algebraMap (RatFunc C) L) = ξ) {y : L} (hy : y ≠ 0) :
    ∃ γ : C, γ ≠ 0 ∧ w y = ‖γ‖₊ := by
  obtain ⟨n, hn, φ, hφ, h⟩ := FundamentalInequality.exists_pow_valuation_eq w
    (Algebra.IsIntegral.isIntegral (R := RatFunc C) y) hy
  obtain ⟨γ, hγ, hφγ⟩ := hξ.exists_eq_nnnorm hφ
  rw [← Valuation.comap_apply, hw, hφγ] at h
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq γ hn
  refine ⟨δ, fun h0 ↦ hγ (by rw [← hδ, h0, zero_pow hn.ne']), ?_⟩
  rw [← hδ, nnnorm_pow] at h
  exact (pow_left_inj₀ zero_le zero_le hn.ne').1 h

end Ext

end TypeFour

end SemistableReduction
