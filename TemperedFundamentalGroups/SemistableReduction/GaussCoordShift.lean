/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.UnfoldedVertex

/-!
# Shifting a Gauss coordinate by an integral constant

* `Gauss.sup_comp_X_add_C`: the Gauss norm of radius `1` is invariant under `X ↦ X + δ` for
  `v(δ) ≤ 1`;
* `IsGaussCoord.add_algebraMap`: `y + δ` is a Gauss coordinate of `w` if `y` is;
* `IsGaussCoord.valuationSubring_eq`: two valuations with a common Gauss coordinate have the same
  valuation ring;
* `gaussRat_valuationSubring_eq_of_le`: the Gauss valuation ring of a closed disc does not depend on
  the centre.
-/

universe u

open Polynomial

namespace SemistableReduction

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

namespace Gauss

lemma sup_sum_le {ι : Type*} (s : Finset ι) (f : ι → K[X]) {g : Γ₀}
    (h : ∀ i ∈ s, sup v 1 (f i) ≤ g) : sup v 1 (∑ i ∈ s, f i) ≤ g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sup_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (sup_add_le _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

lemma sup_X_add_C_le {δ : K} (hδ : v δ ≤ 1) : sup v 1 (X + C δ) ≤ 1 := by
  refine (sup_add_le _ _).trans (max_le ?_ ?_)
  · rw [sup_X, Units.val_one]
  · rw [sup_C]; exact hδ

lemma sup_pow_le {δ : K} (hδ : v δ ≤ 1) (i : ℕ) : sup v 1 ((X + C δ) ^ i) ≤ 1 := by
  induction i with
  | zero => rw [pow_zero, ← C_1, sup_C, map_one]
  | succ n ih =>
    rw [pow_succ]
    exact (sup_mul_le _ _).trans (mul_le_one' ih (sup_X_add_C_le hδ))

lemma sup_comp_le {δ : K} (hδ : v δ ≤ 1) (Q : K[X]) :
    sup v 1 (Q.comp (X + C δ)) ≤ sup v 1 Q := by
  rw [comp, eval₂_eq_sum, Polynomial.sum_def]
  refine sup_sum_le _ _ fun i _ ↦ ?_
  rw [sup_mul, sup_C]
  have h1 : sup v 1 ((X + C δ) ^ i) ≤ 1 := sup_pow_le hδ i
  calc v (Q.coeff i) * sup v 1 ((X + C δ) ^ i) ≤ v (Q.coeff i) * 1 := by gcongr
    _ = term v 1 Q i := by simp [term]
    _ ≤ sup v 1 Q := term_le_sup Q i

lemma sup_comp_X_add_C {δ : K} (hδ : v δ ≤ 1) (Q : K[X]) :
    sup v 1 (Q.comp (X + C δ)) = sup v 1 Q := by
  refine le_antisymm (sup_comp_le hδ Q) ?_
  have hδ' : v (-δ) ≤ 1 := by rw [Valuation.map_neg]; exact hδ
  have e : (Q.comp (X + C δ)).comp (X + C (-δ)) = Q := by
    rw [comp_assoc]
    simp only [add_comp, X_comp, C_comp, map_neg]
    rw [show X + -C δ + C δ = (X : K[X]) by ring, comp_X]
  calc sup v 1 Q = sup v 1 ((Q.comp (X + C δ)).comp (X + C (-δ))) := by rw [e]
    _ ≤ sup v 1 (Q.comp (X + C δ)) := sup_comp_le hδ' _

end Gauss

variable {F : Type*} [Field F] [Algebra K F] {w w' : Valuation F Γ₀} {y : F}

/-- **Shifting a Gauss coordinate by an integral constant.** -/
theorem IsGaussCoord.add_algebraMap (h : IsGaussCoord v w y) {δ : K} (hδ : v δ ≤ 1) :
    IsGaussCoord v w (y + algebraMap K F δ) := by
  refine ⟨fun Q ↦ ?_, ?_⟩
  · have e : aeval (y + algebraMap K F δ) Q = aeval y (Q.comp (X + C δ)) := by
      rw [aeval_comp]; simp
    rw [e, h.eq_sup, Gauss.sup_comp_X_add_C hδ]
  · refine eq_top_iff.2 fun z _ ↦ ?_
    have hy : y ∈ IntermediateField.adjoin K {y + algebraMap K F δ} := by
      have h1 : y + algebraMap K F δ ∈ IntermediateField.adjoin K {y + algebraMap K F δ} :=
        IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
      have h2 : algebraMap K F δ ∈ IntermediateField.adjoin K {y + algebraMap K F δ} :=
        IntermediateField.algebraMap_mem _ δ
      simpa using sub_mem h1 h2
    have hle : IntermediateField.adjoin K {y} ≤ IntermediateField.adjoin K {y + algebraMap K F δ} :=
      IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hy)
    exact hle (h.adjoin_eq_top ▸ IntermediateField.mem_top)

/-- **Two valuations with a common Gauss coordinate have the same valuation ring.** -/
theorem IsGaussCoord.valuationSubring_eq (h : IsGaussCoord v w y) (h' : IsGaussCoord v w' y) :
    w.valuationSubring = w'.valuationSubring :=
  h'.eq_of_isResidueTranscendental h.comap_valuationSubring h.isResidueTranscendental

open GaussTree in
/-- **The Gauss valuation ring of a closed disc does not depend on the centre.** -/
theorem gaussRat_valuationSubring_eq_of_le {a a' r : K} (hr : r ≠ 0) (h : v (a - a') ≤ v r) :
    (gaussRat v a (Units.mk0 (v r) ((v.ne_zero_iff).2 hr))).valuationSubring =
      (gaussRat v a' (Units.mk0 (v r) ((v.ne_zero_iff).2 hr))).valuationSubring := by
  have h₁ := isGaussCoord_coord (v := v) (a := a) hr
  have h₂ := isGaussCoord_coord (v := v) (a := a') hr
  have hδ : v (-((a - a') / r)) ≤ 1 := by
    rw [Valuation.map_neg, map_div₀]
    exact div_le_one_of_le₀ h zero_le
  have e : coord (RatFunc.X : RatFunc K) a r =
      coord (RatFunc.X : RatFunc K) a' r + algebraMap K (RatFunc K) (-((a - a') / r)) := by
    rw [← coord_sub_eq_coord (x := (RatFunc.X : RatFunc K)) (a := a) (a' := a') hr, map_neg,
      sub_eq_add_neg]
  have h₂' := h₂.add_algebraMap hδ
  rw [← e] at h₂'
  exact h₁.valuationSubring_eq h₂'

end SemistableReduction
