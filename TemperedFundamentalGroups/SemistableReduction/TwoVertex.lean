/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CurveDivisor
import TemperedFundamentalGroups.SemistableReduction.InnerVertex
import TemperedFundamentalGroups.SemistableReduction.GaussClassification
import TemperedFundamentalGroups.SemistableReduction.TypeTwo
import TemperedFundamentalGroups.SemistableReduction.GenusCount

/-!
# The two-vertex model `ℙ¹_t`, `t = x + c/x` (R5, preparation)

Blueprint §9.12, R5 / O12. For `0 < |c| < 1` the function `t = x + c/x` (`ζ c`) is a coordinate
of `C(x)` of degree `2` whose Gauss point has exactly the two extensions `w_{0,1}` and `w_{0,|c|}`
to `C(x)` (`gaussRat_comp_ψ`, `eq_or_eq_of_comap`); `x` is integral over `O_C[t]`
(`x² - t x + c = 0`), so the normalization of `ℙ¹_t` is the two-vertex model of the annulus
`|c| ≤ |x| ≤ 1`, whose `t`-chart is the node chart. The twist `TwoV c F'` (`F'` as a
`C(t)`-algebra, via `ψ c : C(t) → C(x)`) is again a finite extension of `C(X)`
(`instFiniteDimensional`), so S7⁺ (`GaussFibre.exists_genus_eq_sum_delta`) applies to it.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TwoVertex

open GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

variable (c : C)

/-- The coordinate `t = x + c/x` of the two-vertex model. -/
noncomputable def ζ : RatFunc C := RatFunc.X + algebraMap C (RatFunc C) c / RatFunc.X

/-- The Gauss value of a monic quadratic `X² + β X + γ` is `max(v γ, v β · r, r²)`. -/
lemma sup_quadratic (r : ℝ≥0ˣ) (β γ : C) :
    Gauss.sup ν r (X ^ 2 + Polynomial.C β * X + Polynomial.C γ) =
      max (max (ν γ) (ν β * r)) ((r : ℝ≥0) ^ 2) := by
  set p : C[X] := X ^ 2 + Polynomial.C β * X + Polynomial.C γ
  have h0 : p.coeff 0 = γ := by simp [p]
  have h1 : p.coeff 1 = β := by simp [p]
  have h2 : p.coeff 2 = 1 := by simp [p]
  have hn : ∀ i, 3 ≤ i → p.coeff i = 0 := fun i hi ↦ by
    simp only [p, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  refine le_antisymm (Gauss.sup_le_iff.2 fun i ↦ ?_) (max_le (max_le ?_ ?_) ?_)
  · rcases i with _ | _ | _ | i
    · simp [Gauss.term, h0]
    · simp [Gauss.term, h1]
    · simp [Gauss.term, h2]
    · simp [Gauss.term, hn (i + 3) (by omega)]
  · simpa [Gauss.term, h0] using Gauss.term_le_sup (v := ν) (r := r) p 0
  · simpa [Gauss.term, h1] using Gauss.term_le_sup (v := ν) (r := r) p 1
  · simpa [Gauss.term, h2] using Gauss.term_le_sup (v := ν) (r := r) p 2


section Hom

variable [IsAlgClosed C] {c}

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma ζ_notMem_range : ζ c ∉ (algebraMap C (RatFunc C)).range := by
  rintro ⟨b, hb⟩
  have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have h : algebraMap C[X] (RatFunc C) (X ^ 2 + Polynomial.C (-b) * X + Polynomial.C c) = 0 := by
    have : (RatFunc.X : RatFunc C) * (ζ c - algebraMap C (RatFunc C) b) = 0 := by
      rw [hb, sub_self, mul_zero]
    rw [ζ] at this
    rw [map_add, map_add, map_mul, map_pow, RatFunc.algebraMap_X, ratFunc_algebraMap_C,
      ratFunc_algebraMap_C, ← this, map_neg]
    field_simp
    ring
  rw [map_eq_zero_iff _ (IsFractionRing.injective C[X] (RatFunc C))] at h
  have := congrArg (coeff · 2) h
  simp at this

omit [IsUltrametricDist C] in
lemma ζ_transcendental : Transcendental C (ζ c) :=
  transcendental_of_notMem_range ζ_notMem_range

variable (c) in
/-- The algebra map `C(t) → C(x)`, `t ↦ x + c/x`. -/
noncomputable def ψ : RatFunc C →ₐ[C] RatFunc C :=
  RatFunc.liftAlgHom (aeval (ζ c))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((transcendental_iff_injective).1 ζ_transcendental))

omit [IsUltrametricDist C] in
lemma ψ_algebraMap (p : C[X]) : ψ c (algebraMap C[X] (RatFunc C) p) = aeval (ζ c) p := by
  have := RatFunc.liftAlgHom_apply_div (aeval (ζ c))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((transcendental_iff_injective).1 ζ_transcendental)) p 1
  simpa [ψ] using this

omit [IsUltrametricDist C] in
lemma ψ_X : ψ c RatFunc.X = ζ c := by simpa using ψ_algebraMap (c := c) Polynomial.X

/-- `w_{0,r} ∘ ψ = w_{0,1}` for `r = 1` and `r = |c|` (`0 < |c| ≤ 1`): the Gauss point of `t`
has the two extensions `w_{0,1}` and `w_{0,|c|}` to `C(x)`. -/
lemma gaussRat_comp_ψ (hc0 : c ≠ 0) (hc1 : ‖c‖ ≤ 1) {r : ℝ≥0ˣ}
    (hr : (r : ℝ≥0) = 1 ∨ (r : ℝ≥0) = ‖c‖₊) :
    (gaussRat ν 0 r).comap (ψ c).toRingHom = gauss1 C := by
  have hc1' : ‖c‖₊ ≤ 1 := by exact_mod_cast hc1
  refine valuation_ratFunc_ext_of_linear (fun b ↦ ?_) fun b ↦ ?_
  · simp only [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, gaussRat_algebraMap_C]
  · simp only [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [ψ_algebraMap, gauss1_algebraMap]
    have hq : aeval (ζ c) (X - Polynomial.C b) = algebraMap C[X] (RatFunc C)
        (X ^ 2 + Polynomial.C (-b) * X + Polynomial.C c) / RatFunc.X := by
      have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
      rw [map_sub, aeval_X, aeval_C, ζ]
      rw [map_add, map_add, map_mul, map_pow, RatFunc.algebraMap_X, ratFunc_algebraMap_C,
        ratFunc_algebraMap_C, map_neg]
      field_simp
      ring
    rw [hq, map_div₀, gaussRat_algebraMap, gauss_apply, taylor_zero, sup_quadratic,
      AnnulusUnit.gaussRat_X, sub_eq_add_neg, ← map_neg Polynomial.C, Gauss.sup_X_add_C]
    simp only [NormedField.valuation_apply, nnnorm_neg, Units.val_one]
    have hK0 : (0 : ℝ≥0) < ‖c‖₊ := by simpa using hc0
    rcases hr with hr | hr
    · rw [hr, div_one, one_pow, mul_one, max_comm (‖c‖₊) _, max_assoc,
        max_eq_right hc1']
    · rw [hr, div_eq_iff hK0.ne', max_mul_of_nonneg _ _ zero_le, one_mul]
      rw [max_eq_left (le_max_left _ _ |>.trans' ?_), max_comm, mul_comm]
      calc ‖c‖₊ ^ 2 = ‖c‖₊ * ‖c‖₊ := sq _
        _ ≤ 1 * ‖c‖₊ := mul_le_mul_of_nonneg_right hc1' zero_le
        _ = ‖c‖₊ := one_mul _


/-- A valuation `μ` of `C(x)` restricting to the Gauss point of `t = x + c/x` with `μ(x) = 1` is
`w_{0,1}`. -/
lemma eq_gauss1_of_comap {μ : Valuation (RatFunc C) ℝ≥0} (hc1 : ‖c‖ < 1)
    (hμ : μ.comap (ψ c).toRingHom = gauss1 C) (hX : μ RatFunc.X = 1) : μ = gauss1 C := by
  have hψ : ∀ φ, μ (ψ c φ) = gauss1 C φ := fun φ ↦ by
    rw [← hμ]; rfl
  have hC : ∀ b : C, μ (algebraMap C (RatFunc C) b) = ‖b‖₊ := fun b ↦ by
    have := hψ (algebraMap C (RatFunc C) b)
    rwa [AlgHom.commutes, gauss1_algebraMap_C] at this
  have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have hc' : ‖c‖₊ < 1 := by exact_mod_cast hc1
  refine valuation_ratFunc_ext_of_linear (fun b ↦ by rw [hC, gauss1_algebraMap_C]) fun b ↦ ?_
  rw [gauss1_algebraMap, sub_eq_add_neg, ← map_neg Polynomial.C, Gauss.sup_X_add_C,
    map_add, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
  simp only [NormedField.valuation_apply, nnnorm_neg, Units.val_one]
  rcases lt_trichotomy ‖b‖₊ 1 with hb | hb | hb
  · rw [max_eq_right hb.le,
      Valuation.map_add_eq_of_lt_left _ (by rw [hC, hX, nnnorm_neg]; exact hb),
      hX]
  · -- `|b| = 1`: compare with `ζ - (b + c/b)`
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    set β := b + c / b
    have hfac : ζ c - algebraMap C (RatFunc C) β = (RatFunc.X + algebraMap C (RatFunc C) (-b)) *
        (1 - algebraMap C (RatFunc C) (c / b) / RatFunc.X) := by
      have hb' : algebraMap C (RatFunc C) b ≠ 0 := by simpa using hb0
      simp only [ζ, β, map_add, map_div₀, map_neg]
      field_simp
      ring
    have hunit : μ (1 - algebraMap C (RatFunc C) (c / b) / RatFunc.X) = 1 := by
      have h : μ (-(algebraMap C (RatFunc C) (c / b) / RatFunc.X)) < μ 1 := by
        rw [Valuation.map_neg, map_div₀, hC, hX, div_one, map_one, nnnorm_div, hb, div_one]
        exact hc'
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ h, map_one]
    have hβ : μ (ζ c - algebraMap C (RatFunc C) β) = 1 := by
      have := hψ (RatFunc.X - algebraMap C (RatFunc C) β)
      rw [map_sub, ψ_X, AlgHom.commutes] at this
      rw [this, ← ratFunc_algebraMap_C, ← RatFunc.algebraMap_X, ← map_sub, gauss1_algebraMap,
        sub_eq_add_neg,
        ← map_neg Polynomial.C, Gauss.sup_X_add_C]
      simp only [NormedField.valuation_apply, nnnorm_neg, Units.val_one]
      have : ‖β‖₊ ≤ 1 := by
        simp only [β]
        refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le hb.le ?_)
        rw [nnnorm_div, hb, div_one]; exact hc'.le
      exact max_eq_right this
    rw [hfac, map_mul, hunit, mul_one] at hβ
    rw [hβ, hb, max_self]
  · rw [max_eq_left hb.le, add_comm,
      Valuation.map_add_eq_of_lt_left _ (by rw [hC, hX, nnnorm_neg]; exact hb),
      hC, nnnorm_neg]


omit [IsUltrametricDist C] in
lemma inv_ψ (hc0 : c ≠ 0) (φ : RatFunc C) : GaussTube.inv hc0 (ψ c φ) = ψ c φ := by
  have hp (p : C[X]) : GaussTube.inv hc0 (ψ c (algebraMap C[X] (RatFunc C) p)) =
      ψ c (algebraMap C[X] (RatFunc C) p) := by
    have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
    have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
    have hζ' : (GaussTube.inv hc0).toAlgHom (ζ c) = ζ c := by
      change GaussTube.inv hc0 (ζ c) = ζ c
      rw [ζ, map_add, map_div₀, AlgEquiv.commutes, GaussTube.inv_apply, GaussTube.invHom_X]
      field_simp
      ring
    rw [ψ_algebraMap]
    change (GaussTube.inv hc0).toAlgHom (aeval (ζ c) p) = _
    rw [← Polynomial.aeval_algHom_apply, hζ']
  rw [← RatFunc.num_div_denom φ, map_div₀, map_div₀, hp, hp]

/-- **The two extensions**: a valuation of `C(x)` restricting to the Gauss point of
`t = x + c/x` (`0 < |c| < 1`) is `w_{0,1}` or `w_{0,|c|}`. -/
theorem eq_or_eq_of_comap {μ : Valuation (RatFunc C) ℝ≥0} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1)
    (hμ : μ.comap (ψ c).toRingHom = gauss1 C) :
    μ = gauss1 C ∨ μ = gaussRat ν 0 (Units.mk0 ‖c‖₊ (by simpa using hc0)) := by
  have hψ : ∀ φ, μ (ψ c φ) = gauss1 C φ := fun φ ↦ by
    rw [← hμ]; rfl
  have hC : ∀ b : C, μ (algebraMap C (RatFunc C) b) = ‖b‖₊ := fun b ↦ by
    have := hψ (algebraMap C (RatFunc C) b)
    rwa [AlgHom.commutes, gauss1_algebraMap_C] at this
  have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have hc' : ‖c‖₊ < 1 := by exact_mod_cast hc1
  have hK0 : (0 : ℝ≥0) < ‖c‖₊ := by simpa using hc0
  have hζ : μ (ζ c) = 1 := by
    have := hψ RatFunc.X
    rwa [ψ_X, AnnulusUnit.gaussRat_X, Units.val_one] at this
  set ρ := μ RatFunc.X
  have hρ0 : ρ ≠ 0 := by simpa [ρ] using hX0
  have hcX : μ (algebraMap C (RatFunc C) c / RatFunc.X) = ‖c‖₊ / ρ := by rw [map_div₀, hC]
  have hρ : ρ = 1 ∨ ρ = ‖c‖₊ := by
    by_contra! h
    obtain ⟨h1, h2⟩ := h
    rw [ζ] at hζ
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · rcases lt_or_gt_of_ne h2 with hlt' | hgt'
      · -- `ρ < |c|`: the term `c/x` dominates
        have hdom : ρ < ‖c‖₊ / ρ := by
          rw [lt_div_iff₀ (pos_iff_ne_zero.2 hρ0)]
          calc ρ * ρ < 1 * ‖c‖₊ := mul_lt_mul'' hlt hlt' zero_le zero_le
            _ = ‖c‖₊ := one_mul _
        rw [add_comm, Valuation.map_add_eq_of_lt_left _ (by rw [hcX]; exact hdom), hcX] at hζ
        rw [div_eq_one_iff_eq hρ0] at hζ
        exact h2 hζ.symm
      · -- `|c| < ρ < 1`: both terms are small
        have : μ (RatFunc.X + algebraMap C (RatFunc C) c / RatFunc.X) < 1 :=
          (Valuation.map_add _ _ _).trans_lt (max_lt hlt (by
            rw [hcX, div_lt_one (pos_iff_ne_zero.2 hρ0)]; exact hgt'))
        exact absurd hζ this.ne
    · -- `ρ > 1`: the term `x` dominates
      have hdom : ‖c‖₊ / ρ < ρ := by
        rw [div_lt_iff₀ (pos_iff_ne_zero.2 hρ0)]
        calc ‖c‖₊ < 1 * 1 := by rw [one_mul]; exact hc'
          _ < ρ * ρ := mul_lt_mul'' hgt hgt zero_le zero_le
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [hcX]; exact hdom)] at hζ
      exact h1 hζ
  rcases hρ with h1 | hK
  · exact Or.inl (eq_gauss1_of_comap hc1 hμ h1)
  · right
    set μ' := μ.comap (GaussTube.inv hc0).toRingHom
    have hμ' : μ'.comap (ψ c).toRingHom = gauss1 C := by
      refine Valuation.ext fun φ ↦ ?_
      change μ (GaussTube.inv hc0 (ψ c φ)) = gauss1 C φ
      rw [inv_ψ, hψ]
    have hX' : μ' RatFunc.X = 1 := by
      change μ (GaussTube.inv hc0 RatFunc.X) = 1
      rw [GaussTube.inv_apply, GaussTube.invHom_X, hcX, hK, div_self hK0.ne']
    have he := eq_gauss1_of_comap hc1 hμ' hX'
    ext φ
    have := congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v (GaussTube.inv hc0 φ)) he
    simp only [μ', Valuation.comap_apply] at this
    change μ (GaussTube.inv hc0 (GaussTube.inv hc0 φ)) = _ at this
    rw [GaussTube.inv_inv_apply] at this
    rw [this]
    have h := GaussTube.gaussRat_inv hc0 1 φ
    have hr : GaussTube.invRad hc0 1 = Units.mk0 ‖c‖₊ (by simpa using hc0) :=
      Units.ext (by rw [GaussTube.coe_invRad]; simp)
    rw [h, hr]

end Hom


/-! ### The two-vertex twist -/

section Twist

variable [IsAlgClosed C]

/-- `F'` as an extension of `C(t)`, `t = x + c/x`: the normalization of `ℙ¹_t` in `F'` is the
model with the two vertices `w_{0,1}`, `w_{0,|c|}`. -/
def TwoV (_c : C) (F' : Type*) : Type _ := F'

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F']

instance : Field (TwoV c F') := inferInstanceAs (Field F')

noncomputable instance : Algebra (RatFunc C) (TwoV c F') :=
  ((algebraMap (RatFunc C) F').comp (ψ c).toRingHom).toAlgebra

instance : Algebra C (TwoV c F') := inferInstanceAs (Algebra C F')

/-- The identity `F' → TwoV c F'`. -/
noncomputable def toTwoV : F' ≃+* TwoV c F' := RingEquiv.refl F'

omit [IsUltrametricDist C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma algebraMap_twoV_apply (φ : RatFunc C) :
    algebraMap (RatFunc C) (TwoV c F') φ = toTwoV c (algebraMap (RatFunc C) F' (ψ c φ)) := rfl

instance : IsScalarTower C (RatFunc C) (TwoV c F') :=
  IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [algebraMap_twoV_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    rfl

omit [IsUltrametricDist C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma xF_twoV : xF C (TwoV c F') = toTwoV c (algebraMap (RatFunc C) F' (ζ c)) := by
  rw [xF, algebraMap_twoV_apply, ψ_X]

variable [FiniteDimensional (RatFunc C) F']

instance : IsCurveFunctionField C (TwoV c F') :=
  haveI : IsCurveFunctionField C F' := GaussFibre.isCurveFunctionField_F
  inferInstanceAs (IsCurveFunctionField C F')

instance : FiniteDimensional (RatFunc C) (TwoV c F') := by
  haveI : IsCurveFunctionField C (TwoV c F') := inferInstance
  refine finiteDimensional_of_transcendental ?_
  rw [xF_twoV]
  have h : Transcendental C (ζ c) := ζ_transcendental
  rw [← transcendental_algebraMap_iff (algebraMap (RatFunc C) F').injective] at h
  exact h

end Twist

/-! ### The extensions of the Gauss point of `t` -/

section Ext

open GaussStability

variable [IsAlgClosed C] {c} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F']

/-- The radius `|c|` of the inner vertex. -/
noncomputable abbrev rc (hc0 : c ≠ 0) : ℝ≥0ˣ := Units.mk0 ‖c‖₊ (by simpa using hc0)

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
include hc0 hc1 in
lemma comap_twoV_eq {r : ℝ≥0ˣ} (hr : (r : ℝ≥0) = 1 ∨ (r : ℝ≥0) = ‖c‖₊)
    (v : GaussExtension (0 : C) r F') :
    (v.1.comap (toTwoV c).symm.toRingHom).comap (algebraMap (RatFunc C) (TwoV c F')) =
      gauss1 C := by
  refine Valuation.ext fun φ ↦ ?_
  rw [Valuation.comap_apply, Valuation.comap_apply, algebraMap_twoV_apply]
  change v.1 (algebraMap (RatFunc C) F' (ψ c φ)) = _
  rw [← Valuation.comap_apply, v.2, ← gaussRat_comp_ψ hc0 hc1.le hr]
  rfl

/-- An extension of `w_{0,1}` (outer vertex) as an extension of the Gauss point of `t`. -/
noncomputable def extU (v : GaussExtension (0 : C) 1 F') : Ext C (TwoV c F') :=
  ⟨v.1.comap (toTwoV c).symm.toRingHom, comap_twoV_eq hc0 hc1 (.inl rfl) v⟩

/-- An extension of `w_{0,|c|}` (inner vertex) as an extension of the Gauss point of `t`. -/
noncomputable def extD (v : GaussExtension (0 : C) (rc hc0) F') : Ext C (TwoV c F') :=
  ⟨v.1.comap (toTwoV c).symm.toRingHom, comap_twoV_eq hc0 hc1 (.inr rfl) v⟩

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
include hc0 hc1 in
/-- Every extension of the Gauss point of `t` comes from one of the two vertices. -/
lemma ext_cases (w : Ext C (TwoV c F')) :
    (w.1.comap (toTwoV c).toRingHom).comap (algebraMap (RatFunc C) F') = gauss1 C ∨
      (w.1.comap (toTwoV c).toRingHom).comap (algebraMap (RatFunc C) F') =
        gaussRat ν 0 (rc hc0) := by
  refine eq_or_eq_of_comap hc0 hc1 (Valuation.ext fun φ ↦ ?_)
  have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u φ) w.2
  simp only [Valuation.comap_apply, algebraMap_twoV_apply] at this
  exact this

end Ext

end TwoVertex

end SemistableReduction
