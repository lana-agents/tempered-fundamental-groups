/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourBranch
import TemperedFundamentalGroups.SemistableReduction.TypeFourUnif

/-!
# The branches near a type-4 point converge to it

Blueprint §9.12, leaf T4, part (G). Let `Bₙ = ball aₙ ‖cₙ‖` be nested balls with empty
intersection, `ξ` their limit (a type-4 point of `C(x)`) and `ξ'` an extension of `ξ` to `F`.

* `isIntegral_polynomial_iff`: integrality over `C[x] ⊆ F` in the two forms (the subalgebra
  `Algebra.adjoin C {x}` and the polynomial ring `C[X]` acting through `x`);
* `eventually_isIntegral` (B3): an element integral over `C[x]` of value `≤ 1` at all extensions
  of `ξ` lies in the integral closure of the chart of `Bₙ` for all large `n` (its characteristic
  polynomial has coefficients of `ξ`-value `≤ 1`, and `ξ` agrees with the Gauss point of `Bₙ` on
  them for large `n`, S8.0);
* **`eventually_val_le_one`** (convergence of the branches): for `g` integral over `C[x]` with
  `ξ'(g) ≤ 1`, for all large `n` every component through the centre `P'` of `ξ'` on the chart of
  `Bₙ` has `|g| ≤ 1`. An idempotent approximation `e` (`|e| = 1` at `ξ'`, `< 1` at the other
  extensions) gives `eᴹ g ∈ R'` and `e ∈ R' ∖ P'`.
-/

open Polynomial Metric
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace TypeFour

open GaussFibre DiscCount SmoothVertex AffineTwist LocalGlobal Splitting GaussLimit TubeCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

/-! ### Integrality over `C[x]` -/

section Poly

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F]

variable (C F) in
/-- `C[X]` acting on `F` through `x`. -/
noncomputable abbrev polyAlg : Algebra C[X] F :=
  ((algebraMap (RatFunc C) F).comp (algebraMap C[X] (RatFunc C))).toAlgebra

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma polyAlg_apply (P : C[X]) :
    @algebraMap C[X] F _ _ (polyAlg C F) P = aeval (xF C F) P := (aeval_xF P).symm

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- Integrality over `C[x]`: the subalgebra form gives the polynomial form. -/
lemma isIntegral_polynomial_of_adjoin {y : F} (hy : IsIntegral (Algebra.adjoin C {xF C F}) y) :
    @IsIntegral C[X] F _ _ (polyAlg C F) y := by
  letI := polyAlg C F
  have hinj : Function.Injective (aeval (R := C) (xF C F)) :=
    transcendental_iff_injective.1 GaussFibre.transcendental_xF
  let φ₀ : C[X] ≃ₐ[C] (aeval (R := C) (xF C F)).range := AlgEquiv.ofInjective _ hinj
  let φ : Algebra.adjoin C {xF C F} →+* C[X] :=
    (φ₀.symm.toRingEquiv.toRingHom).comp
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval C (xF C F))).toRingHom
  refine IsIntegral.map_of_comp_eq φ (RingHom.id F) (RingHom.ext fun a ↦ ?_) hy
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [polyAlg_apply]
  have := congrArg Subtype.val (φ₀.apply_symm_apply
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval C (xF C F)) a))
  rw [AlgEquiv.ofInjective_apply] at this
  exact this

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- Integrality over `C[x]`: the polynomial form gives the subalgebra form. -/
lemma isIntegral_adjoin_of_polynomial {y : F} (hy : @IsIntegral C[X] F _ _ (polyAlg C F) y) :
    IsIntegral (Algebra.adjoin C {xF C F}) y := by
  letI := polyAlg C F
  exact IsIntegral.map_of_comp_eq (aeval (⟨xF C F, Algebra.self_mem_adjoin_singleton C _⟩ :
    Algebra.adjoin C {xF C F})).toRingHom (RingHom.id F)
    (by ext P <;> simp [polyAlg_apply]) hy

end Poly

/-! ### B3 for the balls `Bₙ` -/

section Balls

variable {a c : ℕ → C} (hc : ∀ n, c n ≠ 0)
  (hnest : ∀ n, ball (a (n + 1)) ‖c (n + 1)‖ ⊆ ball (a n) ‖c n‖)
  (hempty : (⋂ n, ball (a n) ‖c n‖) = ∅)

omit [IsAlgClosed C] in
include hc hnest hempty in
/-- For every `A`, the radii `‖cₙ‖` eventually lie below the radius `ξ(x - A)`. -/
lemma eventually_norm_le_radius {ξ : Valuation (RatFunc C) ℝ≥0}
    (hC : ∀ b : C, ξ (algebraMap C (RatFunc C) b) = ‖b‖₊)
    (hlt : ∀ n, ξ (RatFunc.X - algebraMap C (RatFunc C) (a n)) < ‖c n‖₊) (A : C) :
    ∃ m, ∀ n ≥ m, ‖c n‖₊ ≤ radius ξ A := by
  obtain ⟨m, hm⟩ := exists_norm_lt_norm_sub hc hnest hempty A
  refine ⟨m, fun n hn ↦ ?_⟩
  have hXa : algebraMap C[X] (RatFunc C) (X - Polynomial.C (a m)) =
      RatFunc.X - algebraMap C (RatFunc C) (a m) := by
    rw [map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
  have hrad : radius ξ A = ‖A - a m‖₊ := by
    rw [radius, GaussLimit.algebraMap_X_sub_C (a m) A, Valuation.map_add_eq_of_lt_right, hC,
      ← nnnorm_neg, neg_sub]
    rw [hC, hXa, ← nnnorm_neg, neg_sub]
    exact (hlt m).trans (by exact_mod_cast hm)
  rw [hrad]
  have := (norm_le_of_le hc hnest hn).trans hm.le
  exact_mod_cast this

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [Algebra.IsSeparable (RatFunc C) F]

include hc hnest hempty in
/-- **B3 for the balls.** An element integral over `C[x]` of value `≤ 1` at all extensions of the
limit `ξ` is integral over the chart `O_C[(x - aₙ)/cₙ]` for all large `n`. -/
theorem eventually_isIntegral {ξ : Valuation (RatFunc C) ℝ≥0} (hξ : IsTypeFour ξ)
    (hlt : ∀ n, ξ (RatFunc.X - algebraMap C (RatFunc C) (a n)) < ‖c n‖₊) {y : F}
    (hy : IsIntegral (Algebra.adjoin C {xF C F}) y)
    (hyv : ∀ w : Valuation F ℝ≥0, w.comap (algebraMap (RatFunc C) F) = ξ → w y ≤ 1) :
    ∃ N, ∀ n ≥ N, IsIntegral (discRing (a n) (c n)) y := by
  classical
  have hC : ∀ b : C, ξ (algebraMap C (RatFunc C) b) = ‖b‖₊ := fun b ↦ by
    rw [hξ.map_C, NormedField.valuation_apply]
  obtain ⟨b₁, c₁, D₁, hD₁⟩ := exists_discVal hξ
  have hle : ∀ g : Factor (DiscField D₁) (UniformSpace.Completion (DiscField D₁)) F,
      ‖toLocal g y‖ ≤ 1 := fun g ↦ by
    have := hyv (extValuation g) ((Splitting.comap_extValuation D₁ g).trans hD₁)
    rw [extValuation_apply] at this
    exact_mod_cast this
  letI := polyAlg C F
  haveI : IsScalarTower C[X] (RatFunc C) F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hzint : IsIntegral C[X] y := isIntegral_polynomial_of_adjoin hy
  set P₀ : C[X][X] := minpoly C[X] y ^ Module.finrank (RatFunc C)⟮y⟯ F
  have hP₀ : P₀.map (algebraMap C[X] (RatFunc C)) = normPoly (RatFunc C) y := by
    rw [Polynomial.map_pow, normPoly,
      minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc C) hzint]
  have hP₀m : P₀.Monic := (minpoly.monic hzint).pow _
  have hcoeff (i : ℕ) : ξ (algebraMap C[X] (RatFunc C) (P₀.coeff i)) ≤ 1 := by
    haveI : Infinite (DiscField D₁) :=
      Infinite.of_injective _ (algebraMap C (DiscField D₁)).injective
    haveI : Infinite (RatFunc C) :=
      Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
    have h := norm_coeff_normPoly_le_one (F := DiscField D₁)
      (K := UniformSpace.Completion (DiscField D₁)) (F' := F) (y := y) hle i
    have hmap := normPoly_map_ringEquiv (WithAbs.equiv D₁.val.toAbsoluteValue).symm
      (F₂ := DiscField D₁) (by ext; rfl) y
    rw [← hmap, coeff_map, ← hP₀, coeff_map, WithAbs.norm_eq_apply_ofAbs] at h
    rw [← hD₁]
    exact_mod_cast h
  -- thresholds from S8.0
  choose A hA using fun i : ℕ ↦ exists_forall_eq_gaussRat hξ.map_C (P₀.coeff i)
  choose m hm using fun i : ℕ ↦ eventually_norm_le_radius hc hnest hempty hC hlt (A i)
  refine ⟨(Finset.range (P₀.natDegree + 1)).sup m, fun n hn ↦ ?_⟩
  have hcn := hc n
  have hmem (i : ℕ) : algebraMap C[X] (RatFunc C) (P₀.coeff i) ∈ discRing (a n) (c n) := by
    by_cases hi : i ≤ P₀.natDegree
    · refine algebraMap_mem_discRing_of_le hcn ?_
      set a' := a n + c n
      have hrad : radius ξ a' = ‖c n‖₊ := by
        have hXa : algebraMap C[X] (RatFunc C) (X - Polynomial.C (a n)) =
            RatFunc.X - algebraMap C (RatFunc C) (a n) := by
          rw [map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
        rw [radius, GaussLimit.algebraMap_X_sub_C (a n) a', show a n - a' = -c n by ring,
          Valuation.map_add_eq_of_lt_right]
        · rw [hC, nnnorm_neg]
        · rw [hC, nnnorm_neg, hXa]
          exact hlt n
      have hra : radius ξ a' ≤ radius ξ (A i) := by
        rw [hrad]
        exact hm i n ((Finset.le_sup (f := m) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))).trans hn)
      have hu : radiusUnit ξ a' = Units.mk0 ‖c n‖₊ (nnnorm_ne_zero_iff.2 hcn) := by
        ext; rw [val_radiusUnit, Units.val_mk0, hrad]
      rw [← gaussRat_eq_of_le (a := a') (b := a n) (r := Units.mk0 ‖c n‖₊ _) (by
        rw [NormedField.valuation_apply, Units.val_mk0, show a' - a n = c n by ring]), ← hu,
        ← hA i a' hra]
      exact hcoeff i
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero]
      exact Subring.zero_mem _
  have hcs : (↑(P₀.map (algebraMap C[X] (RatFunc C))).coeffs : Set (RatFunc C)) ⊆
      discRing (a n) (c n) := by
    intro f hf
    obtain ⟨k, -, rfl⟩ := mem_coeffs_iff.1 hf
    rw [coeff_map]
    exact hmem k
  refine ⟨(P₀.map (algebraMap C[X] (RatFunc C))).toSubring _ hcs,
    (monic_toSubring _ _ _).2 (hP₀m.map _), ?_⟩
  rw [show algebraMap (discRing (a n) (c n)) F =
    (algebraMap (RatFunc C) F).comp (discRing (a n) (c n)).subtype from rfl, ← eval₂_map,
    map_toSubring, ← aeval_def, hP₀, normPoly, map_pow]
  change aeval y (minpoly (RatFunc C) y) ^ _ = 0
  rw [minpoly.aeval, zero_pow Module.finrank_pos.ne']

include hc hnest hempty in
/-- **The branches converge to `ξ'`.** For `g` integral over `C[x]` with `ξ'(g) ≤ 1`, for all
large `n` every component through the centre of `ξ'` on the chart of `Bₙ` has `|g| ≤ 1`. -/
theorem eventually_val_le_one {ξ' : Valuation F ℝ≥0}
    (hξ : IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F)))
    (hlt : ∀ n, ξ' (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) (a n))) <
      ‖c n‖₊)
    {g : F} (hg : IsIntegral (Algebra.adjoin C {xF C F}) g) (hgle : ξ' g ≤ 1) :
    ∃ N, ∀ n ≥ N, ∀ P' : Ideal (DRint (0 : C) 1 (Aff (a n) (c n) (hc n) F)), P'.IsMaximal →
      (∀ y ∈ P', ξ' ((toAff (hc n)).symm (y : Aff (a n) (c n) (hc n) F)) < 1) →
      ∀ v : Ext C (Aff (a n) (c n) (hc n) F), Through P' v → v.1 (toAff (hc n) g) ≤ 1 := by
  classical
  set ξ := ξ'.comap (algebraMap (RatFunc C) F)
  obtain ⟨b₁, c₁, D₁, hD₁⟩ := exists_discVal hξ
  have hD₁' : ξ'.comap (algebraMap (RatFunc C) F) = D₁.val := hD₁.symm
  obtain ⟨g', hg'⟩ := TypeFour.exists_eq_extValuation' D₁ hD₁'
  -- an idempotent approximation
  obtain ⟨e₀, he₁, he₀⟩ := exists_approx_idempotent (F := DiscField D₁)
    (K := UniformSpace.Completion (DiscField D₁)) (F' := F) g'
  have hext : ∀ w : Valuation F ℝ≥0, w.comap (algebraMap (RatFunc C) F) = ξ →
      ∃ h : Factor (DiscField D₁) (UniformSpace.Completion (DiscField D₁)) F,
        extValuation h = w := fun w hw ↦
    TypeFour.exists_eq_extValuation' D₁ (hw.trans hD₁.symm)
  have hval₀ : extValuation g' e₀ = 1 := by
    rw [extValuation_apply]
    exact NNReal.eq ((DenseCompletion.norm_eq_of_norm_sub_lt (by rwa [norm_one])).trans norm_one)
  have hlt₀ : ∀ h, h ≠ g' → extValuation h e₀ < 1 := fun h hne ↦ by
    rw [extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]; exact he₀ h hne
  -- make it integral over `C[x]`
  letI := polyAlg C F
  haveI : IsScalarTower C[X] (RatFunc C) F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := IsLocalization.isAlgebraic (RatFunc C) (nonZeroDivisors C[X])
  haveI := Algebra.IsAlgebraic.trans C[X] (RatFunc C) F
  obtain ⟨d, hd0, hdint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := C[X]) e₀).exists_integral_multiple
  obtain ⟨γ, hγ⟩ := exists_nnnorm_eq hξ d
  have hξd : ξ (algebraMap C[X] (RatFunc C) d) ≠ 0 := by
    rw [Ne, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]
    exact hd0
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hγ
    exact hξd hγ.symm
  set lam : C[X] := Polynomial.C γ⁻¹ * d
  set e : F := lam • e₀
  have heint : IsIntegral (Algebra.adjoin C {xF C F}) e := by
    refine isIntegral_adjoin_of_polynomial ?_
    change IsIntegral C[X] ((Polynomial.C γ⁻¹ * d) • e₀)
    rw [mul_smul]
    exact hdint.smul _
  have hlam : ξ (algebraMap C[X] (RatFunc C) lam) = 1 := by
    rw [map_mul, map_mul, ratFunc_algebraMap_C, hξ.map_C, ← hγ]
    change ‖γ⁻¹‖₊ * ‖γ‖₊ = 1
    rw [nnnorm_inv, inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hγ0)]
  have hres : ∀ (w : Valuation F ℝ≥0), w.comap (algebraMap (RatFunc C) F) = ξ →
      w e = w e₀ := by
    intro w hw
    change w (lam • e₀) = _
    rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply C[X] (RatFunc C) F,
      ← Valuation.comap_apply, hw, hlam, one_mul]
  have hξ'e : ξ' e = 1 := by rw [hres ξ' rfl, ← hg', hval₀]
  -- a power of `e` pushes `g` below `1` at the other extensions
  haveI : Fintype (Factor (DiscField D₁) (UniformSpace.Completion (DiscField D₁)) F) :=
    inferInstance
  have hM : ∀ h : Factor (DiscField D₁) (UniformSpace.Completion (DiscField D₁)) F,
      ∃ M : ℕ, h ≠ g' → extValuation h e₀ ^ M * extValuation h g ≤ 1 := by
    intro h
    by_cases hh : h = g'
    · exact ⟨0, fun h' ↦ absurd hh h'⟩
    by_cases hg0 : extValuation h g = 0
    · exact ⟨0, fun _ ↦ by rw [hg0, mul_zero]; exact zero_le⟩
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (pos_iff_ne_zero.2 hg0)) (hlt₀ h hh)
    refine ⟨M, fun _ ↦ ?_⟩
    calc extValuation h e₀ ^ M * extValuation h g ≤ (extValuation h g)⁻¹ * extValuation h g :=
          mul_le_mul_left hM.le _
      _ = 1 := inv_mul_cancel₀ hg0
  choose M hM using hM
  set M₀ := Finset.univ.sup M
  set h₀ : F := e ^ M₀ * g
  have hh₀int : IsIntegral (Algebra.adjoin C {xF C F}) h₀ := (heint.pow _).mul hg
  have hh₀v : ∀ w : Valuation F ℝ≥0, w.comap (algebraMap (RatFunc C) F) = ξ → w h₀ ≤ 1 := by
    intro w hw
    obtain ⟨h, rfl⟩ := hext w hw
    rw [map_mul, map_pow, hres _ hw]
    by_cases hh : h = g'
    · subst hh
      rw [hval₀, one_pow, one_mul, hg']
      exact hgle
    · have hle1 : extValuation h e₀ ≤ 1 := (hlt₀ h hh).le
      calc extValuation h e₀ ^ M₀ * extValuation h g ≤ extValuation h e₀ ^ M h *
            extValuation h g := mul_le_mul_left (pow_le_pow_of_le_one zero_le hle1
              (Finset.le_sup (f := M) (Finset.mem_univ h))) _
        _ ≤ 1 := hM h hh
  have hev : ∀ w : Valuation F ℝ≥0, w.comap (algebraMap (RatFunc C) F) = ξ → w e ≤ 1 := by
    intro w hw
    obtain ⟨h, rfl⟩ := hext w hw
    rw [hres _ hw]
    by_cases hh : h = g'
    · rw [hh, hval₀]
    · exact (hlt₀ h hh).le
  have hltξ : ∀ n, ξ (RatFunc.X - algebraMap C (RatFunc C) (a n)) < ‖c n‖₊ := hlt
  obtain ⟨N₁, hN₁⟩ := eventually_isIntegral hc hnest hempty hξ hltξ heint hev
  obtain ⟨N₂, hN₂⟩ := eventually_isIntegral hc hnest hempty hξ hltξ hh₀int hh₀v
  refine ⟨max N₁ N₂, fun n hn P' _ hcen v hv ↦ ?_⟩
  set E : DRint (0 : C) 1 (Aff (a n) (c n) (hc n) F) :=
    ⟨toAff (hc n) e, (isIntegral_toAff_iff (hc n) e).2 (hN₁ n (le_of_max_le_left hn))⟩
  set H : DRint (0 : C) 1 (Aff (a n) (c n) (hc n) F) :=
    ⟨toAff (hc n) h₀, (isIntegral_toAff_iff (hc n) h₀).2 (hN₂ n (le_of_max_le_right hn))⟩
  have hEP : E ∉ P' := fun h ↦ by
    have := hcen E h
    change ξ' e < 1 at this
    rw [hξ'e] at this
    exact lt_irrefl 1 this
  obtain ⟨Q, hQ, hQP⟩ := hv
  have hvE : v.1 (toAff (hc n) e) = 1 := (valuation_eq_one_of_notMem hEP hQP).1
  have hvH : v.1 (toAff (hc n) h₀) ≤ 1 := valuation_le_one_D v H
  rw [show toAff (hc n) h₀ = toAff (hc n) e ^ M₀ * toAff (hc n) g by
    simp [h₀, map_mul, map_pow], map_mul, map_pow, hvE, one_pow, one_mul] at hvH
  exact hvH

end Balls

end TypeFour

end SemistableReduction
