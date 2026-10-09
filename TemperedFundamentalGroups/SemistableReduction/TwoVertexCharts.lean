/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartBounds
import TemperedFundamentalGroups.SemistableReduction.TwoVertex
import TemperedFundamentalGroups.SemistableReduction.AffineTwist

/-!
# The two-vertex model and its two one-vertex models

Blueprint §9.12, O12 / R5, step (1). For a finite extension `F` of `C(x)` and `0 < |c| < 1`, the
twist `T = TwoV c F` (`t = x + c/x`) has the extensions of `w_{0,1}` (outer, `ιU`) and of
`w_{0,|c|}` (inner, `ιD`, the extensions of `w_{0,1}` on `G = Aff 0 c F`, coordinate `s = x/c`).

* `ext_cases'`: every extension of the Gauss point of `t` is outer or inner, not both;
* the values of `x`, `x/t`, `c/(xt)` at outer and inner extensions;
* the comparisons of reduced charts (instances of `ChartLocal.IsLocalIso`):
  `isLocalIso_outer` (`F` at `x` and `T` at `t`, away from `x̄ = 0`), `isLocalIso_outerInf`
  (`F` and `T` at `∞`, outer points), `isLocalIso_innerInf` (`G` at `s` and the inner points of `T`
  at `t = ∞`), `isLocalIso_innerMid` (`G` at `s` and the inner points of `T` at `t ≠ 0, ∞`).
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TwoVertexCharts

open GaussFibre TwoVertex AffineTwist ChartLocal

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  {c : C} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1)

/-- The inner one-vertex model `G = Aff 0 c F` (coordinate `s = x/c`) inside `T = TwoV c F`. -/
noncomputable def φG : Aff (0 : C) c hc0 F ≃+* TwoV c F := (toAff hc0).symm.trans (toTwoV c)

/-- Outer extensions. -/
noncomputable def ιU : Ext C F → Ext C (TwoV c F) := extU hc0 hc1

/-- Inner extensions. -/
noncomputable def ιD : Ext C (Aff (0 : C) c hc0 F) → Ext C (TwoV c F) :=
  fun w ↦ extD hc0 hc1 ((extAff hc0).symm w)

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιU_apply (w : Ext C F) (y : F) : (ιU hc0 hc1 w).1 (toTwoV c y) = w.1 y := rfl

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιD_apply (w : Ext C (Aff (0 : C) c hc0 F)) (y : Aff (0 : C) c hc0 F) :
    (ιD hc0 hc1 w).1 (φG hc0 y) = w.1 y := rfl

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]
  in
lemma toTwoV_algebraMap_C (b : C) : toTwoV c (algebraMap C F b) = algebraMap C (TwoV c F) b := rfl

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]
  in
lemma φG_algebraMap_C (b : C) :
    φG hc0 (algebraMap C (Aff (0 : C) c hc0 F) b) = algebraMap C (TwoV c F) b := rfl

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma valuation_ιU_x (w : Ext C F) : (ιU hc0 hc1 w).1 (toTwoV c (xF C F)) = 1 := by
  rw [ιU_apply, valuation_xF]

omit [IsAlgClosed C] in
lemma valuation_toAff_x (w : Ext C (Aff (0 : C) c hc0 F)) :
    w.1 (toAff hc0 (xF C F)) = ‖c‖₊ := by
  have h := valuation_xF w
  rw [xF_aff, gaussCoord_eq, map_zero, sub_zero, map_mul, map_mul, map_mul] at h
  have hc : w.1 (toAff hc0 (algebraMap (RatFunc C) F (algebraMap C (RatFunc C) c⁻¹))) =
      ‖c‖₊⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply C (RatFunc C) F,
      show toAff hc0 (algebraMap C F c⁻¹) = algebraMap C (Aff (0 : C) c hc0 F) c⁻¹ from rfl,
      valuation_algebraMap_C', nnnorm_inv]
  rw [hc] at h
  have hc' : (‖c‖₊ : ℝ≥0) ≠ 0 := by simpa using hc0
  change w.1 (toAff hc0 (algebraMap (RatFunc C) F RatFunc.X)) = _
  calc w.1 (toAff hc0 (algebraMap (RatFunc C) F RatFunc.X))
      = ‖c‖₊ * (‖c‖₊⁻¹ * w.1 (toAff hc0 (algebraMap (RatFunc C) F RatFunc.X))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc', one_mul]
    _ = ‖c‖₊ := by rw [h, mul_one]

lemma valuation_ιD_x (w : Ext C (Aff (0 : C) c hc0 F)) :
    (ιD hc0 hc1 w).1 (toTwoV c (xF C F)) = ‖c‖₊ := by
  rw [← valuation_toAff_x hc0 w]
  rfl

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
/-- **Every extension of the Gauss point of `t` is outer or inner.** -/
lemma ext_cases' (w' : Ext C (TwoV c F)) :
    (∃ w, ιU hc0 hc1 w = w') ∨ ∃ w, ιD hc0 hc1 w = w' := by
  rcases ext_cases hc0 hc1 w' with h | h
  · exact Or.inl ⟨⟨_, h⟩, rfl⟩
  · exact Or.inr ⟨extAff hc0 ⟨_, h⟩, rfl⟩

lemma ιU_ne_ιD (w : Ext C F) (w' : Ext C (Aff (0 : C) c hc0 F)) :
    ιU hc0 hc1 w ≠ ιD hc0 hc1 w' := by
  intro h
  have h1 := valuation_ιU_x hc0 hc1 w
  rw [h, valuation_ιD_x] at h1
  have : ‖c‖₊ < 1 := by exact_mod_cast hc1
  exact this.ne h1

lemma valuation_ιD_toTwoV_x_lt (w : Ext C (Aff (0 : C) c hc0 F)) :
    (ιD hc0 hc1 w).1 (toTwoV c (xF C F)) < 1 := by
  rw [valuation_ιD_x]; exact_mod_cast hc1

lemma isIntegral_of_mem {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    {A : Subalgebra R L} {a : L} (ha : a ∈ A) : IsIntegral A a :=
  isIntegral_algebraMap (R := A) (x := ⟨a, ha⟩)

omit [IsAlgClosed C] in
/-- A reduction equal to `1`. -/
lemma red_eq_one_of {K : Type*} [Field K] [Algebra (RatFunc C) K] {w : Ext C K} {f : K}
    (h : w.1 (f - 1) < 1) : red C f w = 1 := by
  have : f = (f - 1) + 1 := by ring
  rw [this, red_add h.le (by rw [map_one]), (red_eq_zero_iff h.le).2 h, red_one, zero_add]

/-! ### The coordinate `t` -/

omit [IsUltrametricDist C] in
lemma xF_twoV' : xF C (TwoV c F) = toTwoV c (xF C F + algebraMap C F c / xF C F) := by
  rw [xF_twoV, ζ, map_add, map_div₀, ← IsScalarTower.algebraMap_apply]

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma xF_ne_zero [FiniteDimensional (RatFunc C) F] : xF C F ≠ 0 := by
  rw [xF, ne_eq, map_eq_zero_iff _ (algebraMap (RatFunc C) F).injective]
  exact RatFunc.X_ne_zero

omit [IsUltrametricDist C] in
/-- `x` is integral over `C[t]`: `x² - t x + c = 0`. -/
lemma isIntegral_xT [FiniteDimensional (RatFunc C) F] :
    IsIntegral (Algebra.adjoin C {xF C (TwoV c F)}) (toTwoV c (xF C F)) := by
  set t : Algebra.adjoin C {xF C (TwoV c F)} := ⟨_, Algebra.subset_adjoin rfl⟩
  refine ⟨X ^ 2 + (Polynomial.C (-t) * X + Polynomial.C (algebraMap C _ c)),
    monic_X_pow_add ((degree_linear_le).trans_lt (by norm_num)), ?_⟩
  have hx := xF_ne_zero (C := C) (F := F)
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, eval₂_neg, map_neg]
  have key : xF C F ^ 2 + (-(xF C F + algebraMap C F c / xF C F) * xF C F +
      algebraMap C F c) = 0 := by
    rw [neg_mul, add_mul, div_mul_cancel₀ _ hx]
    ring
  change toTwoV c (xF C F) ^ 2 + (-xF C (TwoV c F) * toTwoV c (xF C F) +
    algebraMap C (TwoV c F) c) = 0
  rw [xF_twoV']
  exact key

/-! ### Values at outer and inner extensions -/

section ValCalc

variable (c) in
/-- `x t = x² + c`. -/
noncomputable abbrev Dn : F := xF C F ^ 2 + algebraMap C F c

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma Dn_ne_zero [FiniteDimensional (RatFunc C) F] : Dn (F := F) c ≠ 0 := by
  have h : Dn (F := F) c =
      algebraMap (RatFunc C) F (RatFunc.X ^ 2 + algebraMap C (RatFunc C) c) := by
    rw [map_add, map_pow, ← IsScalarTower.algebraMap_apply]
  rw [h, ne_eq, map_eq_zero_iff _ (algebraMap (RatFunc C) F).injective]
  intro h0
  rw [← RatFunc.algebraMap_X, ← map_pow, ← ratFunc_algebraMap_C, ← map_add,
    map_eq_zero_iff _ (IsFractionRing.injective C[X] (RatFunc C))] at h0
  have := congrArg (coeff · 2) h0
  simp at this

variable {v : Valuation F ℝ≥0} (hv : ∀ b : C, v (algebraMap C F b) = ‖b‖₊)
include hv hc1

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
lemma val_Dn_out (hx : v (xF C F) = 1) : v (Dn c) = 1 := by
  have hc : ‖c‖₊ < 1 := by exact_mod_cast hc1
  rw [Dn, add_comm, Valuation.map_add_eq_of_lt_right, map_pow, hx, one_pow]
  rw [map_pow, hx, one_pow, hv]; exact hc

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
include hc0 in
lemma val_Dn_in (hx : v (xF C F) = ‖c‖₊) : v (Dn c) = ‖c‖₊ := by
  have hc : ‖c‖₊ < 1 := by exact_mod_cast hc1
  have hc0' : (0 : ℝ≥0) < ‖c‖₊ := by simpa using hc0
  rw [Dn, Valuation.map_add_eq_of_lt_right, hv]
  rw [map_pow, hx, hv, sq]
  exact mul_lt_of_lt_one_left hc0' hc

end ValCalc

/-- `x/t = x²/(x² + c)`. -/
noncomputable abbrev qq (c : C) : F := xF C F ^ 2 / Dn c

/-- `1/t = x/(x² + c)`. -/
noncomputable abbrev tinv (c : C) : F := xF C F / Dn c

/-- `c/(xt) = c/(x² + c)`. -/
noncomputable abbrev rr (c : C) : F := algebraMap C F c / Dn c

section ValCalc2

variable {v : Valuation F ℝ≥0} (hv : ∀ b : C, v (algebraMap C F b) = ‖b‖₊)
include hv hc1

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
lemma val_qq_out (hx : v (xF C F) = 1) : v (qq (F := F) c) = 1 := by
  rw [qq, map_div₀, val_Dn_out hc1 hv hx, map_pow, hx, one_pow, div_one]

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
include hc0 in
lemma val_qq_in (hx : v (xF C F) = ‖c‖₊) : v (qq (F := F) c) = ‖c‖₊ := by
  have hc0' : (‖c‖₊ : ℝ≥0) ≠ 0 := by simpa using hc0
  rw [qq, map_div₀, val_Dn_in hc0 hc1 hv hx, map_pow, hx, sq, mul_div_assoc, div_self hc0',
    mul_one]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma val_qq_sub_one_out [FiniteDimensional (RatFunc C) F] (hx : v (xF C F) = 1) :
    v (qq (F := F) c - 1) < 1 := by
  have h : qq (F := F) c - 1 = -rr c := by
    have := Dn_ne_zero (F := F) (c := c)
    rw [qq, rr, div_sub_one this, ← neg_div]
    congr 1
    rw [Dn]; ring
  rw [h, Valuation.map_neg, rr, map_div₀, val_Dn_out hc1 hv hx, div_one, hv]
  exact_mod_cast hc1

omit [IsUltrametricDist C] [IsAlgClosed C] in
include hc0 in
lemma val_rr_sub_one_in [FiniteDimensional (RatFunc C) F] (hx : v (xF C F) = ‖c‖₊) :
    v (rr (F := F) c - 1) < 1 := by
  have h : rr (F := F) c - 1 = -qq c := by
    have := Dn_ne_zero (F := F) (c := c)
    rw [qq, rr, div_sub_one this, ← neg_div]
    congr 1
    rw [Dn]; ring
  rw [h, Valuation.map_neg, val_qq_in hc0 hc1 hv hx]
  exact_mod_cast hc1

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
lemma val_rr_out (hx : v (xF C F) = 1) : v (rr (F := F) c) = ‖c‖₊ := by
  rw [rr, map_div₀, val_Dn_out hc1 hv hx, div_one, hv]

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
include hc0 in
lemma val_rr_in (hx : v (xF C F) = ‖c‖₊) : v (rr (F := F) c) = 1 := by
  have hc0' : (‖c‖₊ : ℝ≥0) ≠ 0 := by simpa using hc0
  rw [rr, map_div₀, val_Dn_in hc0 hc1 hv hx, hv, div_self hc0']

end ValCalc2

/-! ### Elements of the two-vertex model -/

section Elements

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιD_toTwoV (w : Ext C (Aff (0 : C) c hc0 F)) (y : F) :
    (ιD hc0 hc1 w).1 (toTwoV c y) = w.1 (toAff hc0 y) := rfl

omit [IsAlgClosed C] in
lemma val_toAff_C (w : Ext C (Aff (0 : C) c hc0 F)) (b : C) :
    w.1 (toAff hc0 (algebraMap C F b)) = ‖b‖₊ :=
  valuation_algebraMap_C' w b

omit [IsUltrametricDist C] in
lemma xF_twoV_inv [FiniteDimensional (RatFunc C) F] :
    (xF C (TwoV c F))⁻¹ = toTwoV c (tinv (F := F) c) := by
  have hx := xF_ne_zero (C := C) (F := F)
  have hD := Dn_ne_zero (F := F) (c := c)
  have key : (xF C F + algebraMap C F c / xF C F)⁻¹ = tinv (F := F) c := by
    rw [tinv, Dn]
    field_simp
  rw [xF_twoV', ← map_inv₀, key]

omit [IsUltrametricDist C] in
/-- `x/t` is integral over `C[1/t]`: `(x/t)² - x/t + c (1/t)² = 0`. -/
lemma isIntegral_qq [FiniteDimensional (RatFunc C) F] :
    IsIntegral (Algebra.adjoin C {(xF C (TwoV c F))⁻¹}) (toTwoV c (qq (F := F) c)) := by
  set ti : Algebra.adjoin C {(xF C (TwoV c F))⁻¹} := ⟨_, Algebra.subset_adjoin rfl⟩
  refine ⟨X ^ 2 + (Polynomial.C (-1) * X + Polynomial.C (algebraMap C _ c * ti ^ 2)),
    monic_X_pow_add ((degree_linear_le).trans_lt (by norm_num)), ?_⟩
  have hx := xF_ne_zero (C := C) (F := F)
  have hD := Dn_ne_zero (F := F) (c := c)
  have key : qq (F := F) c ^ 2 + (-1 * qq c + algebraMap C F c * tinv c ^ 2) = 0 := by
    rw [qq, tinv, Dn] at *
    field_simp
    ring
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, eval₂_neg, eval₂_one, map_neg,
    map_one, map_mul, map_pow]
  change toTwoV c (qq (F := F) c) ^ 2 + (-1 * toTwoV c (qq (F := F) c) +
    algebraMap C (TwoV c F) c * (xF C (TwoV c F))⁻¹ ^ 2) = 0
  rw [xF_twoV_inv]
  exact key

end Elements

/-! ### The outer finite charts: `F` at `x` and `T` at `t` -/

section Outer

variable [FiniteDimensional (RatFunc C) F] [CharZero C] {p : ℕ} (hp : p.Prime)
  (hp1 : ‖(p : C)‖ < 1) [Fintype (Ext C F)] [Fintype (Ext C (TwoV c F))]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

omit [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hp hp1 hc0 hc1 in
/-- **Maximum principle on the annulus**: an element of the chart `O_C[x]` (integral over `C[x]`,
value `≤ 1` at the extensions of `w_{0,1}`) has value `≤ 1` at all extensions of the Gauss point
of `t`. -/
lemma valuation_toTwoV_le_one {f : F} (hf : f ∈ intRing C F (xF C F))
    (w' : Ext C (TwoV c F)) : w'.1 (toTwoV c f) ≤ 1 := by
  have hfD := SmoothVertex.isIntegral_of_le hp hp1 hf.1 fun v ↦ (le_gnorm v f).trans hf.2
  obtain ⟨d, hd⟩ := ChartBounds.exists_pow_mul_le_one hfD
  set v : Valuation F ℝ≥0 := w'.1.comap (toTwoV c).toRingHom
  have hv (b : C) : v (algebraMap (RatFunc C) F (algebraMap C (RatFunc C) b)) ≤ ‖b‖₊ := by
    change w'.1 (toTwoV c (algebraMap (RatFunc C) F (algebraMap C (RatFunc C) b))) ≤ _
    rw [← IsScalarTower.algebraMap_apply, toTwoV_algebraMap_C, valuation_algebraMap_C']
  have hx : v (xF C F) ≤ 1 := by
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact (valuation_ιU_x hc0 hc1 w).le
    · change (ιD hc0 hc1 w).1 (toTwoV c (xF C F)) ≤ 1
      rw [valuation_ιD_x]
      exact_mod_cast hc1.le
  have := hd v hv 1 (by rw [map_one, one_mul, max_eq_left hx]) d le_rfl
  rwa [one_pow, one_mul] at this

include hp hp1 in
/-- **The outer finite charts agree after inverting `x̄`** (instance (I1) of the locality). -/
theorem isLocalIso_outer
    (hΛF : IsChart 𝓀 (fun w : Ext C F ↦ red C (xF C F) w) (redRing C F (xF C F)))
    (hΛT : IsChart 𝓀 (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F)) w)
      (redRing C (TwoV c F) (xF C (TwoV c F)))) :
    IsLocalIso hΛF hΛT (extEmb (toTwoV c) (fun _ ↦ rfl) (ιU hc0 hc1) (ιU_apply hc0 hc1))
      (fun w ↦ red C (xF C F) w) (fun w' ↦ red C (toTwoV c (xF C F)) w') := by
  have hxT := isIntegral_xT (C := C) (F := F) (c := c)
  refine isLocalIso_of _ _ _ _ hΛF hΛT
    ⟨isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _), ?_⟩
    ⟨hxT, ?_⟩ (fun f hf ↦ ⟨1, ⟨?_, ?_⟩, ?_⟩) (fun g hg ↦ ?_) ?_ ?_
  · exact gnorm_le_iff.2 fun w ↦ (valuation_xF w).le
  · exact gnorm_le_iff.2 fun w' ↦ by
      rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · exact (valuation_ιU_x hc0 hc1 w).le
      · exact (valuation_ιD_toTwoV_x_lt hc0 hc1 w).le
  · -- integrality over `C[t]`
    have hf' : IsIntegral (Algebra.adjoin C {toTwoV c (xF C F)}) (toTwoV c f) := hf.1
    obtain ⟨N, hN⟩ := ChartBounds.exists_pow_mul_isIntegral' (u := 1) isIntegral_one
      (by rw [one_mul]; exact hxT) hf'
    rw [one_pow, one_mul] at hN
    rw [pow_one]
    exact hxT.mul hN
  · refine gnorm_le_iff.2 fun w' ↦ ?_
    rw [pow_one, map_mul]
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [valuation_ιU_x, one_mul, ιU_apply]
      exact (le_gnorm w f).trans hf.2
    · exact mul_le_one' (valuation_ιD_toTwoV_x_lt hc0 hc1 w).le
        (valuation_toTwoV_le_one hc0 hc1 hp hp1 hf _)
  · rintro w' hw'
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact absurd ⟨w, rfl⟩ hw'
    · rw [pow_one, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (valuation_ιD_toTwoV_x_lt hc0 hc1 w)
        (valuation_toTwoV_le_one hc0 hc1 hp hp1 hf _)
  · -- clearing the pole of `t` at `x = 0`
    have hg' : IsIntegral (Algebra.adjoin C {xF C F + algebraMap C F c / xF C F})
        ((toTwoV c).symm g) := by
      have := hg.1
      rw [xF_twoV'] at this
      exact this
    have hx0 := xF_ne_zero (C := C) (F := F)
    obtain ⟨N, hN⟩ := ChartBounds.exists_pow_mul_isIntegral (u := xF C F)
      (S := Algebra.adjoin C {xF C F}) (Algebra.self_mem_adjoin_singleton C _) (by
        have : xF C F * (xF C F + algebraMap C F c / xF C F) =
            xF C F ^ 2 + algebraMap C F c := by field_simp
        rw [this]
        exact add_mem (pow_mem (Algebra.self_mem_adjoin_singleton C _) 2)
          (Subalgebra.algebraMap_mem _ c)) hg'
    refine ⟨N, hN, gnorm_le_iff.2 fun w ↦ ?_⟩
    rw [map_mul, map_pow, valuation_xF, one_pow, one_mul, ← ιU_apply hc0 hc1 w,
      RingEquiv.apply_symm_apply]
    exact (le_gnorm _ g).trans hg.2
  · intro w Q _ hu
    exact hu
  · intro w' Q _ hu
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨⟨w, rfl⟩, hu⟩
    · exfalso
      rw [(red_eq_zero_iff (valuation_ιD_toTwoV_x_lt hc0 hc1 w).le).2
        (valuation_ιD_toTwoV_x_lt hc0 hc1 w), map_zero] at hu
      exact zero_ne_one hu

end Outer

/-! ### The chart at `∞`: the maximum principle -/

section Infinity

open GaussTube

variable [FiniteDimensional (RatFunc C) F] [Fintype (Ext C F)]

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C F)] in
lemma xF_inv_one : xF C (Inv (1 : C) one_ne_zero F) = toInv one_ne_zero (xF C F)⁻¹ := by
  change toInv one_ne_zero (algebraMap (RatFunc C) F (inv one_ne_zero RatFunc.X)) = _
  rw [inv_apply, invHom_X, map_one, one_div, map_inv₀]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma invRad_one_one : invRad (one_ne_zero (α := C)) 1 = 1 := Units.ext (by simp [coe_invRad])

/-- An extension of `w_{0,1}` to `Inv 1 F` is an extension of `w_{0,1}` to `F`. -/
noncomputable def extInvOne (v : Ext C (Inv (1 : C) one_ne_zero F)) : Ext C F :=
  ⟨v.1.comap (toInv one_ne_zero).toRingHom, Valuation.ext fun φ ↦ by
    rw [Valuation.comap_apply, Valuation.comap_apply]
    have h := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u (inv one_ne_zero φ)) v.2
    simp only [Valuation.comap_apply, algebraMap_inv_apply, inv_inv_apply] at h
    change v.1 (toInv one_ne_zero (algebraMap (RatFunc C) F φ)) = _
    rw [h, gaussRat_inv, invRad_one_one]⟩

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [Fintype (GaussFibre.Ext C F)] in
lemma extInvOne_apply (v : Ext C (Inv (1 : C) one_ne_zero F)) (y : F) :
    (extInvOne v).1 y = v.1 (toInv one_ne_zero y) := rfl

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **The maximum principle for the chart at `∞`**: an element integral over `C[1/x]` with value
`≤ 1` at the extensions of `w_{0,1}` is integral over `O_C[1/x]` (as `O_C[x]` of the twist
`Inv 1 F`). -/
theorem isIntegral_inv_of_mem {f : F} (hf : f ∈ intRing C F (xF C F)⁻¹) :
    IsIntegral (DiscCount.discRing (0 : C) 1)
      (toInv one_ne_zero f : Inv (1 : C) one_ne_zero F) := by
  refine SmoothVertex.isIntegral_of_le hp hp1 ?_ fun v ↦ ?_
  · rw [xF_inv_one]
    exact hf.1
  · rw [← extInvOne_apply]
    exact (le_gnorm _ f).trans hf.2

end Infinity

/-! ### The outer charts at `∞` -/

section OuterInf

open GaussTube

variable [FiniteDimensional (RatFunc C) F] [CharZero C] {p : ℕ} (hp : p.Prime)
  (hp1 : ‖(p : C)‖ < 1) [Fintype (Ext C F)] [Fintype (Ext C (TwoV c F))]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- `1 + c/x²`, a unit of the chart at `∞` of `F` clearing the poles of `1/t`. -/
noncomputable abbrev U1 (c : C) : F := 1 + algebraMap C F c * (xF C F)⁻¹ ^ 2

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] [CharZero C] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma U1_mem_adjoin : U1 (F := F) c ∈ Algebra.adjoin C {(xF C F)⁻¹} :=
  add_mem (one_mem _) (mul_mem (Subalgebra.algebraMap_mem _ c)
    (pow_mem (Algebra.self_mem_adjoin_singleton C _) 2))

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hc1 in
lemma val_U1_sub_one (w : Ext C F) : w.1 (U1 (F := F) c - 1) < 1 := by
  rw [U1, add_sub_cancel_left, map_mul, map_pow, map_inv₀, valuation_xF, inv_one, one_pow,
    mul_one, valuation_algebraMap_C']
  exact_mod_cast hc1

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hc1 in
lemma red_U1 (w : Ext C F) : red C (U1 (F := F) c) w = 1 :=
  red_eq_one_of (val_U1_sub_one hc1 w)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hc1 in
lemma U1_mem : U1 (F := F) c ∈ intRing C F (xF C F)⁻¹ := by
  refine ⟨isIntegral_of_mem U1_mem_adjoin, gnorm_le_iff.2 fun w ↦ ?_⟩
  have : U1 (F := F) c = (U1 c - 1) + 1 := by ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le (val_U1_sub_one hc1 w).le (by rw [map_one]))

omit [CharZero C] [Fintype (GaussFibre.Ext C F)] [Fintype (GaussFibre.Ext C (TwoV c F))]
  [IsAlgClosed C] in
include hc1 in
lemma red_qq_out (w : Ext C F) : red C (qq (F := F) c) w = 1 :=
  red_eq_one_of (val_qq_sub_one_out hc1 (valuation_algebraMap_C' w) (valuation_xF w))

include hp hp1 in
/-- **The outer charts at `∞` agree after inverting `x/t`** (instance (I2) of the locality). -/
theorem isLocalIso_outerInf
    (hΛF : IsChart 𝓀 (fun w : Ext C F ↦ red C (xF C F)⁻¹ w) (redRing C F (xF C F)⁻¹))
    (hΛT : IsChart 𝓀 (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F))⁻¹ w)
      (redRing C (TwoV c F) (xF C (TwoV c F))⁻¹)) :
    IsLocalIso hΛF hΛT (extEmb (toTwoV c) (fun _ ↦ rfl) (ιU hc0 hc1) (ιU_apply hc0 hc1))
      (fun w ↦ red C (U1 (F := F) c) w) (fun w' ↦ red C (toTwoV c (qq (F := F) c)) w') := by
  have hq := isIntegral_qq (C := C) (F := F) (c := c)
  have hvin (w : Ext C (Aff (0 : C) c hc0 F)) :
      ∀ b : C, (w.1.comap (toAff hc0).toRingHom) (algebraMap C F b) = ‖b‖₊ :=
    fun b ↦ val_toAff_C hc0 w b
  have hxin (w : Ext C (Aff (0 : C) c hc0 F)) :
      (w.1.comap (toAff hc0).toRingHom) (xF C F) = ‖c‖₊ := valuation_toAff_x hc0 w
  -- the bound at inner extensions
  have hbound : ∀ f ∈ intRing C F (xF C F)⁻¹, ∃ d : ℕ, ∀ (w : Ext C (Aff (0 : C) c hc0 F)) M,
      d ≤ M → (ιD hc0 hc1 w).1 (toTwoV c (qq (F := F) c ^ M * f)) ≤ 1 := by
    intro f hf
    obtain ⟨d, hd⟩ := ChartBounds.exists_pow_mul_le_one (isIntegral_inv_of_mem hp hp1 hf)
    refine ⟨d, fun w M hM ↦ ?_⟩
    set v : Valuation (Inv (1 : C) one_ne_zero F) ℝ≥0 :=
      (ιD hc0 hc1 w).1.comap ((toInv one_ne_zero).symm.trans (toTwoV c)).toRingHom
    have hv (b : C) : v (algebraMap (RatFunc C) (Inv (1 : C) one_ne_zero F)
        (algebraMap C (RatFunc C) b)) ≤ ‖b‖₊ := by
      change (ιD hc0 hc1 w).1 (toTwoV c (algebraMap (RatFunc C) F
        (inv one_ne_zero (algebraMap C (RatFunc C) b)))) ≤ _
      rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply, ιD_toTwoV]
      exact (val_toAff_C hc0 w b).le
    have hvx : v (xF C (Inv (1 : C) one_ne_zero F)) = ‖c‖₊⁻¹ := by
      rw [xF_inv_one]
      change (ιD hc0 hc1 w).1 (toTwoV c (xF C F)⁻¹) = _
      rw [ιD_toTwoV, map_inv₀, map_inv₀, valuation_toAff_x]
    have hvq : v (toInv one_ne_zero (qq (F := F) c)) = ‖c‖₊ := by
      change (w.1.comap (toAff hc0).toRingHom) (qq (F := F) c) = _
      exact val_qq_in hc0 hc1 (hvin w) (hxin w)
    have hc0' : (‖c‖₊ : ℝ≥0) ≠ 0 := by simpa using hc0
    have hc1' : ‖c‖₊ ≤ 1 := by exact_mod_cast hc1.le
    have := hd v hv _ (by
      rw [hvq, hvx, max_eq_right (one_le_inv₀ (pos_iff_ne_zero.2 hc0') |>.2 hc1'),
        mul_inv_cancel₀ hc0']) M hM
    exact this
  refine isLocalIso_of _ _ _ _ hΛF hΛT (U1_mem hc1) ⟨hq, gnorm_le_iff.2 fun w' ↦ ?_⟩
    (fun f hf ↦ ?_) (fun g hg ↦ ?_) ?_ ?_
  · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [ιU_apply, val_qq_out hc1 (valuation_algebraMap_C' w) (valuation_xF w)]
    · rw [ιD_toTwoV]
      exact (val_qq_in hc0 hc1 (hvin w) (hxin w)).le.trans (by exact_mod_cast hc1.le)
  · -- forward
    have hf' : IsIntegral (Algebra.adjoin C {toTwoV c (xF C F)⁻¹}) (toTwoV c f) := hf.1
    obtain ⟨N₀, hN₀⟩ := ChartBounds.exists_pow_mul_isIntegral' (u := toTwoV c (qq (F := F) c))
      hq (by
        have key : qq (F := F) c * (xF C F)⁻¹ = tinv c := by
          have hx := xF_ne_zero (C := C) (F := F)
          have hD := Dn_ne_zero (F := F) (c := c)
          rw [qq, tinv]; field_simp
        rw [← map_mul, key, ← xF_twoV_inv]
        exact isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _)) hf'
    obtain ⟨d, hd⟩ := hbound f hf
    refine ⟨N₀ + (d + 1), ⟨?_, gnorm_le_iff.2 fun w' ↦ ?_⟩, fun w' hw' ↦ ?_⟩
    · rw [pow_add, mul_comm (_ ^ N₀), mul_assoc]
      exact (hq.pow _).mul hN₀
    · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · rw [← map_pow, ← map_mul, ιU_apply, map_mul, map_pow,
          val_qq_out hc1 (valuation_algebraMap_C' w) (valuation_xF w), one_pow, one_mul]
        exact (le_gnorm w f).trans hf.2
      · rw [← map_pow, ← map_mul]
        exact hd w _ (by omega)
    · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · exact absurd ⟨w, rfl⟩ hw'
      · have e : toTwoV c (qq (F := F) c) ^ (N₀ + (d + 1)) * toTwoV c f =
            toTwoV c (qq c) * toTwoV c (qq (F := F) c ^ (N₀ + d) * f) := by
          rw [← map_pow, ← map_mul, ← map_mul]; congr 1; ring
        rw [e, map_mul, ιD_toTwoV hc0 hc1 w (qq c)]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le
          ((val_qq_in hc0 hc1 (hvin w) (hxin w)).trans_lt (by exact_mod_cast hc1))
          (hd w _ (by omega))
  · -- backward
    have hg' : IsIntegral (Algebra.adjoin C {tinv (F := F) c}) ((toTwoV c).symm g) := by
      have := hg.1
      rw [xF_twoV_inv] at this
      exact this
    obtain ⟨N, hN⟩ := ChartBounds.exists_pow_mul_isIntegral (u := U1 (F := F) c)
      (S := Algebra.adjoin C {(xF C F)⁻¹}) U1_mem_adjoin (by
        have key : U1 (F := F) c * tinv c = (xF C F)⁻¹ := by
          have hx := xF_ne_zero (C := C) (F := F)
          have hD := Dn_ne_zero (F := F) (c := c)
          rw [U1, tinv, Dn]; field_simp
        rw [key]
        exact Algebra.self_mem_adjoin_singleton C _) hg'
    refine ⟨N, hN, gnorm_le_iff.2 fun w ↦ ?_⟩
    rw [map_mul, map_pow]
    refine mul_le_one' (pow_le_one₀ zero_le ((le_gnorm w _).trans (U1_mem hc1).2)) ?_
    rw [← ιU_apply hc0 hc1 w, RingEquiv.apply_symm_apply]
    exact (le_gnorm _ g).trans hg.2
  · intro w Q _ _
    change Q.valuation (red C (qq (F := F) c) w) = 1
    rw [red_qq_out hc1 w, Valuation.map_one]
  · intro w' Q _ hu
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · refine ⟨⟨w, rfl⟩, ?_⟩
      have : red C (toTwoV c (U1 (F := F) c)) (ιU hc0 hc1 w) = 1 := by
        refine red_eq_one_of ?_
        rw [← map_one (toTwoV c), ← map_sub, ιU_apply]
        exact val_U1_sub_one hc1 w
      rw [this, Valuation.map_one]
    · exfalso
      have hlt : (ιD hc0 hc1 w).1 (toTwoV c (qq (F := F) c)) < 1 := by
        rw [ιD_toTwoV]
        exact (val_qq_in hc0 hc1 (hvin w) (hxin w)).trans_lt (by exact_mod_cast hc1)
      rw [(red_eq_zero_iff hlt.le).2 hlt, map_zero] at hu
      exact zero_ne_one hu

end OuterInf

/-! ### The inner charts: `G` at `s` against `T` at `1/t` and at `t` -/

section Inner

variable [FiniteDimensional (RatFunc C) F] [CharZero C] {p : ℕ} (hp : p.Prime)
  (hp1 : ‖(p : C)‖ < 1) [Fintype (Ext C (Aff (0 : C) c hc0 F))] [Fintype (Ext C (TwoV c F))]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- `s = x/c`. -/
noncomputable abbrev sF (c : C) : F := algebraMap C F c⁻¹ * xF C F

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma xF_G : xF C (Aff (0 : C) c hc0 F) = toAff hc0 (sF (F := F) c) := by
  rw [xF_aff, gaussCoord_eq, map_zero, sub_zero, map_mul, ← IsScalarTower.algebraMap_apply]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma val_sF_in (w : Ext C (Aff (0 : C) c hc0 F)) : w.1 (toAff hc0 (sF (F := F) c)) = 1 := by
  rw [← xF_G, valuation_xF]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma val_sF_out (w : Ext C F) : w.1 (sF (F := F) c) = ‖c‖₊⁻¹ := by
  rw [sF, map_mul, valuation_algebraMap_C', valuation_xF, mul_one, nnnorm_inv]

/-- `1 + c s²`, a unit of the chart of `G` clearing the poles of `1/t`. -/
noncomputable abbrev U1G (c : C) : F := 1 + algebraMap C F c * sF c ^ 2

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma U1G_mem_adjoin :
    toAff hc0 (U1G (F := F) c) ∈ Algebra.adjoin C {xF C (Aff (0 : C) c hc0 F)} := by
  rw [xF_G]
  exact add_mem (one_mem _) (mul_mem (Subalgebra.algebraMap_mem _ c)
    (pow_mem (Algebra.self_mem_adjoin_singleton C _) 2))

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hc1 in
lemma val_U1G_sub_one (w : Ext C (Aff (0 : C) c hc0 F)) :
    w.1 (toAff hc0 (U1G (F := F) c - 1)) < 1 := by
  rw [U1G, add_sub_cancel_left, map_mul, map_mul, map_pow, map_pow, val_sF_in, one_pow, mul_one]
  change w.1 (algebraMap C _ c) < 1
  rw [valuation_algebraMap_C']
  exact_mod_cast hc1

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hc1 in
lemma U1G_mem : toAff hc0 (U1G (F := F) c) ∈
    intRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F)) := by
  refine ⟨isIntegral_of_mem (U1G_mem_adjoin hc0), gnorm_le_iff.2 fun w ↦ ?_⟩
  have : U1G (F := F) c = (U1G c - 1) + 1 := by ring
  rw [this, map_add, map_one]
  exact (Valuation.map_add _ _ _).trans (max_le (val_U1G_sub_one hc0 hc1 w).le (by rw [map_one]))

omit [CharZero C] [Fintype (GaussFibre.Ext C (TwoV c F))] [IsUltrametricDist C] in
lemma isIntegral_rr :
    IsIntegral (Algebra.adjoin C {(xF C (TwoV c F))⁻¹}) (toTwoV c (rr (F := F) c)) := by
  have h : rr (F := F) c = 1 - qq c := by
    have hD := Dn_ne_zero (F := F) (c := c)
    rw [rr, qq, eq_sub_iff_add_eq, ← add_div, Dn, add_comm, div_self hD]
  rw [h, map_sub, map_one]
  exact isIntegral_one.sub isIntegral_qq

omit [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hp hp1 hc1 in
/-- The outer bound for elements of the chart of `G`: an element of `O_C[s]` times a power of
`u` (with `|u| |s| ≤ 1` at the outer extensions) has value `≤ 1` there. -/
lemma exists_bound_outer {f : Aff (0 : C) c hc0 F}
    (hf : f ∈ intRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F))) {u : F}
    (hu : ∀ w : Ext C F, w.1 u = ‖c‖₊) :
    ∃ d : ℕ, ∀ (w : Ext C F) M, d ≤ M → (ιU hc0 hc1 w).1 (toTwoV c u ^ M * φG hc0 f) ≤ 1 := by
  have hfD := SmoothVertex.isIntegral_of_le hp hp1 hf.1 fun v ↦ (le_gnorm v f).trans hf.2
  obtain ⟨d, hd⟩ := ChartBounds.exists_pow_mul_le_one hfD
  refine ⟨d, fun w M hM ↦ ?_⟩
  set v : Valuation (Aff (0 : C) c hc0 F) ℝ≥0 := (ιU hc0 hc1 w).1.comap (φG hc0).toRingHom
  have hv (b : C) : v (algebraMap (RatFunc C) (Aff (0 : C) c hc0 F)
      (algebraMap C (RatFunc C) b)) ≤ ‖b‖₊ := by
    rw [← IsScalarTower.algebraMap_apply]
    change w.1 (algebraMap C F b) ≤ _
    rw [valuation_algebraMap_C']
  have hvs : v (xF C (Aff (0 : C) c hc0 F)) = ‖c‖₊⁻¹ := by
    rw [xF_G]
    exact val_sF_out (c := c) w
  have hc0' : (‖c‖₊ : ℝ≥0) ≠ 0 := by simpa using hc0
  have hc1' : ‖c‖₊ ≤ 1 := by exact_mod_cast hc1.le
  have hvu : v (toAff hc0 u) = ‖c‖₊ := hu w
  exact hd v hv (toAff hc0 u) (by
    rw [hvu, hvs, max_eq_right (one_le_inv₀ (pos_iff_ne_zero.2 hc0') |>.2 hc1'),
      mul_inv_cancel₀ hc0']) M hM

include hp hp1 in
/-- **The chart of `G` at `s = 0` and the inner chart of `T` at `t = ∞`** agree after inverting
`c/(x t)` (instance (I3) of the locality). -/
theorem isLocalIso_innerInf
    (hΛG : IsChart 𝓀 (fun w : Ext C (Aff (0 : C) c hc0 F) ↦ red C (xF C (Aff (0 : C) c hc0 F)) w)
      (redRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F))))
    (hΛT : IsChart 𝓀 (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F))⁻¹ w)
      (redRing C (TwoV c F) (xF C (TwoV c F))⁻¹)) :
    IsLocalIso hΛG hΛT (extEmb (φG hc0) (fun _ ↦ rfl) (ιD hc0 hc1) (ιD_apply hc0 hc1))
      (fun w ↦ red C (toAff hc0 (U1G (F := F) c)) w)
      (fun w' ↦ red C (toTwoV c (rr (F := F) c)) w') := by
  have hr := isIntegral_rr (C := C) (F := F) (c := c)
  have hvout (w : Ext C F) : ∀ b : C, w.1 (algebraMap C F b) = ‖b‖₊ := valuation_algebraMap_C' w
  have hvin (w : Ext C (Aff (0 : C) c hc0 F)) :
      ∀ b : C, (w.1.comap (toAff hc0).toRingHom) (algebraMap C F b) = ‖b‖₊ :=
    fun b ↦ val_toAff_C hc0 w b
  have hxin (w : Ext C (Aff (0 : C) c hc0 F)) :
      (w.1.comap (toAff hc0).toRingHom) (xF C F) = ‖c‖₊ := valuation_toAff_x hc0 w
  have hcF : algebraMap C F c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  refine isLocalIso_of _ _ _ _ hΛG hΛT (U1G_mem hc0 hc1) ⟨hr, gnorm_le_iff.2 fun w' ↦ ?_⟩
    (fun f hf ↦ ?_) (fun g hg ↦ ?_) ?_ ?_
  · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [ιU_apply, val_rr_out hc1 (hvout w) (valuation_xF w)]
      exact_mod_cast hc1.le
    · rw [ιD_toTwoV]
      exact (val_rr_in hc0 hc1 (hvin w) (hxin w)).le
  · -- forward
    have hf' : IsIntegral (Algebra.adjoin C {φG hc0 (toAff hc0 (sF (F := F) c))}) (φG hc0 f) := by
      have := hf.1
      rw [xF_G] at this
      exact this
    obtain ⟨N₀, hN₀⟩ := ChartBounds.exists_pow_mul_isIntegral' (u := toTwoV c (rr (F := F) c))
      hr (by
        have key : rr (F := F) c * sF c = tinv c := by
          have hx := xF_ne_zero (C := C) (F := F)
          have hD := Dn_ne_zero (F := F) (c := c)
          rw [rr, sF, tinv, map_inv₀]; field_simp
        have e : toTwoV c (rr (F := F) c) * φG hc0 (toAff hc0 (sF (F := F) c)) =
            (xF C (TwoV c F))⁻¹ := by
          rw [xF_twoV_inv, ← key]; rfl
        rw [e]
        exact isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _)) hf'
    obtain ⟨d, hd⟩ := exists_bound_outer hc0 hc1 hp hp1 hf (u := rr c) fun w ↦
      val_rr_out hc1 (hvout w) (valuation_xF w)
    refine ⟨N₀ + (d + 1), ⟨?_, gnorm_le_iff.2 fun w' ↦ ?_⟩, fun w' hw' ↦ ?_⟩
    · rw [pow_add, mul_comm (_ ^ N₀), mul_assoc]
      exact (hr.pow _).mul hN₀
    · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · exact hd w _ (by omega)
      · have hr1 : (ιD hc0 hc1 w).1 (toTwoV c (rr (F := F) c)) = 1 := by
          change (w.1.comap (toAff hc0).toRingHom) (rr (F := F) c) = 1
          exact val_rr_in hc0 hc1 (hvin w) (hxin w)
        rw [map_mul, map_pow, hr1, one_pow, one_mul, ιD_apply]
        exact (le_gnorm w f).trans hf.2
    · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · have e : toTwoV c (rr (F := F) c) ^ (N₀ + (d + 1)) * φG hc0 f =
            toTwoV c (rr c) * (toTwoV c (rr (F := F) c) ^ (N₀ + d) * φG hc0 f) := by ring
        rw [e, map_mul, ιU_apply]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le
          ((val_rr_out hc1 (hvout w) (valuation_xF w)).trans_lt (by exact_mod_cast hc1))
          (hd w _ (by omega))
      · exact absurd ⟨w, rfl⟩ hw'
  · -- backward
    have hg' : IsIntegral (Algebra.adjoin C {toAff (a := (0 : C)) hc0 (tinv (F := F) c)})
        ((φG hc0).symm g) := by
      have := hg.1
      rw [xF_twoV_inv] at this
      exact this
    obtain ⟨N, hN⟩ := ChartBounds.exists_pow_mul_isIntegral (u := toAff hc0 (U1G (F := F) c))
      (S := Algebra.adjoin C {xF C (Aff (0 : C) c hc0 F)}) (U1G_mem_adjoin hc0) (by
        have key : U1G (F := F) c * tinv c = sF c := by
          have hx := xF_ne_zero (C := C) (F := F)
          have hD := Dn_ne_zero (F := F) (c := c)
          rw [U1G, sF, tinv, Dn, map_inv₀]; field_simp; ring
        have e : toAff hc0 (U1G (F := F) c) * toAff (a := (0 : C)) hc0 (tinv (F := F) c) =
            xF C (Aff (0 : C) c hc0 F) := by
          rw [xF_G, ← key]; rfl
        rw [e]
        exact Algebra.self_mem_adjoin_singleton C _) hg'
    refine ⟨N, hN, gnorm_le_iff.2 fun w ↦ ?_⟩
    rw [map_mul, map_pow]
    refine mul_le_one' (pow_le_one₀ zero_le ((le_gnorm w _).trans (U1G_mem hc0 hc1).2)) ?_
    rw [← ιD_apply hc0 hc1 w, RingEquiv.apply_symm_apply]
    exact (le_gnorm _ g).trans hg.2
  · intro w Q _ _
    have : red C ((φG hc0).symm (toTwoV c (rr (F := F) c))) w = 1 := by
      refine red_eq_one_of ?_
      change (w.1.comap (toAff hc0).toRingHom) (rr (F := F) c - 1) < 1
      exact val_rr_sub_one_in hc0 hc1 (hvin w) (hxin w)
    rw [this, Valuation.map_one]
  · intro w' Q _ hu
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exfalso
      have hlt : (ιU hc0 hc1 w).1 (toTwoV c (rr (F := F) c)) < 1 := by
        rw [ιU_apply, val_rr_out hc1 (hvout w) (valuation_xF w)]
        exact_mod_cast hc1
      rw [(red_eq_zero_iff hlt.le).2 hlt, map_zero] at hu
      exact zero_ne_one hu
    · refine ⟨⟨w, rfl⟩, ?_⟩
      have : red C (φG hc0 (toAff hc0 (U1G (F := F) c))) (ιD hc0 hc1 w) = 1 := by
        refine red_eq_one_of ?_
        change w.1 (toAff hc0 (U1G (F := F) c - 1)) < 1
        exact val_U1G_sub_one hc0 hc1 w
      rw [this, Valuation.map_one]

/-- `c/x`. -/
noncomputable abbrev cxF (c : C) : F := algebraMap C F c / xF C F

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hc0 in
lemma cxF_mul_sF : cxF (F := F) c * sF c = 1 := by
  have hx := xF_ne_zero (C := C) (F := F)
  have hcF : algebraMap C F c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  rw [cxF, sF, map_inv₀]
  field_simp

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CharZero C]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma val_cxF_out (w : Ext C F) : w.1 (cxF (F := F) c) = ‖c‖₊ := by
  rw [cxF, map_div₀, valuation_algebraMap_C', valuation_xF, div_one]

omit [IsAlgClosed C] [CharZero C] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma val_cxF_in (w : Ext C (Aff (0 : C) c hc0 F)) : w.1 (toAff hc0 (cxF (F := F) c)) = 1 := by
  have h := congrArg w.1 (congrArg (toAff hc0) (cxF_mul_sF hc0 (F := F)))
  rw [map_one, map_one, map_mul, map_mul, val_sF_in, mul_one] at h
  exact h

omit [IsUltrametricDist C] [CharZero C] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma isIntegral_cxF :
    IsIntegral (Algebra.adjoin C {xF C (TwoV c F)}) (toTwoV c (cxF (F := F) c)) := by
  have h : toTwoV c (cxF (F := F) c) = xF C (TwoV c F) - toTwoV c (xF C F) := by
    rw [xF_twoV', ← map_sub, add_sub_cancel_left]
  rw [h]
  exact (isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _)).sub isIntegral_xT

omit [IsAlgClosed C] [CharZero C] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
/-- In the residue field, `(c/x)‾ (x/c)‾ = 1` at inner extensions. -/
lemma red_cxF_mul_red_sF (w : Ext C (Aff (0 : C) c hc0 F)) :
    red C (toAff hc0 (cxF (F := F) c)) w * red C (toAff hc0 (sF (F := F) c)) w = 1 := by
  rw [← red_mul (val_cxF_in hc0 w).le (val_sF_in hc0 w).le, ← map_mul, cxF_mul_sF hc0, map_one,
    red_one]

include hp hp1 in
/-- **The chart of `G` at `s` and the inner finite chart of `T`** agree after inverting `s̄`
(resp. `(c/x)‾ = s̄⁻¹`) (instance (I4) of the locality). -/
theorem isLocalIso_innerMid
    (hΛG : IsChart 𝓀 (fun w : Ext C (Aff (0 : C) c hc0 F) ↦ red C (xF C (Aff (0 : C) c hc0 F)) w)
      (redRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F))))
    (hΛT : IsChart 𝓀 (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F)) w)
      (redRing C (TwoV c F) (xF C (TwoV c F)))) :
    IsLocalIso hΛG hΛT (extEmb (φG hc0) (fun _ ↦ rfl) (ιD hc0 hc1) (ιD_apply hc0 hc1))
      (fun w ↦ red C (xF C (Aff (0 : C) c hc0 F)) w)
      (fun w' ↦ red C (toTwoV c (cxF (F := F) c)) w') := by
  have hcx := isIntegral_cxF (C := C) (F := F) (c := c)
  have hc1' : ‖c‖₊ < 1 := by exact_mod_cast hc1
  refine isLocalIso_of _ _ _ _ hΛG hΛT
    ⟨isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _),
      gnorm_le_iff.2 fun w ↦ (valuation_xF w).le⟩
    ⟨hcx, gnorm_le_iff.2 fun w' ↦ ?_⟩ (fun f hf ↦ ?_) (fun g hg ↦ ?_) ?_ ?_
  · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [ιU_apply, val_cxF_out]; exact hc1'.le
    · rw [ιD_toTwoV, val_cxF_in]
  · -- forward
    have hf' : IsIntegral (Algebra.adjoin C {φG hc0 (toAff hc0 (sF (F := F) c))}) (φG hc0 f) := by
      have := hf.1
      rw [xF_G] at this
      exact this
    obtain ⟨N₀, hN₀⟩ := ChartBounds.exists_pow_mul_isIntegral' (u := toTwoV c (cxF (F := F) c))
      hcx (by
        have e : toTwoV c (cxF (F := F) c) * φG hc0 (toAff hc0 (sF (F := F) c)) = 1 := by
          change toTwoV c (cxF (F := F) c * sF c) = 1
          rw [cxF_mul_sF hc0, map_one]
        rw [e]
        exact isIntegral_one) hf'
    obtain ⟨d, hd⟩ := exists_bound_outer hc0 hc1 hp hp1 hf (u := cxF c) fun w ↦ val_cxF_out w
    refine ⟨N₀ + (d + 1), ⟨?_, gnorm_le_iff.2 fun w' ↦ ?_⟩, fun w' hw' ↦ ?_⟩
    · rw [pow_add, mul_comm (_ ^ N₀), mul_assoc]
      exact (hcx.pow _).mul hN₀
    · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · exact hd w _ (by omega)
      · rw [map_mul, map_pow, ιD_toTwoV, val_cxF_in, one_pow, one_mul, ιD_apply]
        exact (le_gnorm w f).trans hf.2
    · rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · have e : toTwoV c (cxF (F := F) c) ^ (N₀ + (d + 1)) * φG hc0 f =
            toTwoV c (cxF c) * (toTwoV c (cxF (F := F) c) ^ (N₀ + d) * φG hc0 f) := by ring
        rw [e, map_mul, ιU_apply]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le
          ((val_cxF_out w).trans_lt hc1') (hd w _ (by omega))
      · exact absurd ⟨w, rfl⟩ hw'
  · -- backward
    have hg' : IsIntegral (Algebra.adjoin C {toAff (a := (0 : C)) hc0
        (xF C F + algebraMap C F c / xF C F)}) ((φG hc0).symm g) := by
      have := hg.1
      rw [xF_twoV'] at this
      exact this
    obtain ⟨N, hN⟩ := ChartBounds.exists_pow_mul_isIntegral
      (u := toAff (a := (0 : C)) hc0 (sF (F := F) c))
      (S := Algebra.adjoin C {xF C (Aff (0 : C) c hc0 F)})
      (by rw [xF_G]; exact Algebra.self_mem_adjoin_singleton C _) (by
        have key : sF (F := F) c * (xF C F + algebraMap C F c / xF C F) =
            algebraMap C F c * sF c ^ 2 + 1 := by
          have hx := xF_ne_zero (C := C) (F := F)
          have hcF : algebraMap C F c ≠ 0 := (_root_.map_ne_zero _).2 hc0
          rw [sF, map_inv₀]; field_simp
        have e : toAff hc0 (sF (F := F) c) *
            toAff (a := (0 : C)) hc0 (xF C F + algebraMap C F c / xF C F) =
            algebraMap C _ c * xF C (Aff (0 : C) c hc0 F) ^ 2 + 1 := by
          rw [xF_G, ← map_mul, key]; rfl
        rw [e]
        exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ c)
          (pow_mem (Algebra.self_mem_adjoin_singleton C _) 2)) (one_mem _)) hg'
    rw [← xF_G] at hN
    refine ⟨N, hN, gnorm_le_iff.2 fun w ↦ ?_⟩
    rw [map_mul, map_pow, xF_G, val_sF_in, one_pow, one_mul, ← ιD_apply hc0 hc1 w,
      RingEquiv.apply_symm_apply]
    exact (le_gnorm _ g).trans hg.2
  · intro w Q _ hu
    have h := congrArg Q.valuation (red_cxF_mul_red_sF hc0 w)
    rw [map_mul, Valuation.map_one, ← xF_G, hu, mul_one] at h
    exact h
  · intro w' Q _ hu
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exfalso
      have hlt : (ιU hc0 hc1 w).1 (toTwoV c (cxF (F := F) c)) < 1 := by
        rw [ιU_apply, val_cxF_out]; exact hc1'
      rw [(red_eq_zero_iff hlt.le).2 hlt, map_zero] at hu
      exact zero_ne_one hu
    · refine ⟨⟨w, rfl⟩, ?_⟩
      have h1 : (ιD hc0 hc1 w).1 (toTwoV c (cxF (F := F) c)) = 1 := by
        rw [ιD_toTwoV, val_cxF_in]
      have h2 : (ιD hc0 hc1 w).1 (φG hc0 (xF C (Aff (0 : C) c hc0 F))) = 1 := by
        rw [ιD_apply, valuation_xF]
      have h : red C (toTwoV c (cxF (F := F) c)) (ιD hc0 hc1 w) *
          red C (φG hc0 (xF C (Aff (0 : C) c hc0 F))) (ιD hc0 hc1 w) = 1 := by
        rw [← red_mul h1.le h2.le]
        have e : toTwoV c (cxF (F := F) c) * φG hc0 (xF C (Aff (0 : C) c hc0 F)) = 1 := by
          rw [xF_G]
          change toTwoV c (cxF (F := F) c * sF c) = 1
          rw [cxF_mul_sF hc0, map_one]
        rw [e, red_one]
      have h' := congrArg Q.valuation h
      rw [map_mul, Valuation.map_one, hu, one_mul] at h'
      exact h'

end Inner

end TwoVertexCharts

end SemistableReduction
