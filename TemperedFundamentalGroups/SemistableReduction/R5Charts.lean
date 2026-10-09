/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhaustDescent

/-!
# Invariants of a residue ball and of a disc under changes of representative

Blueprint §9.12, O6.2 (R5). For a change of coordinates `x₂ = φ (u x₁ + β)` (`|u| = 1`, `|β| ≤ 1`)
preserving the Gauss point (`ChartChange`), the numbers of branches over `x̄ = ∞` (`ic`) agree, and
for `|β| < 1` also the numbers of branches over `x̄ = 0` (`mm`) and the total `δ` over `x̄ = 0`
(`tot0_xbar_eq`). Instance: two representatives `(a, c)`, `(a', c')` of the same disc
(`repφ`, `|c| = |c'|`, `|a - a'| ≤ |c|`) resp. of the same open ball (`|a - a'| < |c|`).
-/

open Polynomial IsLocalRing WithZero Metric
open scoped NNReal

namespace SemistableReduction

namespace R5Measure

open GaussFibre ChartLocal DeltaCount FundamentalInequality GaussStability AffineTwist
  TwoVertex NodeBridge ChartChange LocalFormula ExhaustGluing ExhaustDescent

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

section Rep

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0)

/-- The change of coordinates `(x - a)/c ↦ (x - a')/c'` of `C(x)`. -/
noncomputable def repσ (a a' : C) {c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    RatFunc C ≃ₐ[C] RatFunc C :=
  (aff a' c' hc').trans (aff a c hc).symm

/-- The identity of `F` from the twist `Aff a c F` to the twist `Aff a' c' F`. -/
noncomputable def repφ (a a' : C) {c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    Aff a c hc F ≃+* Aff a' c' hc' F :=
  (toAff hc).symm.trans (toAff hc')

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma repφ_he (ψ : RatFunc C) :
    repφ (F := F) a a' hc hc' (algebraMap (RatFunc C) (Aff a c hc F) (repσ a a' hc hc' ψ)) =
      algebraMap (RatFunc C) (Aff a' c' hc' F) ψ := by
  change toAff hc' (algebraMap (RatFunc C) F (aff a c hc ((aff a c hc).symm (aff a' c' hc' ψ))))
    = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

lemma repσ_gauss (h1 : ‖c‖ = ‖c'‖) (h2 : ‖a - a'‖ ≤ ‖c‖) (ψ : RatFunc C) :
    gauss1 C (repσ a a' hc hc' ψ) = gauss1 C ψ := by
  change gauss1 C ((aff a c hc).symm (aff a' c' hc' ψ)) = gauss1 C ψ
  rw [gauss1_aff_symm hc, ← gaussRat_aff (a := a') hc' ψ]
  have hr : Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc) =
      Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc') := Units.ext (NNReal.eq (by simpa using h1))
  have hle : NormedField.valuation (a - a') ≤
      ((Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc') : ℝ≥0ˣ) : ℝ≥0) := by
    rw [NormedField.valuation_apply, Units.val_mk0]
    exact_mod_cast (show ‖a - a'‖ ≤ ‖c'‖ from h1 ▸ h2)
  rw [hr, Splitting.gaussRat_eq_of_le hle]

omit [IsAlgClosed C] in
lemma repφ_x :
    xF C (Aff a' c' hc' F) = repφ (F := F) a a' hc hc'
      (algebraMap C (Aff a c hc F) (c / c') * xF C (Aff a c hc F) +
        algebraMap C (Aff a c hc F) ((a - a') / c')) := by
  rw [xF_aff, xF_aff]
  change algebraMap (RatFunc C) F (gaussCoord a' c') =
    algebraMap C F (c / c') * algebraMap (RatFunc C) F (gaussCoord a c) +
      algebraMap C F ((a - a') / c')
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) F,
    IsScalarTower.algebraMap_apply C (RatFunc C) F,
    ← map_mul, ← map_add]
  congr 1
  rw [gaussCoord_eq, gaussCoord_eq]
  have h0 : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
  have h0' : algebraMap C (RatFunc C) c' ≠ 0 := by simpa using hc'
  simp only [map_inv₀, map_div₀, map_sub]
  field_simp
  ring

end Rep

section Zeros

variable {κ : Type*} [Field κ] [Algebra (IsLocalRing.ResidueField (HenselComplete.integers C)) κ]
  [IsCurveFunctionField (IsLocalRing.ResidueField (HenselComplete.integers C)) κ]

lemma zeros_inv_lin {k₁ : 𝓀} (k₀ : 𝓀) (hk : k₁ ≠ 0) (f : κ) :
    PlaceNorm.zeros 𝓀 (algebraMap 𝓀 κ k₁ * f + algebraMap 𝓀 κ k₀)⁻¹ =
      PlaceNorm.zeros 𝓀 f⁻¹ := by
  ext Q
  rw [PlaceNorm.mem_zeros, PlaceNorm.mem_zeros, inv_inv, inv_inv, not_iff_not]
  constructor
  · intro h
    have e : f = algebraMap 𝓀 κ k₁⁻¹ * ((algebraMap 𝓀 κ k₁ * f + algebraMap 𝓀 κ k₀) -
        algebraMap 𝓀 κ k₀) := by
      rw [add_sub_cancel_right, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
    rw [e]
    exact mul_mem (Q.algebraMap_mem _) (sub_mem h (Q.algebraMap_mem _))
  · intro h
    exact add_mem (mul_mem (Q.algebraMap_mem _) h) (Q.algebraMap_mem _)

lemma zeros_smul {k₁ : 𝓀} (hk : k₁ ≠ 0) (f : κ) :
    PlaceNorm.zeros 𝓀 (algebraMap 𝓀 κ k₁ * f) = PlaceNorm.zeros 𝓀 f := by
  ext Q
  rw [PlaceNorm.mem_zeros, PlaceNorm.mem_zeros, not_iff_not, mul_inv, ← map_inv₀]
  constructor
  · intro h
    have e : f⁻¹ = algebraMap 𝓀 κ k₁ * (algebraMap 𝓀 κ k₁⁻¹ * f⁻¹) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hk, map_one, one_mul]
    rw [e]
    exact mul_mem (Q.algebraMap_mem _) h
  · intro h
    exact mul_mem (Q.algebraMap_mem _) h

end Zeros

/-! ### Invariants along a change of coordinates -/

section Invariance

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra (RatFunc C) K₁] [Algebra (RatFunc C) K₂]
  (σ : RatFunc C ≃ₐ[C] RatFunc C) (hσ : ∀ ψ, gauss1 C (σ ψ) = gauss1 C ψ) (φ : K₁ ≃+* K₂)
  (he : ∀ ψ, φ (algebraMap (RatFunc C) K₁ (σ ψ)) = algebraMap (RatFunc C) K₂ ψ)
  [Algebra C K₁] [IsScalarTower C (RatFunc C) K₁] [Algebra C K₂]
  [IsScalarTower C (RatFunc C) K₂]
  {u β : C} (hu : ‖u‖ = 1) (hβ : ‖β‖ ≤ 1)
  (hx : xF C K₂ = φ (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β))

omit [IsAlgClosed C] [IsUltrametricDist C] in
lemma nnnorm_le_one_of_eq {u : C} (hu : ‖u‖ = 1) : ‖u‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, hu]; rfl

include hu hβ in
omit [IsAlgClosed C] in
lemma red_lin (w : Ext C K₁) :
    red C (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β) w =
      algebraMap 𝓀 _ (residue (HenselComplete.integers C)
        ⟨u, (HenselComplete.mem_integers_iff _).2 hu.le⟩) *
        red C (xF C K₁) w +
      algebraMap 𝓀 _ (residue (HenselComplete.integers C)
        ⟨β, (HenselComplete.mem_integers_iff _).2 hβ⟩) := by
  have hu' : ‖u‖₊ ≤ 1 := nnnorm_le_one_of_eq hu
  have hβ' : ‖β‖₊ ≤ 1 := by exact_mod_cast hβ
  rw [red_add (by rw [map_mul, valuation_algebraMap_C', valuation_xF, mul_one]; exact hu')
    (by rw [valuation_algebraMap_C']; exact hβ'),
    red_mul (by rw [valuation_algebraMap_C']; exact hu') (valuation_xF w).le,
    red_algebraMap_C u hu', red_algebraMap_C β hβ']

omit [IsAlgClosed C] in
lemma residue_ne_zero_of_norm_eq_one (hu : ‖u‖ = 1) :
    residue (HenselComplete.integers C) ⟨u, (HenselComplete.mem_integers_iff _).2 hu.le⟩ ≠ 0 := by
  rw [Ne, residue_eq_zero_iff]
  intro h
  have := (HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).1 h
  simp [hu] at this

omit [IsAlgClosed C] in
lemma algebraMap_mem_intRing {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
    [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)] {u : C}
    (hu : ‖u‖ ≤ 1) :
    algebraMap C K u ∈ intRing C K (xF C K) := by
  refine ⟨TwoVertexCharts.isIntegral_of_mem (Subalgebra.algebraMap_mem _ u),
    gnorm_le_iff.2 fun w ↦ ?_⟩
  rw [valuation_algebraMap_C']
  exact_mod_cast hu

include hu hβ in
omit [IsAlgClosed C] in
lemma lin_mem_intRing [FiniteDimensional (RatFunc C) K₁] [Fintype (Ext C K₁)] :
    algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β ∈ intRing C K₁ (xF C K₁) :=
  add_mem (mul_mem (algebraMap_mem_intRing hu.le)
    ⟨TwoVertexCharts.isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _),
      gnorm_le_iff.2 fun w ↦ (valuation_xF w).le⟩) (algebraMap_mem_intRing hβ)

omit [IsAlgClosed C] in
lemma residue_eq_zero_of_norm_lt_one {β : C} (hβ1 : ‖β‖ < 1) :
    residue (HenselComplete.integers C) ⟨β, (HenselComplete.mem_integers_iff _).2 hβ1.le⟩ = 0 :=
  (residue_eq_zero_iff _).2 ((HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).2 hβ1)

variable [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂]

include σ hσ φ he hu hβ hx in
lemma card_zeros_inv_x (w : Ext C K₁) :
    (PlaceNorm.zeros 𝓀 (red C (xF C K₂) (extEquiv σ hσ φ he w))⁻¹).card =
      (PlaceNorm.zeros 𝓀 (red C (xF C K₁) w)⁻¹).card := by
  rw [hx, ← resEq_red σ hσ φ he, ← map_inv₀, card_zeros_map, red_lin hu hβ,
    zeros_inv_lin _ (residue_ne_zero_of_norm_eq_one hu)]

include σ hσ φ he hu hx in
lemma card_zeros_x (hβ1 : ‖β‖ < 1) (w : Ext C K₁) :
    (PlaceNorm.zeros 𝓀 (red C (xF C K₂) (extEquiv σ hσ φ he w))).card =
      (PlaceNorm.zeros 𝓀 (red C (xF C K₁) w)).card := by
  rw [hx, ← resEq_red σ hσ φ he, card_zeros_map, red_lin hu hβ1.le,
    residue_eq_zero_of_norm_lt_one hβ1, map_zero, add_zero,
    zeros_smul (residue_ne_zero_of_norm_eq_one hu)]

lemma genus_ext (w : Ext C K₁) :
    genus 𝓀 (IsLocalRing.ResidueField (extEquiv σ hσ φ he w).1.valuationSubring) =
      genus 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring) :=
  CurvePlace.genus_congr (resEq σ hσ φ he w)

end Invariance

section Counts

variable (K : Type*) [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]

variable (C) in
/-- The number of branches over `x̄ = 0` (the zeros of `x̄` on the residue curves). -/
noncomputable def mm : ℕ := ∑ w : Ext C K, (PlaceNorm.zeros 𝓀 (red C (xF C K) w)).card

variable (C) in
/-- The number of branches over `x̄ = ∞`. -/
noncomputable def ic : ℕ := ∑ w : Ext C K, (PlaceNorm.zeros 𝓀 (red C (xF C K) w)⁻¹).card

end Counts

section InvarianceSums

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra (RatFunc C) K₁] [Algebra (RatFunc C) K₂]
  (σ : RatFunc C ≃ₐ[C] RatFunc C) (hσ : ∀ ψ, gauss1 C (σ ψ) = gauss1 C ψ) (φ : K₁ ≃+* K₂)
  (he : ∀ ψ, φ (algebraMap (RatFunc C) K₁ (σ ψ)) = algebraMap (RatFunc C) K₂ ψ)
  [Algebra C K₁] [IsScalarTower C (RatFunc C) K₁] [Algebra C K₂]
  [IsScalarTower C (RatFunc C) K₂]
  {u β : C} (hu : ‖u‖ = 1) (hβ : ‖β‖ ≤ 1)
  (hx : xF C K₂ = φ (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β))
  [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂]
  [Fintype (Ext C K₁)] [Fintype (Ext C K₂)]

include σ hσ φ he hu hβ hx in
lemma ic_eq : ic C K₂ = ic C K₁ := by
  rw [ic, ic, ← (extEquiv σ hσ φ he).sum_comp]
  exact Finset.sum_congr rfl fun w _ ↦ card_zeros_inv_x σ hσ φ he hu hβ hx w

include σ hσ φ he hu hx in
lemma mm_eq (hβ1 : ‖β‖ < 1) : mm C K₂ = mm C K₁ := by
  rw [mm, mm, ← (extEquiv σ hσ φ he).sum_comp]
  exact Finset.sum_congr rfl fun w _ ↦ card_zeros_x σ hσ φ he hu hx hβ1 w

omit [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂] in
lemma tot0_congr {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
    [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]
    (hΛ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)))
    {P Q : Ideal (redRing C K (xF C K)) → Prop} (h : ∀ 𝔫, 𝔫.IsMaximal → (P 𝔫 ↔ Q 𝔫)) :
    tot0 C K hΛ P = tot0 C K hΛ Q := by
  have : {𝔫 : Ideal (redRing C K (xF C K)) | 𝔫.IsMaximal ∧ P 𝔫} =
      {𝔫 | 𝔫.IsMaximal ∧ Q 𝔫} := by
    ext 𝔫
    exact ⟨fun h' ↦ ⟨h'.1, (h 𝔫 h'.1).1 h'.2⟩, fun h' ↦ ⟨h'.1, (h 𝔫 h'.1).2 h'.2⟩⟩
  rw [tot0, tot0, this]

include σ hσ φ he hu hx in
/-- **`δ` over the residue point** along a change of coordinates within the open disc. -/
lemma tot0_xbar_eq (hβ1 : ‖β‖ < 1)
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂))) :
    tot0 C K₂ hΛ₂ (fun 𝔫 ↦ DiscBridge.xbar hΛ₂ ∈ 𝔫) =
      tot0 C K₁ hΛ₁ (fun 𝔫 ↦ DiscBridge.xbar hΛ₁ ∈ 𝔫) := by
  have hg := lin_mem_intRing hu hβ1.le (K₁ := K₁)
  rw [tot0_x_eq σ hσ φ he hu hx hΛ₁ hΛ₂ hg]
  refine tot0_congr hΛ₁ fun 𝔫 h𝔫 ↦ ?_
  set U : redRing C K₁ (xF C K₁) :=
    ⟨fun w ↦ red C (algebraMap C K₁ u) w, red_mem_redRing (algebraMap_mem_intRing hu.le)⟩
  have hu' : ‖u⁻¹‖ ≤ 1 := by rw [norm_inv, hu, inv_one]
  set U' : redRing C K₁ (xF C K₁) :=
    ⟨fun w ↦ red C (algebraMap C K₁ u⁻¹) w, red_mem_redRing (algebraMap_mem_intRing hu')⟩
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hUU : U * U' = 1 := by
    apply Subtype.ext
    funext w
    change red C (algebraMap C K₁ u) w * red C (algebraMap C K₁ u⁻¹) w = 1
    rw [← red_mul (by rw [valuation_algebraMap_C']; exact nnnorm_le_one_of_eq hu)
      (by rw [valuation_algebraMap_C']; exact_mod_cast hu'), ← map_mul, mul_inv_cancel₀ hu0,
      map_one, red_one]
  have hU : IsUnit U := IsUnit.of_mul_eq_one _ hUU
  have e : (⟨fun w ↦ red C (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β) w,
      red_mem_redRing hg⟩ : redRing C K₁ (xF C K₁)) = U * DiscBridge.xbar hΛ₁ := by
    apply Subtype.ext
    funext w
    change red C (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β) w =
      red C (algebraMap C K₁ u) w * red C (xF C K₁) w
    have hβ' : ‖β‖₊ ≤ 1 := by exact_mod_cast hβ1.le
    have h1 : w.1 (algebraMap C K₁ u) ≤ 1 := by
      rw [valuation_algebraMap_C']; exact nnnorm_le_one_of_eq hu
    have h2 : w.1 (algebraMap C K₁ u * xF C K₁) ≤ 1 := by
      rw [map_mul, valuation_xF, mul_one]; exact h1
    have h3 : w.1 (algebraMap C K₁ β) ≤ 1 := by rw [valuation_algebraMap_C']; exact hβ'
    rw [red_add h2 h3, red_mul h1 (valuation_xF w).le, red_algebraMap_C β hβ',
      residue_eq_zero_of_norm_lt_one hβ1, map_zero, add_zero]
  rw [e]
  exact Ideal.unit_mul_mem_iff_mem _ hU

end InvarianceSums

section Norms

omit [IsAlgClosed C] [IsUltrametricDist C]

lemma norm_u_eq {c c' : C} (hc' : c' ≠ 0) (h1 : ‖c‖ = ‖c'‖) : ‖c / c'‖ = 1 := by
  rw [norm_div, h1, div_self (norm_ne_zero_iff.2 hc')]

lemma norm_β_le {a a' c c' : C} (hc' : c' ≠ 0) (h1 : ‖c‖ = ‖c'‖) (h2 : ‖a - a'‖ ≤ ‖c‖) :
    ‖(a - a') / c'‖ ≤ 1 := by
  rw [norm_div, div_le_one (norm_pos_iff.2 hc'), ← h1]; exact h2

lemma norm_β_lt {a a' c c' : C} (hc' : c' ≠ 0) (h1 : ‖c‖ = ‖c'‖) (h2 : ‖a - a'‖ < ‖c‖) :
    ‖(a - a') / c'‖ < 1 := by
  rw [norm_div, div_lt_one (norm_pos_iff.2 hc'), ← h1]; exact h2

end Norms

/-! ### Changes of representative of a disc -/

section TwistInv

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) (h1 : ‖c‖ = ‖c'‖)

variable [Fintype (Ext C (Aff a c hc F))] [Fintype (Ext C (Aff a' c' hc' F))]
  (h2 : ‖a - a'‖ ≤ ‖c‖)

include h1 h2

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
lemma card_ext_aff :
    Fintype.card (Ext C (Aff a' c' hc' F)) = Fintype.card (Ext C (Aff a c hc F)) :=
  (card_ext_eq (repσ a a' hc hc') (repσ_gauss hc hc' h1 h2) (repφ (F := F) a a' hc hc')
    (repφ_he hc hc')).symm

lemma gsum_aff : gsum C (Aff a' c' hc' F) = gsum C (Aff a c hc F) :=
  (gsum_eq (repσ a a' hc hc') (repσ_gauss hc hc' h1 h2) (repφ (F := F) a a' hc hc')
    (repφ_he hc hc')).symm

lemma ic_aff : ic C (Aff a' c' hc' F) = ic C (Aff a c hc F) :=
  ic_eq (repσ a a' hc hc') (repσ_gauss hc hc' h1 h2) (repφ (F := F) a a' hc hc')
    (repφ_he hc hc') (norm_u_eq hc' h1) (norm_β_le hc' h1 h2) (repφ_x hc hc')

lemma tot0_true_aff
    (hΛ : IsChart 𝓀 (fun w : Ext C (Aff a c hc F) ↦ red C (xF C (Aff a c hc F)) w)
      (redRing C _ (xF C (Aff a c hc F))))
    (hΛ' : IsChart 𝓀 (fun w : Ext C (Aff a' c' hc' F) ↦ red C (xF C (Aff a' c' hc' F)) w)
      (redRing C _ (xF C (Aff a' c' hc' F)))) :
    tot0 C _ hΛ' (fun _ ↦ True) = tot0 C _ hΛ (fun _ ↦ True) :=
  tot0_true_eq (repσ a a' hc hc') (repσ_gauss hc hc' h1 h2) (repφ (F := F) a a' hc hc')
    (repφ_he hc hc') (norm_u_eq hc' h1) (repφ_x hc hc') hΛ hΛ'

omit [Fintype (Ext C (Aff a c hc F))] [Fintype (Ext C (Aff a' c' hc' F))] in
/-- A disc of a tube does not depend on the representative. -/
lemma isTubeDisc_aff (h : IsTubeDisc F a hc) : IsTubeDisc F a' hc' := by
  intro w'
  obtain ⟨w, rfl⟩ := (extEquiv (repσ a a' hc hc') (repσ_gauss hc hc' h1 h2)
    (repφ (F := F) a a' hc hc') (repφ_he hc hc')).surjective w'
  rw [genus_ext, card_zeros_inv_x _ _ _ _ (norm_u_eq hc' h1) (norm_β_le hc' h1 h2)
    (repφ_x hc hc')]
  exact h w

end TwistInv

section TwistInvOpen

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) (h1 : ‖c‖ = ‖c'‖) (h2 : ‖a - a'‖ < ‖c‖)
include h1 h2

lemma mm_aff [Fintype (Ext C (Aff a c hc F))] [Fintype (Ext C (Aff a' c' hc' F))] :
    mm C (Aff a' c' hc' F) = mm C (Aff a c hc F) :=
  mm_eq (repσ a a' hc hc') (repσ_gauss hc hc' h1 h2.le) (repφ (F := F) a a' hc hc')
    (repφ_he hc hc') (norm_u_eq hc' h1) (repφ_x hc hc') (norm_β_lt hc' h1 h2)

lemma tot0_xbar_aff [Fintype (Ext C (Aff a c hc F))] [Fintype (Ext C (Aff a' c' hc' F))]
    (hΛ : IsChart 𝓀 (fun w : Ext C (Aff a c hc F) ↦ red C (xF C (Aff a c hc F)) w)
      (redRing C _ (xF C (Aff a c hc F))))
    (hΛ' : IsChart 𝓀 (fun w : Ext C (Aff a' c' hc' F) ↦ red C (xF C (Aff a' c' hc' F)) w)
      (redRing C _ (xF C (Aff a' c' hc' F)))) :
    tot0 C _ hΛ' (fun 𝔫 ↦ DiscBridge.xbar hΛ' ∈ 𝔫) =
      tot0 C _ hΛ (fun 𝔫 ↦ DiscBridge.xbar hΛ ∈ 𝔫) :=
  tot0_xbar_eq (repσ a a' hc hc') (repσ_gauss hc hc' h1 h2.le) (repφ (F := F) a a' hc hc')
    (repφ_he hc hc') (norm_u_eq hc' h1) (repφ_x hc hc') (norm_β_lt hc' h1 h2) hΛ hΛ'

lemma card_zeros_aff (w : Ext C (Aff a c hc F)) :
    (PlaceNorm.zeros 𝓀 (red C (xF C (Aff a' c' hc' F)) (extEquiv (repσ a a' hc hc')
      (repσ_gauss hc hc' h1 h2.le) (repφ (F := F) a a' hc hc') (repφ_he hc hc') w))).card =
      (PlaceNorm.zeros 𝓀 (red C (xF C (Aff a c hc F)) w)).card :=
  card_zeros_x _ _ _ _ (norm_u_eq hc' h1) (repφ_x hc hc') (norm_β_lt hc' h1 h2) w

end TwistInvOpen

end R5Measure

end SemistableReduction
