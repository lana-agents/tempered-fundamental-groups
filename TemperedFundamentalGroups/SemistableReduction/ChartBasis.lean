/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SpecialFibre

/-!
# Bases of the affine charts of the special fibre

Blueprint §9.9, S7⁺.1–S7⁺.3. Let `ζ ∈ {X, X⁻¹}` be a *coordinate* of `C(X)` (`IsCoord`) and
`z ∈ F` its image. The chart ring `intRing z` (elements of `F` of norm `≤ 1` integral over `C[z]`)
reduces to `Λ = redRing z ⊆ Π_w κ(w)`.

* S7⁺.1 `exists_trace_bound`: for an integral orthonormal basis `d` there is `Δ ∈ C[X]` of Gauss
  norm `1` with `Δ(ζ) φᵢ = Pᵢ(ζ)`, `‖Pᵢ‖ ≤ 1`, for the coordinates `φ` of every element of the
  chart ring (trace form, `char C = 0`);
* S7⁺.2 `exists_chartBasis`: there are `sᵢ ∈ intRing z` whose reductions are a `k[z̄]`-basis of
  `Λ` (a submodule of a free module over the PID `k[X]`), and the `sᵢ` are an orthonormal
  `C(X)`-basis of `F`;
* S7⁺.3 `exists_disc_coords`: the coordinates of every element of `intRing z` in the basis `s`
  have no poles in the closed unit disc (fibre argument).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion CurvePlace

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "vC" => NormedField.valuation (K := C)

section Coord

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F]

variable (F) in
/-- A *coordinate* `ζ` of `C(X)` relative to `F`: polynomials in `ζ` have the Gauss norm of their
coefficients, `C(X) = C(ζ)`, traces of elements integral over `C[ζ]` are polynomials in `ζ`, and
every element of `F` has a multiple integral over `C[ζ]`. Instances: `X` and `X⁻¹`. -/
structure IsCoord (ζ : RatFunc C) : Prop where
  gauss : ∀ P : C[X], gauss1 C (aeval ζ P) = Gauss.sup vC 1 P
  frac : ∀ φ : RatFunc C, ∃ p q : C[X], q ≠ 0 ∧ aeval ζ q * φ = aeval ζ p
  trace : ∀ f : F, IsIntegral (Algebra.adjoin C {algebraMap (RatFunc C) F ζ}) f →
    ∃ Q : C[X], Algebra.trace (RatFunc C) F f = aeval ζ Q
  mul_integral : ∀ f : F, ∃ P : C[X], P ≠ 0 ∧
    IsIntegral (Algebra.adjoin C {algebraMap (RatFunc C) F ζ}) (aeval (algebraMap _ F ζ) P * f)

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField_F

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma aeval_X_ratFunc (P : C[X]) : aeval (RatFunc.X : RatFunc C) P = algebraMap C[X] _ P :=
  RatFunc.aeval_X_left_eq_algebraMap P

/-- `X` is a coordinate. -/
theorem isCoord_X : IsCoord F (RatFunc.X : RatFunc C) where
  gauss P := by rw [aeval_X_ratFunc, gauss1_algebraMap]
  frac φ := ⟨φ.num, φ.denom, φ.denom_ne_zero, by
    rw [aeval_X_ratFunc, aeval_X_ratFunc, mul_comm, ← eq_div_iff (by simp [φ.denom_ne_zero]),
      RatFunc.num_div_denom]⟩
  trace f hf := by
    obtain ⟨P, hP⟩ := exists_trace_eq (F := F) hf
    exact ⟨P, by rw [hP, aeval_X_ratFunc]⟩
  mul_integral f := by
    obtain ⟨Q, hQ, D, hD⟩ := exists_aeval_mul_mem_rrSpace (C := C) f
    exact ⟨Q, hQ, isIntegral_of_mem_rrSpace hD⟩

omit [IsUltrametricDist C] [Algebra C F] [IsScalarTower C (RatFunc C) F] [IsAlgClosed C]
  [FiniteDimensional (RatFunc C) F] in
lemma algebraMap_X_inv : algebraMap (RatFunc C) F (RatFunc.X)⁻¹ = (xF C F)⁻¹ := map_inv₀ _ _

/-- `X⁻¹` is a coordinate. -/
theorem isCoord_X_inv : IsCoord F (RatFunc.X : RatFunc C)⁻¹ where
  gauss P := gauss1_aeval_X_inv P
  frac φ := by
    obtain ⟨p, q, hq, h⟩ := (isCoord_X (F := F)).frac (invX C φ)
    refine ⟨p, q, hq, ?_⟩
    have h' := congrArg (invX C) h
    simp only [map_mul, invX_apply, aeval_X_ratFunc, invXHom_algebraMap,
      invXHom_invXHom] at h'
    exact h'
  trace f hf := by
    rw [algebraMap_X_inv] at hf
    exact exists_trace_eq_inv hf
  mul_integral f := by
    obtain ⟨Q, hQ, D, hD⟩ := exists_aeval_mul_mem_rrSpace (C := C) f
    set N := max D Q.natDegree
    have hD' := rrSpace_nsmul_mono (C := C) (F := F) (le_max_left D Q.natDegree) hD
    have hint := isIntegral_div_of_mem_rrSpace hD'
    refine ⟨Q.reflect N, by simpa [reflect_eq_zero_iff] using hQ, ?_⟩
    rw [algebraMap_X_inv]
    convert hint using 1
    have hx : xF C F ≠ 0 := by
      intro h
      exact transcendental_xF (C := C) (F := F) (h ▸ isAlgebraic_zero)
    letI : Invertible (xF C F) := invertibleOfNonzero hx
    have := eval₂_reflect_mul_pow (algebraMap C F) (xF C F) N Q (le_max_right _ _)
    rw [invOf_eq_inv] at this
    rw [aeval_def, aeval_def, ← this, mul_assoc, mul_assoc, mul_comm (xF C F ^ N),
      mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, mul_one]

end Coord

section RedPoly

/-- The reduction of a polynomial with coefficients of norm `≤ 1` (`0` otherwise). -/
noncomputable def redPoly (P : C[X]) : 𝓀[X] :=
  open Classical in
  if h : ∀ i, vC (P.coeff i) ≤ 1 then
    (Classical.choose (ValuationResidue.exists_map_eq (v := vC) P h)).map (residue _) else 0

lemma coeff_le_one_of_sup {P : C[X]} (hP : Gauss.sup vC 1 P ≤ 1) (i : ℕ) :
    vC (P.coeff i) ≤ 1 := by
  simpa [Gauss.term] using (Gauss.term_le_sup (v := vC) (r := 1) P i).trans hP

lemma exists_lift_redPoly {P : C[X]} (hP : Gauss.sup vC 1 P ≤ 1) :
    ∃ P' : (HenselComplete.integers C)[X],
      P'.map (algebraMap (HenselComplete.integers C) C) = P ∧
        P'.map (residue _) = redPoly P := by
  have h := coeff_le_one_of_sup hP
  refine ⟨Classical.choose (ValuationResidue.exists_map_eq (v := vC) P h),
    Classical.choose_spec (ValuationResidue.exists_map_eq (v := vC) P h), ?_⟩
  rw [redPoly, dif_pos h]

/-- Every polynomial over the residue field is a reduction. -/
lemma exists_redPoly_eq (ψ : 𝓀[X]) :
    ∃ P : C[X], Gauss.sup vC 1 P ≤ 1 ∧ redPoly P = ψ := by
  obtain ⟨P', rfl⟩ := map_surjective _ (residue_surjective (R := HenselComplete.integers C)) ψ
  set P := P'.map (algebraMap (HenselComplete.integers C) C)
  have hP : Gauss.sup vC 1 P ≤ 1 := Gauss.sup_one_map_le (v := vC) P'
  refine ⟨P, hP, ?_⟩
  obtain ⟨P'', hP'', hred⟩ := exists_lift_redPoly hP
  have : P'' = P' := map_injective _ (FaithfulSMul.algebraMap_injective _ C) hP''
  rw [← hred, this]

lemma sup_lt_one_of_redPoly_eq_zero {P : C[X]} (hP : Gauss.sup vC 1 P ≤ 1)
    (h0 : redPoly P = 0) : Gauss.sup vC 1 P < 1 := by
  refine lt_of_le_of_ne hP fun h1 ↦ ?_
  obtain ⟨P', hP', hred⟩ := exists_lift_redPoly hP
  rw [h0] at hred
  obtain ⟨i, hi⟩ := Gauss.exists_term_eq_sup (v := vC) (r := 1) P
  have hc : vC (P.coeff i) = 1 := by simpa [Gauss.term, h1] using hi
  have hz : residue (HenselComplete.integers C) (P'.coeff i) = 0 := by
    rw [← coeff_map, hred, coeff_zero]
  rw [residue_eq_zero_iff] at hz
  have : vC ((P'.coeff i : HenselComplete.integers C) : C) < 1 := by
    have := (HenselComplete.mem_maximalIdeal_iff_norm_lt_one (P'.coeff i)).1 hz
    rw [NormedField.valuation_apply]
    exact_mod_cast this
  rw [← hP', coeff_map] at hc
  exact this.ne hc

lemma redPoly_eq_zero_of_sup_lt_one {P : C[X]} (hP : Gauss.sup vC 1 P < 1) : redPoly P = 0 := by
  obtain ⟨P', hP', hred⟩ := exists_lift_redPoly hP.le
  rw [← hred]
  ext i
  rw [coeff_map, coeff_zero, residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
  have h := (Gauss.term_le_sup (v := vC) (r := 1) P i).trans_lt hP
  rw [← hP'] at h
  simpa [Gauss.term, ← NNReal.coe_lt_coe] using h

lemma redPoly_eq_zero_iff {P : C[X]} (hP : Gauss.sup vC 1 P ≤ 1) :
    redPoly P = 0 ↔ Gauss.sup vC 1 P < 1 :=
  ⟨sup_lt_one_of_redPoly_eq_zero hP, redPoly_eq_zero_of_sup_lt_one⟩

lemma sup_pos_of_ne_zero {P : C[X]} (hP : P ≠ 0) : 0 < Gauss.sup vC 1 P := by
  obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Polynomial.ext fun i ↦ by simp [h i])
  refine lt_of_lt_of_le ?_ (Gauss.term_le_sup (v := vC) (r := 1) P i)
  simpa [Gauss.term] using hi

lemma sup_X : Gauss.sup vC 1 (X : C[X]) = 1 := by
  have := gauss1_algebraMap (C := C) X
  rwa [RatFunc.algebraMap_X, gauss1_X, eq_comm] at this

end RedPoly

section Lattice

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [Fintype (Ext C F)]

variable (C) in
/-- Orthonormality of a family for `gnorm`. -/
def Orth {ι : Type*} [Fintype ι] (s : ι → F) : Prop :=
  ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • s i) = Finset.univ.sup fun i ↦ gauss1 C (φ i)

variable {ζ : RatFunc C}

omit [IsUltrametricDist C] [Fintype (Ext C F)] in
lemma aeval_coord (P : C[X]) :
    aeval (algebraMap (RatFunc C) F ζ) P = algebraMap (RatFunc C) F (aeval ζ P) :=
  aeval_algebraMap_apply F ζ P

omit [IsUltrametricDist C] [IsScalarTower C (RatFunc C) F] [Fintype (Ext C F)] in
lemma isIntegral_aeval_coord (P : C[X]) :
    IsIntegral (Algebra.adjoin C {algebraMap (RatFunc C) F ζ})
      (aeval (algebraMap (RatFunc C) F ζ) P) :=
  isIntegral_algebraMap (x := (⟨_, aeval_mem_adjoin_singleton C (algebraMap (RatFunc C) F ζ)
    (p := P)⟩ : Algebra.adjoin C {algebraMap (RatFunc C) F ζ}))

variable (hζ : IsCoord F ζ)
include hζ

omit [Fintype (Ext C F)] [IsScalarTower C (RatFunc C) F] in
lemma gauss1_coord : gauss1 C ζ = 1 := by
  simpa [sup_X] using hζ.gauss X

omit [Fintype (Ext C F)] in
lemma valuation_aeval_coord (P : C[X]) (w : Ext C F) :
    w.1 (aeval (algebraMap (RatFunc C) F ζ) P) = Gauss.sup vC 1 P := by
  rw [aeval_coord, valuation_algebraMap, hζ.gauss]

omit [Fintype (Ext C F)] [IsScalarTower C (RatFunc C) F] in
lemma valuation_coord (w : Ext C F) : w.1 (algebraMap (RatFunc C) F ζ) = 1 := by
  rw [valuation_algebraMap, gauss1_coord hζ]

omit [Fintype (Ext C F)] in
lemma red_aeval_coord {P : C[X]} (hP : Gauss.sup vC 1 P ≤ 1) (w : Ext C F) :
    red C (aeval (algebraMap (RatFunc C) F ζ) P) w =
      aeval (red C (algebraMap (RatFunc C) F ζ) w) (redPoly P) := by
  obtain ⟨P', hP', hred⟩ := exists_lift_redPoly hP
  conv_lhs => rw [← hP']
  rw [red_aeval_of_le (valuation_coord hζ w).le, hred]

lemma aeval_coord_mem_intRing {P : C[X]} (hP : Gauss.sup vC 1 P ≤ 1) :
    aeval (algebraMap (RatFunc C) F ζ) P ∈ intRing C F (algebraMap (RatFunc C) F ζ) :=
  ⟨isIntegral_algebraMap (x := (⟨_, aeval_mem_adjoin_singleton C (algebraMap (RatFunc C) F ζ) (p := P)⟩ :
      Algebra.adjoin C {algebraMap (RatFunc C) F ζ})),
    gnorm_le_iff.2 fun w ↦ by rw [valuation_aeval_coord hζ]; exact hP⟩

omit [Fintype (Ext C F)] in
/-- `z̄` is transcendental over `k`. -/
lemma transcendental_red_coord (w : Ext C F) :
    Transcendental 𝓀 (red C (algebraMap (RatFunc C) F ζ) w) := by
  rintro ⟨ψ, hψ, h⟩
  obtain ⟨P, hP, rfl⟩ := exists_redPoly_eq ψ
  have h1 : Gauss.sup vC 1 P = 1 :=
    le_antisymm hP (not_lt.1 fun hlt ↦ hψ (redPoly_eq_zero_of_sup_lt_one hlt))
  have hw := valuation_aeval_coord hζ P w
  rw [h1] at hw
  have := (red_eq_zero_iff hw.le).1 (by rw [red_aeval_coord hζ hP]; exact h)
  exact this.ne hw

lemma valuation_sum_aeval_le {ι : Type*} [Fintype ι] {s : ι → F}
    (hs1 : ∀ i, gnorm C (s i) ≤ 1) {P : ι → C[X]} (hP : ∀ i, Gauss.sup vC 1 (P i) ≤ 1)
    (w : Ext C F) (i : ι) : w.1 (aeval (algebraMap (RatFunc C) F ζ) (P i) * s i) ≤ 1 := by
  rw [map_mul, valuation_aeval_coord hζ]
  exact mul_le_one' (hP i) ((le_gnorm w _).trans (hs1 i))

/-- The reduction of `Σ Pᵢ(z) sᵢ`. -/
lemma red_sum_aeval {ι : Type*} [Fintype ι] {s : ι → F}
    (hs1 : ∀ i, gnorm C (s i) ≤ 1) {P : ι → C[X]} (hP : ∀ i, Gauss.sup vC 1 (P i) ≤ 1)
    (w : Ext C F) :
    red C (∑ i, aeval (algebraMap (RatFunc C) F ζ) (P i) * s i) w =
      ∑ i, aeval (red C (algebraMap (RatFunc C) F ζ) w) (redPoly (P i)) * red C (s i) w := by
  rw [red_sum _ _ fun i _ ↦ valuation_sum_aeval_le hζ hs1 hP w i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [red_mul (((valuation_aeval_coord hζ (P i) w).trans_le (hP i)))
    ((le_gnorm w _).trans (hs1 i)), red_aeval_coord hζ (hP i) w]

/-- **Independence of reductions** of an orthonormal family over `k[z̄]`. -/
lemma eq_zero_of_sum_red {ι : Type*} [Fintype ι] {s : ι → F} (hs : Orth C s)
    (hs1 : ∀ i, gnorm C (s i) ≤ 1) (ψ : ι → 𝓀[X])
    (h : ∀ w, ∑ i, aeval (red C (algebraMap (RatFunc C) F ζ) w) (ψ i) * red C (s i) w = 0) :
    ψ = 0 := by
  classical
  choose P hP hPψ using fun i ↦ exists_redPoly_eq (C := C) (ψ i)
  set f := ∑ i, aeval (algebraMap (RatFunc C) F ζ) (P i) * s i
  have hf : gnorm C f = Finset.univ.sup fun i ↦ Gauss.sup vC 1 (P i) := by
    have : f = ∑ i, aeval ζ (P i) • s i := by
      simp only [f, Algebra.smul_def, aeval_coord]
    rw [this, hs]
    simp only [hζ.gauss]
  have hterm (w : Ext C F) (i : ι) :
      w.1 (aeval (algebraMap (RatFunc C) F ζ) (P i) * s i) ≤ 1 := by
    rw [map_mul, valuation_aeval_coord hζ]
    exact mul_le_one' (hP i) ((le_gnorm w _).trans (hs1 i))
  have hlt : gnorm C f < 1 := (gnorm_lt_iff one_pos).2 fun w ↦ by
    have hfw : w.1 f ≤ 1 := Valuation.map_sum_le _ fun i _ ↦ hterm w i
    refine (red_eq_zero_iff hfw).1 ?_
    rw [red_sum _ _ fun i _ ↦ hterm w i]
    simp_rw [fun i ↦ red_mul (C := C) (w := w) (((valuation_aeval_coord hζ (P i) w).trans_le
      (hP i))) ((le_gnorm w _).trans (hs1 i)), fun i ↦ red_aeval_coord hζ (hP i) w, hPψ]
    exact h w
  funext i
  by_contra hne
  have h1 : Gauss.sup vC 1 (P i) = 1 := by
    refine le_antisymm (hP i) (not_lt.1 fun h' ↦ hne ?_)
    rw [← hPψ]
    exact redPoly_eq_zero_of_sup_lt_one h'
  have hle : Gauss.sup vC 1 (P i) ≤ gnorm C f := by
    rw [hf]
    exact Finset.le_sup (f := fun i ↦ Gauss.sup vC 1 (P i)) (Finset.mem_univ i)
  rw [h1] at hle
  exact (not_le.2 hlt) hle

/-- **Orthonormality from independent reductions**: if the reductions of `sᵢ` (of norm `≤ 1`)
are independent over `k[z̄]`, then `s` is orthonormal. -/
lemma orth_of_indep {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → F}
    (hs1 : ∀ i, gnorm C (s i) ≤ 1)
    (hind : ∀ ψ : ι → 𝓀[X], (∀ w, ∑ i, aeval (red C (algebraMap (RatFunc C) F ζ) w) (ψ i) *
      red C (s i) w = 0) → ψ = 0) : Orth C s := by
  intro φ
  refine le_antisymm ((gnorm_sum_le _ _).trans (Finset.sup_mono_fun fun i _ ↦ ?_)) ?_
  · rw [gnorm_smul]
    exact mul_le_of_le_one_right' (hs1 i)
  by_contra hlt
  push Not at hlt
  set M := Finset.univ.sup fun i ↦ gauss1 C (φ i)
  have hM : 0 < M := lt_of_le_of_lt zero_le hlt
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [M, h] at hM
  obtain ⟨i₀, -, hi₀'⟩ := Finset.exists_mem_eq_sup _ hne fun i ↦ gauss1 C (φ i)
  have hi₀ : M = gauss1 C (φ i₀) := hi₀'
  obtain ⟨γ, hγ⟩ := exists_gauss1_eq (φ i₀)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [hi₀, hγ, nnnorm_zero] at hM
    exact lt_irrefl _ hM
  -- common denominators
  choose p q hq hpq using fun i ↦ hζ.frac (φ i)
  set Q := ∏ i, q i
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hq i
  set R : ι → C[X] := fun i ↦ p i * ∏ j ∈ Finset.univ.erase i, q j
  have hR (i : ι) : aeval ζ Q * φ i = aeval ζ (R i) := by
    simp only [Q, R, map_mul, map_prod]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← hpq i]
    ring
  obtain ⟨e, he⟩ := exists_sup_eq Q
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at he
    exact (sup_pos_of_ne_zero hQ0).ne' he
  set R' : ι → C[X] := fun i ↦ Polynomial.C (e⁻¹ * γ⁻¹) * R i
  have hgQ : gauss1 C (aeval ζ Q) = ‖e‖₊ := by rw [hζ.gauss, he]
  have hR' (i : ι) : Gauss.sup vC 1 (R' i) = gauss1 C (φ i) / ‖γ‖₊ := by
    rw [← hζ.gauss, map_mul, aeval_C, ← hR, map_mul, map_mul, map_mul, map_mul,
      gauss1_algebraMap_C, gauss1_algebraMap_C, hgQ, nnnorm_inv, nnnorm_inv]
    have : ‖e‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 he0
    field_simp
  have hγM : ‖γ‖₊ = M := by rw [← hγ, ← hi₀]
  have hR'1 (i : ι) : Gauss.sup vC 1 (R' i) ≤ 1 := by
    rw [hR', div_le_one (by rw [hγM]; exact hM), hγM]
    exact Finset.le_sup (f := fun i ↦ gauss1 C (φ i)) (Finset.mem_univ i)
  set f := ∑ i, aeval (algebraMap (RatFunc C) F ζ) (R' i) * s i
  have hf : f = algebraMap (RatFunc C) F (algebraMap C (RatFunc C) (e⁻¹ * γ⁻¹) * aeval ζ Q) *
      ∑ i, φ i • s i := by
    simp only [f, R', Finset.mul_sum, aeval_coord, map_mul, aeval_C, ← hR, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hfn : gnorm C f < 1 := by
    rw [hf, gnorm_algebraMap_mul, map_mul, gauss1_algebraMap_C, hgQ, nnnorm_mul, nnnorm_inv,
      nnnorm_inv, hγM]
    have : ‖e‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 he0
    rw [show ‖e‖₊⁻¹ * M⁻¹ * ‖e‖₊ = M⁻¹ by field_simp]
    rw [← div_eq_inv_mul, div_lt_one hM]
    exact hlt
  have h0 := hind (fun i ↦ redPoly (R' i)) fun w ↦ by
    rw [← red_sum_aeval hζ hs1 hR'1 w]
    exact (red_eq_zero_iff ((le_gnorm w f).trans hfn.le)).2 ((le_gnorm w f).trans_lt hfn)
  have h1 := sup_lt_one_of_redPoly_eq_zero (hR'1 i₀) (congrFun h0 i₀)
  rw [hR', ← hi₀, ← hγM, div_self (nnnorm_ne_zero_iff.2 hγ0)] at h1
  exact lt_irrefl _ h1

/-- An orthonormal basis can be made integral over `C[z]` (S7⁺.1). -/
lemma exists_integral_orth {ι : Type*} [Fintype ι] (b : Module.Basis ι (RatFunc C) F)
    (hb : Orth C b) : ∃ d : Module.Basis ι (RatFunc C) F, Orth C d ∧
      ∀ i, d i ∈ intRing C F (algebraMap (RatFunc C) F ζ) := by
  classical
  choose P hP0 hPint using fun i ↦ hζ.mul_integral (b i)
  choose c hc using fun i ↦ exists_sup_eq (P i)
  have hc0 (i : ι) : c i ≠ 0 := by
    rintro h
    have := sup_pos_of_ne_zero (hP0 i)
    rw [hc i, h, nnnorm_zero] at this
    exact lt_irrefl _ this
  set u : ι → RatFunc C := fun i ↦ aeval ζ (Polynomial.C (c i)⁻¹ * P i)
  have hu (i : ι) : gauss1 C (u i) = 1 := by
    rw [hζ.gauss, ← hζ.gauss, map_mul, aeval_C, map_mul, gauss1_algebraMap_C, hζ.gauss, hc i,
      nnnorm_inv, inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 (hc0 i))]
  have hu0 (i : ι) : u i ≠ 0 := fun h ↦ by simpa [h] using hu i
  set d := b.unitsSMul fun i ↦ Units.mk0 (u i) (hu0 i)
  have hd (i : ι) : d i = u i • b i := by
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have horth : Orth C d := fun φ ↦ by
    have : ∑ i, φ i • d i = ∑ i, (φ i * u i) • b i := by
      simp only [hd, smul_smul]
    rw [this, hb]
    simp only [map_mul, hu, mul_one]
  refine ⟨d, horth, fun i ↦ ⟨?_, ?_⟩⟩
  · have hui : algebraMap (RatFunc C) F (u i) =
        aeval (algebraMap (RatFunc C) F ζ) (Polynomial.C (c i)⁻¹) *
          aeval (algebraMap (RatFunc C) F ζ) (P i) := by
      simp only [u, aeval_coord, map_mul]
    rw [hd, Algebra.smul_def, hui, mul_assoc]
    exact (isIntegral_aeval_coord (F := F) (ζ := ζ) _).mul (hPint i)
  · have := horth (Pi.single i 1)
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    rw [this]
    exact Finset.sup_le fun j _ ↦ by split_ifs <;> simp

variable [CharZero C] [FiniteDimensional (RatFunc C) F]

/-- **The trace bound** (S7⁺.1): there is `Δ ∈ C[X]` of Gauss norm `1` such that for every
element `a` of the chart ring, `Δ(ζ) · dᵢ*(a)` is a polynomial in `ζ` of Gauss norm `≤ 1`. -/
theorem exists_trace_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : Module.Basis ι (RatFunc C) F) (hd : Orth C d)
    (hdi : ∀ i, d i ∈ intRing C F (algebraMap (RatFunc C) F ζ)) :
    ∃ Δ : C[X], Gauss.sup vC 1 Δ = 1 ∧ ∀ a ∈ intRing C F (algebraMap (RatFunc C) F ζ), ∀ i,
      ∃ P : C[X], Gauss.sup vC 1 P ≤ 1 ∧ aeval ζ Δ * d.repr a i = aeval ζ P := by
  set R : Subring (RatFunc C) := (aeval ζ : C[X] →ₐ[C] RatFunc C).range.toSubring
  have htr (f : F) (hf : f ∈ intRing C F (algebraMap (RatFunc C) F ζ)) :
      Algebra.trace (RatFunc C) F f ∈ R := by
    obtain ⟨Q, hQ⟩ := hζ.trace f hf.1
    exact ⟨Q, hQ.symm⟩
  set G := (Algebra.traceForm (RatFunc C) F).toMatrix d
  have hG (i j : ι) : G i j = Algebra.trace (RatFunc C) F (d i * d j) := by
    simp [G, LinearMap.BilinForm.toMatrix_apply, Algebra.traceForm_apply]
  set Gr : Matrix ι ι R := fun i j ↦ ⟨G i j, by rw [hG]; exact htr _ (mul_mem (hdi i) (hdi j))⟩
  have hGr : G = Gr.map R.subtype := by ext i j; rfl
  have hdet0 : G.det ≠ 0 := det_traceForm_ne_zero d
  have hdetR : G.det ∈ R := by
    have h := RingHom.map_det R.subtype Gr
    rw [RingHom.mapMatrix_apply] at h
    rw [hGr, ← h]
    exact (Gr.det).2
  obtain ⟨δ, hδ⟩ := hdetR
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hdet0 (by rw [← hδ]; simp)
  obtain ⟨c, hc⟩ := exists_sup_eq δ
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hc
    exact (sup_pos_of_ne_zero hδ0).ne' hc
  refine ⟨Polynomial.C c⁻¹ * δ, ?_, fun a ha i ↦ ?_⟩
  · rw [← hζ.gauss, map_mul, aeval_C, map_mul, gauss1_algebraMap_C, hζ.gauss, hc, nnnorm_inv,
      inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hc0)]
  -- `G φ = T`
  set φ : ι → RatFunc C := ⇑(d.repr a)
  set T : ι → RatFunc C := fun j ↦ Algebra.trace (RatFunc C) F (d j * a)
  have hGφ : Matrix.mulVec G φ = T := by
    funext j
    simp only [Matrix.mulVec, dotProduct, hG, T]
    conv_rhs => rw [← d.sum_repr a]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hadj : G.det • φ = Matrix.mulVec G.adjugate T := by
    rw [← hGφ, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hmem : G.det * φ i ∈ R := by
    have := congrFun hadj i
    rw [Pi.smul_apply, smul_eq_mul] at this
    have h := RingHom.map_adjugate R.subtype Gr
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [this, hGr, ← h]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact sum_mem fun j _ ↦ mul_mem (Gr.adjugate i j).2 (htr _ (mul_mem (hdi j) ha))
  obtain ⟨Pr, hPr⟩ := hmem
  replace hPr : aeval ζ Pr = G.det * φ i := hPr
  replace hδ : aeval ζ δ = G.det := hδ
  refine ⟨Polynomial.C c⁻¹ * Pr, ?_, ?_⟩
  · have hφ : gauss1 C (φ i) ≤ 1 := by
      have h := hd φ
      rw [d.sum_repr a] at h
      exact (Finset.le_sup (f := fun i ↦ gauss1 C (φ i)) (Finset.mem_univ i)).trans
        (h ▸ ha.2)
    rw [← hζ.gauss, map_mul, aeval_C]
    change gauss1 C (algebraMap C (RatFunc C) c⁻¹ * aeval ζ Pr) ≤ 1
    rw [hPr, ← hδ, map_mul, map_mul, gauss1_algebraMap_C, hζ.gauss, hc, ← mul_assoc,
      nnnorm_inv, inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hc0), one_mul]
    exact hφ
  · change aeval ζ (Polynomial.C c⁻¹ * δ) * φ i = aeval ζ (Polynomial.C c⁻¹ * Pr)
    rw [map_mul, map_mul, aeval_C, mul_assoc, hδ]
    change _ = _ * aeval ζ Pr
    rw [hPr]

omit [IsUltrametricDist C] [Fintype (Ext C F)] hζ [CharZero C]
  [FiniteDimensional (RatFunc C) F] in
/-- In `F`: `Δ(z) a = Σᵢ Pᵢ(z) dᵢ` for the polynomials of the trace bound. -/
lemma aeval_mul_eq_sum {ι : Type*} [Fintype ι] (d : Module.Basis ι (RatFunc C) F)
    {Δ : C[X]} {a : F} {P : ι → C[X]} (hP : ∀ i, aeval ζ Δ * d.repr a i = aeval ζ (P i)) :
    aeval (algebraMap (RatFunc C) F ζ) Δ * a =
      ∑ i, aeval (algebraMap (RatFunc C) F ζ) (P i) * d i := by
  conv_lhs => rw [← d.sum_repr a]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, ← mul_assoc, aeval_coord, aeval_coord, ← map_mul, hP]

/-- **The chart basis** (S7⁺.2): there is an orthonormal `C(X)`-basis `s` of `F` in the chart
ring whose reductions span the reduced chart ring `redRing z` over `k[z̄]`. -/
theorem exists_chartBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (RatFunc C) F) (hb : Orth C b) :
    ∃ (n : ℕ) (s : Module.Basis (Fin n) (RatFunc C) F), Orth C s ∧
      (∀ j, s j ∈ intRing C F (algebraMap (RatFunc C) F ζ)) ∧
      ∀ a ∈ intRing C F (algebraMap (RatFunc C) F ζ), ∃ ψ : Fin n → 𝓀[X], ∀ w : Ext C F,
        red C a w = ∑ j, aeval (red C (algebraMap (RatFunc C) F ζ) w) (ψ j) * red C (s j) w := by
  classical
  set z := algebraMap (RatFunc C) F ζ
  obtain ⟨d, hd, hdi⟩ := exists_integral_orth hζ b hb
  obtain ⟨Δ, hΔ, hbound⟩ := exists_trace_bound hζ d hd hdi
  have hd1 (i : ι) : gnorm C (d i) ≤ 1 := (hdi i).2
  have hΔ0 : redPoly Δ ≠ 0 := fun h ↦ (sup_lt_one_of_redPoly_eq_zero hΔ.le h).ne hΔ
  have hΔw (w : Ext C F) : aeval (red C z w) (redPoly Δ) ≠ 0 := fun h ↦
    transcendental_red_coord hζ w ⟨_, hΔ0, h⟩
  -- the reduction identity
  have hred (a : F) (ha : a ∈ intRing C F z) : ∃ c : ι → 𝓀[X], ∀ w : Ext C F,
      aeval (red C z w) (redPoly Δ) * red C a w = ∑ i, aeval (red C z w) (c i) * red C (d i) w := by
    choose P hP1 hP using hbound a ha
    refine ⟨fun i ↦ redPoly (P i), fun w ↦ ?_⟩
    rw [← red_sum_aeval hζ hd1 hP1 w, ← aeval_mul_eq_sum d hP, ← red_aeval_coord hζ hΔ.le w,
      red_mul ((valuation_aeval_coord hζ Δ w).trans_le hΔ.le) ((le_gnorm w a).trans ha.2)]
  -- the module of coefficient vectors
  let N : Submodule 𝓀[X] (ι → 𝓀[X]) :=
    { carrier := {c | ∃ a ∈ intRing C F z, ∀ w : Ext C F,
        aeval (red C z w) (redPoly Δ) * red C a w = ∑ i, aeval (red C z w) (c i) * red C (d i) w}
      add_mem' := by
        rintro c c' ⟨a, ha, hc⟩ ⟨a', ha', hc'⟩
        refine ⟨a + a', add_mem ha ha', fun w ↦ ?_⟩
        rw [red_add ((le_gnorm w a).trans ha.2) ((le_gnorm w a').trans ha'.2), mul_add, hc, hc',
          ← Finset.sum_add_distrib]
        simp only [Pi.add_apply, map_add, add_mul]
      zero_mem' := ⟨0, zero_mem _, fun w ↦ by simp [red_zero]⟩
      smul_mem' := by
        rintro ψ c ⟨a, ha, hc⟩
        obtain ⟨Q, hQ, rfl⟩ := exists_redPoly_eq (C := C) ψ
        refine ⟨aeval z Q * a, mul_mem (aeval_coord_mem_intRing hζ hQ) ha, fun w ↦ ?_⟩
        rw [red_mul ((valuation_aeval_coord hζ Q w).trans_le hQ) ((le_gnorm w a).trans ha.2),
          red_aeval_coord hζ hQ w, mul_left_comm, hc, Finset.mul_sum]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
        rfl }
  obtain ⟨n, β⟩ := Submodule.basisOfPid (Pi.basisFun 𝓀[X] ι) N
  choose s' hs' hs'eq using fun j ↦ (β j).2
  have hs'1 (j : Fin n) : gnorm C (s' j) ≤ 1 := (hs' j).2
  -- independence of the reductions of `s'`
  have hind (ψ : Fin n → 𝓀[X]) (h : ∀ w, ∑ j, aeval (red C z w) (ψ j) * red C (s' j) w = 0) :
      ψ = 0 := by
    have h1 : (fun i ↦ ∑ j, ψ j * (β j : ι → 𝓀[X]) i) = 0 := by
      refine eq_zero_of_sum_red hζ hd hd1 _ fun w ↦ ?_
      have := congrArg (aeval (red C z w) (redPoly Δ) * ·) (h w)
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      simp only [map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_left_comm, hs'eq j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have h2 : ∑ j, ψ j • β j = 0 := by
      apply Subtype.ext
      funext i
      have := congrFun h1 i
      simpa [Submodule.coe_sum] using this
    exact (Fintype.linearIndependent_iff.1 β.linearIndependent) ψ h2 |> funext
  have horth : Orth C s' := orth_of_indep hζ hs'1 hind
  -- spanning
  have hspan (a : F) (ha : a ∈ intRing C F z) : ∃ ψ : Fin n → 𝓀[X], ∀ w : Ext C F,
      red C a w = ∑ j, aeval (red C z w) (ψ j) * red C (s' j) w := by
    obtain ⟨c, hc⟩ := hred a ha
    have hcN : c ∈ N := ⟨a, ha, hc⟩
    set ψ := β.repr ⟨c, hcN⟩
    have hcsum : c = fun i ↦ ∑ j, ψ j * (β j : ι → 𝓀[X]) i := by
      have := congrArg Subtype.val (β.sum_repr ⟨c, hcN⟩)
      funext i
      have hi := congrFun this i
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hi
      exact hi.symm
    refine ⟨ψ, fun w ↦ mul_left_cancel₀ (hΔw w) ?_⟩
    rw [hc w, hcsum, Finset.mul_sum]
    simp only [map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_left_comm, hs'eq j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  -- the count `n = [F : C(X)]`
  have hli : LinearIndependent (RatFunc C) s' := by
    rw [Fintype.linearIndependent_iff]
    intro φ hφ j
    have h0 := horth φ
    rw [hφ, gnorm_zero] at h0
    have := Finset.le_sup (f := fun j ↦ gauss1 C (φ j)) (Finset.mem_univ j)
    rw [← h0, nonpos_iff_eq_zero, map_eq_zero] at this
    exact this
  have hn1 : n ≤ Module.finrank (RatFunc C) F := by
    simpa using hli.fintype_card_le_finrank
  have hn2 : Module.finrank (RatFunc C) F ≤ n := by
    rw [Module.finrank_eq_card_basis b]
    haveI : Module.Finite 𝓀[X] N := Module.Finite.of_basis β
    have hmem (i : ι) : (Pi.single i (redPoly Δ) : ι → 𝓀[X]) ∈ N := by
      refine ⟨d i, hdi i, fun w ↦ ?_⟩
      simp only [Pi.single_apply, apply_ite (aeval (red C z w)), map_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hli' : LinearIndependent 𝓀[X] fun i ↦ (⟨_, hmem i⟩ : N) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := congrFun (congrArg Subtype.val hc) i
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, ZeroMemClass.coe_zero, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_right hΔ0
    have := hli'.fintype_card_le_finrank
    rwa [Module.finrank_eq_card_basis β, Fintype.card_fin] at this
  have hcard : Fintype.card (Fin n) = Module.finrank (RatFunc C) F := by
    rw [Fintype.card_fin]; omega
  haveI : Nonempty (Fin n) := ⟨⟨0, by
    have := Module.finrank_pos (R := RatFunc C) (M := F); omega⟩⟩
  set s := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hs : ⇑s = s' := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  exact ⟨n, s, hs ▸ horth, hs ▸ hs', hs ▸ hspan⟩

end Lattice

end GaussFibre

end SemistableReduction
