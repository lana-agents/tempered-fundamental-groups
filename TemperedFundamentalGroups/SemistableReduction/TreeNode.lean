/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TreeReduction

/-!
# Node charts of a Gauss tree

Blueprint §9.9, S7.5. For a coordinate `t` of `F'` and `0 < |c| < 1`, the node chart
`O_C[t, c/t]` of the annulus between the Gauss points of `t` (outer) and of `t/c` (inner).

* `TypeTwo.ofComap`: a valuation over the Gauss point of a coordinate as a type-2 valuation;
* `comap_eq_gauss1_of_valuation_sub`: the values of `t - β` determine the Gauss point;
* `isIntegral_nodeRing`: the maximum principle (`GaussTube.isIntegral_of_le`) for type-2
  valuations: if `tᴺ y` is integral over `C[t]` and `y` has value `≤ 1` at all type-2 valuations
  over the Gauss points of `t` and of `c / t`, then `y` is integral over `O_C[t, c/t]` (in the
  `C(X)`-algebra structure `X ↦ t`).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability GaussFibre GaussTube

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra C F]

section Conv

/-- A criterion for a valuation to lie over the Gauss point of `t`: the values of the constants and
of the `t - β` are right. -/
lemma comap_eq_gauss1_of_valuation_sub [IsAlgClosed C] {t : F} (ht : Transcendental C t)
    (v : Valuation F ℝ≥0) (hC : ∀ c : C, v (algebraMap C F c) = ‖c‖₊)
    (h : ∀ β : C, v (t - algebraMap C F β) = max ‖β‖₊ 1) :
    v.comap (coordAlgHom ht).toRingHom = gauss1 C := by
  refine valuation_ratFunc_ext_of_linear (fun e ↦ ?_) fun β ↦ ?_
  · simp only [comap_apply]
    change v (coordAlgHom ht (algebraMap C (RatFunc C) e)) = _
    rw [AlgHom.commutes, hC, gauss1_algebraMap_C]
  · simp only [comap_apply]
    change v (coordAlgHom ht (algebraMap C[X] (RatFunc C) (X - Polynomial.C β))) = _
    rw [coordAlgHom_algebraMap, _root_.map_sub, aeval_X, aeval_C, h, gaussRat_algebraMap,
      gauss_X_sub_C, zero_sub, Valuation.map_neg, NormedField.valuation_apply, Units.val_one]

variable [IsAlgClosed C] [IsCurveFunctionField C F]

/-- A valuation over the Gauss point of a coordinate, as a type-2 valuation. -/
noncomputable def TypeTwo.ofComap {t : F} (ht : Transcendental C t) (v : Valuation F ℝ≥0)
    (hv : v.comap (coordAlgHom ht).toRingHom = gauss1 C) : TypeTwo C F :=
  letI : Algebra (RatFunc C) F := (coordAlgHom ht).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom ht).commutes c).symm
  ⟨v, by
    ext c
    have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u (algebraMap C (RatFunc C) c)) hv
    simp only [comap_apply] at this
    change v (coordAlgHom ht (algebraMap C (RatFunc C) c)) = _ at this
    rw [AlgHom.commutes, gauss1_algebraMap_C] at this
    rw [comap_apply, this, NormedField.valuation_apply], by
    letI := hasExtension_C (F := F) (⟨v, hv⟩ : Ext C F)
    exact Algebra.transcendental_def.2 ⟨_, transcendental_red_x (⟨v, hv⟩ : Ext C F)⟩⟩

omit [IsCurveFunctionField C F] in
lemma TypeTwo.ofComap_val {t : F} (ht : Transcendental C t) (v : Valuation F ℝ≥0)
    (hv : v.comap (coordAlgHom ht).toRingHom = gauss1 C) : (TypeTwo.ofComap ht v hv).val = v :=
  rfl

omit [IsCurveFunctionField C F] in
lemma TypeTwo.isOver_ofComap {t : F} (ht : Transcendental C t) (v : Valuation F ℝ≥0)
    (hv : v.comap (coordAlgHom ht).toRingHom = gauss1 C) : IsOver ht (TypeTwo.ofComap ht v hv) :=
  hv

end Conv

section Node

variable [IsAlgClosed C] [IsCurveFunctionField C F] [CharZero C]
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **The maximum principle for node charts, with type-2 valuations.** -/
theorem isIntegral_nodeRing {t : F} (ht : Transcendental C t) {c : C} (hc0 : c ≠ 0)
    (ht' : Transcendental C (algebraMap C F c / t)) {y : F} {N : ℕ}
    (hint : IsIntegral (Algebra.adjoin C {t}) (t ^ N * y))
    (hout : ∀ W : TypeTwo C F, IsOver ht W → W.val y ≤ 1)
    (hin : ∀ W : TypeTwo C F, IsOver ht' W → W.val y ≤ 1) :
    letI : Algebra (RatFunc C) F := (coordAlgHom ht).toRingHom.toAlgebra
    IsIntegral (nodeRing c) y := by
  letI : Algebra (RatFunc C) F := (coordAlgHom ht).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom ht).commutes c).symm
  have hxF : xF C F = t := xF_coord ht
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ ht)
  refine isIntegral_of_le hp hp1 hc0 (N := N) (by rwa [hxF])
    (fun v ↦ hout (TypeTwo.ofComap ht v.1 v.2) (TypeTwo.isOver_ofComap ht v.1 v.2)) fun v ↦ ?_
  -- an extension of the inner Gauss point lies over the Gauss point of `c / t`
  have hv (φ : RatFunc C) : v.1 (coordAlgHom ht φ) =
      gaussRat (NormedField.valuation (K := C)) 0 (invRad hc0 1) φ :=
    congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u φ) v.2
  have hC (e : C) : v.1 (algebraMap C F e) = ‖e‖₊ := by
    rw [← AlgHom.commutes (coordAlgHom ht) e, hv, gaussRat_algebraMap_C,
      NormedField.valuation_apply]
  have hlin (γ : C) : v.1 (t - algebraMap C F γ) = max ‖γ‖₊ ‖c‖₊ := by
    have := hv (algebraMap C[X] (RatFunc C) (X - Polynomial.C γ))
    rw [coordAlgHom_algebraMap, _root_.map_sub, aeval_X, aeval_C, gaussRat_algebraMap,
      gauss_X_sub_C, zero_sub, Valuation.map_neg, NormedField.valuation_apply, coe_invRad,
      Units.val_one, div_one] at this
    exact this
  have ht1 : v.1 t = ‖c‖₊ := by simpa using hlin 0
  have hc' : ‖c‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 hc0
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht1
    exact hc' ht1.symm
  refine hin (TypeTwo.ofComap ht' v.1 (comap_eq_gauss1_of_valuation_sub ht' v.1 hC fun β ↦ ?_))
    (TypeTwo.isOver_ofComap _ _ _)
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [map_zero, sub_zero, map_div₀, hC, ht1, div_self hc', nnnorm_zero, max_eq_right zero_le]
  have heq : algebraMap C F c / t - algebraMap C F β =
      algebraMap C F (-β) * (t - algebraMap C F (c / β)) / t := by
    rw [map_div₀, _root_.map_neg]
    have hβ' : algebraMap C F β ≠ 0 := by simpa using hβ
    field_simp
    ring
  rw [heq, map_div₀, map_mul, hC, hlin, ht1, nnnorm_neg, nnnorm_div,
    mul_max_of_nonneg _ _ zero_le, mul_div_cancel₀ _ (nnnorm_ne_zero_iff.2 hβ),
    show max ‖c‖₊ (‖β‖₊ * ‖c‖₊) = ‖c‖₊ * max 1 ‖β‖₊ by
      rw [mul_max_of_nonneg _ _ zero_le, mul_one, mul_comm],
    mul_div_cancel_left₀ _ hc', max_comm]

end Node

section AlgHom

omit [IsUltrametricDist C] in
/-- `C`-algebra maps out of `C(X)` are determined by the image of `X`. -/
lemma ratFunc_algHom_ext {φ ψ : RatFunc C →ₐ[C] F} (h : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  have hp (P : C[X]) : φ (algebraMap C[X] (RatFunc C) P) = ψ (algebraMap C[X] (RatFunc C) P) := by
    have e (χ : RatFunc C →ₐ[C] F) : χ (algebraMap C[X] (RatFunc C) P) =
        aeval (χ RatFunc.X) P := by
      rw [Polynomial.aeval_algHom_apply, RatFunc.aeval_X_left_eq_algebraMap]
    rw [e, e, h]
  ext f
  rw [← RatFunc.num_div_denom f, map_div₀, map_div₀, hp, hp]

omit [IsUltrametricDist C] in
lemma coordAlgHom_X {t : F} (ht : Transcendental C t) : coordAlgHom ht RatFunc.X = t := by
  rw [← RatFunc.algebraMap_X, coordAlgHom_algebraMap, aeval_X]

omit [IsUltrametricDist C] in
/-- The inversion `X ↦ c/X` followed by the coordinate `t` is the coordinate `c/t`. -/
lemma coordAlgHom_comp_inv [IsAlgClosed C] {t : F} (ht : Transcendental C t) {c : C} (hc0 : c ≠ 0)
    (ht' : Transcendental C (algebraMap C F c / t)) :
    (coordAlgHom ht).comp (inv hc0).toAlgHom = coordAlgHom ht' := by
  refine ratFunc_algHom_ext ?_
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, inv_apply, invHom_X,
    map_div₀, AlgHom.commutes, coordAlgHom_X, coordAlgHom_X]

end AlgHom

namespace TreeCount

variable (T : TreeData C) [IsAlgClosed C] [IsCurveFunctionField C F] {x₀ : F}
  (hx₀ : Transcendental C x₀)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Twist

open scoped Classical in
variable (x₀) in
/-- The factor of the twist of an edge for the point `bⱼ`: `(x₀ - bⱼ)` divided by `x₀ - a_{child}`
(if `bⱼ` is in the child disc), by `c_{parent}` (if `bⱼ` is in the parent disc), or by
`a_{child} - bⱼ`; a unit at both end points of the edge. -/
noncomputable def TreeData.mu (e : T.E) (j : T.ι) : F :=
  if ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖ then
    (x₀ - algebraMap C F (T.b j)) / (x₀ - algebraMap C F (T.a (T.chi e)))
  else if ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.par e)‖ then
    (x₀ - algebraMap C F (T.b j)) / algebraMap C F (T.c (T.par e))
  else (x₀ - algebraMap C F (T.b j)) / algebraMap C F (T.a (T.chi e) - T.b j)

lemma TreeData.norm_b_sub (e : T.E) (j : T.ι) (h1 : ¬ ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖) :
    ‖T.c (T.par e)‖ ≤ ‖T.b j - T.a (T.chi e)‖ :=
  (T.hb_edge e j).resolve_left h1

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
lemma TreeData.ec_eq_mul (e : T.E) :
    x₀ - algebraMap C F (T.a (T.chi e)) = algebraMap C F (T.c (T.par e)) * T.ec x₀ e := by
  have : algebraMap C F (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  simp only [TreeData.ec, vcoord]
  field_simp

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
lemma TreeData.vc_chi_eq (e : T.E) :
    T.ec x₀ e = algebraMap C F (T.ce e) * T.vc x₀ (T.chi e) := by
  have h1 : algebraMap C F (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  have h2 : algebraMap C F (T.c (T.chi e)) ≠ 0 := by simpa using T.hc (T.chi e)
  simp only [TreeData.ec, TreeData.vc, vcoord, TreeData.ce, map_div₀]
  field_simp

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
lemma TreeData.nnnorm_b_sub_par_le (e : T.E) (j : T.ι) :
    ‖T.b j - T.a (T.par e)‖₊ ≤ max ‖T.b j - T.a (T.chi e)‖₊ ‖T.c (T.par e)‖₊ := by
  have h : T.b j - T.a (T.par e) = (T.b j - T.a (T.chi e)) + (T.a (T.chi e) - T.a (T.par e)) := by
    ring
  rw [h]
  refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le_max le_rfl ?_)
  exact_mod_cast T.hedge_a e

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
lemma TreeData.nnnorm_b_sub_par_eq (e : T.E) (j : T.ι)
    (h3 : ‖T.c (T.par e)‖ < ‖T.b j - T.a (T.chi e)‖) :
    ‖T.b j - T.a (T.par e)‖₊ = ‖T.b j - T.a (T.chi e)‖₊ := by
  have h : T.b j - T.a (T.par e) = (T.b j - T.a (T.chi e)) + (T.a (T.chi e) - T.a (T.par e)) := by
    ring
  have hlt : ‖T.a (T.chi e) - T.a (T.par e)‖₊ < ‖T.b j - T.a (T.chi e)‖₊ := by
    have := (T.hedge_a e).trans_lt h3
    exact_mod_cast this
  rw [h, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm (ne_of_gt hlt),
    max_eq_left hlt.le]

omit [IsCurveFunctionField C F] in
lemma valuation_mu_par {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.par e)) W)
    (j : T.ι) : W.val (T.mu x₀ e j) = 1 := by
  have hcp : ‖T.c (T.par e)‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 (T.hc _)
  have hca : ‖T.a (T.chi e) - T.a (T.par e)‖₊ ≤ ‖T.c (T.par e)‖₊ := by
    exact_mod_cast T.hedge_a e
  have hle := T.nnnorm_b_sub_par_le e j
  unfold TreeData.mu
  split_ifs with h1 h2
  · have h1' : ‖T.b j - T.a (T.chi e)‖₊ ≤ ‖T.c (T.par e)‖₊ := by
      have := h1.trans (T.hedge_c e).le
      exact_mod_cast this
    rw [map_div₀, valuation_xF_sub T hx₀ hW, valuation_xF_sub T hx₀ hW,
      max_eq_left (hle.trans (max_le h1' le_rfl)), max_eq_left hca, div_self hcp]
  · have h2' : ‖T.b j - T.a (T.chi e)‖₊ ≤ ‖T.c (T.par e)‖₊ := by exact_mod_cast h2
    rw [map_div₀, valuation_xF_sub T hx₀ hW, TypeTwo.valuation_algebraMap,
      max_eq_left (hle.trans (max_le h2' le_rfl)), div_self hcp]
  · have h3 : ‖T.c (T.par e)‖ < ‖T.b j - T.a (T.chi e)‖ := not_le.1 h2
    have h3' : ‖T.c (T.par e)‖₊ < ‖T.b j - T.a (T.chi e)‖₊ := by exact_mod_cast h3
    have hab : ‖T.a (T.chi e) - T.b j‖₊ = ‖T.b j - T.a (T.chi e)‖₊ := by
      rw [← nnnorm_neg, neg_sub]
    rw [map_div₀, valuation_xF_sub T hx₀ hW, TypeTwo.valuation_algebraMap,
      T.nnnorm_b_sub_par_eq e j h3, max_eq_right h3'.le, hab,
      div_self (ne_of_gt (lt_of_le_of_lt zero_le h3'))]

omit [IsCurveFunctionField C F] in
lemma valuation_mu_chi {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.chi e)) W)
    (j : T.ι) : W.val (T.mu x₀ e j) = 1 := by
  have hcc : ‖T.c (T.chi e)‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 (T.hc _)
  unfold TreeData.mu
  split_ifs with h1 h2
  · have h1' : ‖T.b j - T.a (T.chi e)‖₊ ≤ ‖T.c (T.chi e)‖₊ := by exact_mod_cast h1
    rw [map_div₀, valuation_xF_sub T hx₀ hW, valuation_xF_sub T hx₀ hW, max_eq_left h1',
      sub_self, nnnorm_zero, max_eq_left zero_le, div_self hcc]
  · have heq : ‖T.b j - T.a (T.chi e)‖₊ = ‖T.c (T.par e)‖₊ :=
      NNReal.coe_injective (by simpa using le_antisymm h2 (T.norm_b_sub e j h1))
    have hlt : ‖T.c (T.chi e)‖₊ ≤ ‖T.c (T.par e)‖₊ := by exact_mod_cast (T.hedge_c e).le
    rw [map_div₀, valuation_xF_sub T hx₀ hW, TypeTwo.valuation_algebraMap, heq, max_eq_right hlt,
      div_self (nnnorm_ne_zero_iff.2 (T.hc _))]
  · have h3 : ‖T.c (T.par e)‖ < ‖T.b j - T.a (T.chi e)‖ := not_le.1 h2
    have h3' : ‖T.c (T.chi e)‖₊ ≤ ‖T.b j - T.a (T.chi e)‖₊ := by
      have := (T.hedge_c e).le.trans h3.le
      exact_mod_cast this
    have hab : ‖T.a (T.chi e) - T.b j‖₊ = ‖T.b j - T.a (T.chi e)‖₊ := by
      rw [← nnnorm_neg, neg_sub]
    have hne : ‖T.b j - T.a (T.chi e)‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 fun h0 ↦ by
      rw [h0, norm_zero] at h3
      exact not_lt.2 (norm_nonneg _) h3
    rw [map_div₀, valuation_xF_sub T hx₀ hW, TypeTwo.valuation_algebraMap, max_eq_right h3',
      hab, div_self hne]

open scoped Classical in
/-- The exponent of `x₀ - a_{child}` in the twist factor. -/
noncomputable def TreeData.eps (e : T.E) (j : T.ι) : ℕ :=
  if ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖ then 1 else 0

open scoped Classical in
/-- The constant of the twist factor. -/
noncomputable def TreeData.kap (e : T.E) (j : T.ι) : C :=
  if ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.par e)‖ then (T.c (T.par e))⁻¹
  else (T.a (T.chi e) - T.b j)⁻¹

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
include hx₀ in
lemma TreeData.ec_pow_mul_mu (e : T.E) (j : T.ι) :
    T.ec x₀ e ^ T.eps e j * T.mu x₀ e j =
      (x₀ - algebraMap C F (T.b j)) * algebraMap C F (T.kap e j) := by
  have hcp : algebraMap C F (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  have hxa : x₀ - algebraMap C F (T.a (T.chi e)) ≠ 0 := xF_sub_ne_zero hx₀ _
  have hec := T.ec_eq_mul (x₀ := x₀) e
  unfold TreeData.eps TreeData.kap TreeData.mu
  split_ifs with h1 h2 h2
  · rw [pow_one, map_inv₀, hec]
    rw [hec] at hxa
    have hec0 : T.ec x₀ e ≠ 0 := right_ne_zero_of_mul hxa
    field_simp
  · exact absurd ((h1.trans (T.hedge_c e).le)) h2
  · rw [pow_zero, one_mul, map_inv₀, div_eq_mul_inv]
  · rw [pow_zero, one_mul, map_inv₀, div_eq_mul_inv]

include hx₀ in
/-- The twisted element `x̃ᴺ f Πⱼ μⱼᵐ` is integral over `C[x̃]` (`x̃` the edge coordinate). -/
lemma isIntegral_ec_pow_mul {m : ℕ} {f : F} (hf : f ∈ rrSpace (T.D x₀ m)) (e : T.E) :
    IsIntegral (Algebra.adjoin C {T.ec x₀ e})
      (T.ec x₀ e ^ (m * ∑ j, T.eps e j) * (f * ∏ j, T.mu x₀ e j ^ m)) := by
  have heq : T.ec x₀ e ^ (m * ∑ j, T.eps e j) * (f * ∏ j, T.mu x₀ e j ^ m) =
      (f * ∏ j, (x₀ - algebraMap C F (T.b j)) ^ m) *
        algebraMap C F (∏ j, T.kap e j ^ m) := by
    have : T.ec x₀ e ^ (m * ∑ j, T.eps e j) * ∏ j, T.mu x₀ e j ^ m =
        ∏ j, (T.ec x₀ e ^ T.eps e j * T.mu x₀ e j) ^ m := by
      rw [Finset.prod_pow (s := Finset.univ) (f := fun j ↦ T.ec x₀ e ^ T.eps e j * T.mu x₀ e j),
        Finset.prod_mul_distrib, mul_pow, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm _ m,
        Finset.prod_pow]
    rw [mul_left_comm, this]
    simp only [T.ec_pow_mul_mu hx₀, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
    ring
  rw [heq]
  have hadj : Algebra.adjoin C {T.ec x₀ e} = Algebra.adjoin C {x₀} := by
    have : T.ec x₀ e = algebraMap C F (T.c (T.par e))⁻¹ * x₀ +
        algebraMap C F (-(T.a (T.chi e) / T.c (T.par e))) := by
      have : algebraMap C F (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
      simp only [TreeData.ec, vcoord, map_inv₀, _root_.map_neg, map_div₀]
      field_simp
      ring
    rw [this]
    exact adjoin_affine (inv_ne_zero (T.hc _))
  refine isIntegral_of_adjoin_le hadj.ge ?_
  exact (isIntegral_clear T hx₀ hf).mul (isIntegral_algebraMap (x := (⟨_,
    Subalgebra.algebraMap_mem _ (∏ j, T.kap e j ^ m)⟩ : Algebra.adjoin C {x₀})))

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **The twist is in the normalized node chart**: `f Πⱼ μⱼᵐ` is integral over `O_C[x̃, c_e/x̃]`
(in the `C(X)`-structure of the edge coordinate `x̃`). -/
theorem isIntegral_twist {m : ℕ} {f : F} (hf : f ∈ rrSpace (T.D x₀ m))
    (hn : ∀ (i : T.ι) (W : TypeTwo C F), IsOver (T.hvc hx₀ i) W → W.val f ≤ 1) (e : T.E) :
    letI : Algebra (RatFunc C) F := (coordAlgHom (T.hec hx₀ e)).toRingHom.toAlgebra
    IsIntegral (nodeRing (T.ce e)) (f * ∏ j, T.mu x₀ e j ^ m) := by
  have hout (W : TypeTwo C F) (hW : IsOver (T.hec hx₀ e) W) :
      W.val (f * ∏ j, T.mu x₀ e j ^ m) ≤ 1 := by
    have hW' := (T.isOver_ec_iff hx₀ e W).2 hW
    rw [map_mul, map_prod]
    simp only [map_pow, valuation_mu_par T hx₀ hW', one_pow, Finset.prod_const_one, mul_one]
    exact hn _ W hW'
  have hin (W : TypeTwo C F) (hW : IsOver (T.hinner hx₀ e) W) :
      W.val (f * ∏ j, T.mu x₀ e j ^ m) ≤ 1 := by
    have hW' := (T.isOver_inner_iff hx₀ e W).2 hW
    rw [map_mul, map_prod]
    simp only [map_pow, valuation_mu_chi T hx₀ hW', one_pow, Finset.prod_const_one, mul_one]
    exact hn _ W hW'
  exact isIntegral_nodeRing hp hp1 (T.hec hx₀ e) (T.ce_ne_zero e) (T.hinner hx₀ e)
    (isIntegral_ec_pow_mul T hx₀ hf e) hout hin

section Residues

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
include hx₀ in
lemma TreeData.mu_eq_one (e : T.E) (j : T.ι) (h1 : ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖) :
    T.mu x₀ e j = 1 - algebraMap C F ((T.b j - T.a (T.chi e)) / T.c (T.chi e)) *
      (algebraMap C F (T.ce e) / T.ec x₀ e) := by
  have hcp : algebraMap C F (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  have hcc : algebraMap C F (T.c (T.chi e)) ≠ 0 := by simpa using T.hc (T.chi e)
  have hxa : x₀ - algebraMap C F (T.a (T.chi e)) ≠ 0 := xF_sub_ne_zero hx₀ _
  rw [T.ec_eq_mul (x₀ := x₀) e] at hxa
  have hec0 : T.ec x₀ e ≠ 0 := right_ne_zero_of_mul hxa
  have hx : x₀ = algebraMap C F (T.c (T.par e)) * T.ec x₀ e + algebraMap C F (T.a (T.chi e)) := by
    rw [← T.ec_eq_mul (x₀ := x₀) e]
    ring
  unfold TreeData.mu
  rw [if_pos h1]
  generalize T.ec x₀ e = E at hx hec0 ⊢
  subst hx
  simp only [TreeData.ce, map_div₀, _root_.map_sub]
  field_simp
  ring

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
lemma TreeData.mu_eq_sub (e : T.E) (j : T.ι) (h1 : ¬ ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖)
    (h2 : ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.par e)‖) :
    T.mu x₀ e j = T.ec x₀ e - algebraMap C F ((T.b j - T.a (T.chi e)) / T.c (T.par e)) := by
  have hcp : algebraMap C F (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  unfold TreeData.mu
  rw [if_neg h1, if_pos h2]
  simp only [TreeData.ec, vcoord, map_div₀, _root_.map_sub]
  field_simp
  ring

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
lemma TreeData.mu_eq_add (e : T.E) (j : T.ι) (h1 : ¬ ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖)
    (h2 : ¬ ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.par e)‖) :
    T.mu x₀ e j = 1 + algebraMap C F (T.c (T.par e) / (T.a (T.chi e) - T.b j)) * T.ec x₀ e := by
  have hcp : algebraMap C F (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  have hab : algebraMap C F (T.a (T.chi e) - T.b j) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap C F).injective, sub_eq_zero]
    intro h
    apply h2
    rw [← h, sub_self, norm_zero]
    exact norm_nonneg _
  unfold TreeData.mu
  rw [if_neg h1, if_neg h2]
  simp only [TreeData.ec, vcoord, map_div₀]
  rw [_root_.map_sub] at hab ⊢
  field_simp
  ring

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
/-- An element close to a constant reduces to the residue of the constant. -/
lemma red_eq_residue {W : TypeTwo C F} {y : F} {γ : C} (hγ : ‖γ‖ ≤ 1)
    (h : W.val (y - algebraMap C F γ) < 1) :
    W.val y ≤ 1 ∧ W.red y = algebraMap 𝓀 (ResidueField W.val.valuationSubring)
      (residue (HenselComplete.integers C) ⟨γ, (HenselComplete.mem_integers_iff γ).2 hγ⟩) := by
  have hγ' : W.val (algebraMap C F γ) ≤ 1 := by
    rw [TypeTwo.valuation_algebraMap]; exact_mod_cast hγ
  have hy : W.val y ≤ 1 := by
    have : y = (y - algebraMap C F γ) + algebraMap C F γ := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le h.le hγ')
  exact ⟨hy, by rw [TypeTwo.red_eq_of_sub hy hγ' h, TypeTwo.red_algebraMap _ hγ]⟩

lemma residue_ne_zero_of_norm_eq_one {γ : C} (hγ : ‖γ‖ = 1) :
    residue (HenselComplete.integers C) ⟨γ, (HenselComplete.mem_integers_iff γ).2 hγ.le⟩ ≠ 0 := by
  rw [Ne, residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
  simp [hγ]

/-- **The twist is a unit at the outer branches.** -/
lemma res_red_mu_par {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.par e)) W)
    (Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring))
    (hQ : Q.valuation (W.red (T.ec x₀ e)) < 1) (j : T.ι) :
    W.red (T.mu x₀ e j) ∈ Q.V ∧ Q.res (W.red (T.mu x₀ e j)) ≠ 0 := by
  have hec : W.val (T.ec x₀ e) = 1 := ((T.isOver_ec_iff hx₀ e W).1 hW).valuation_self
  have hce : ‖T.ce e‖ < 1 := T.norm_ce_lt_one e
  -- the reduction is a nonzero constant
  have hconst (γ : C) (hγ : ‖γ‖ = 1) (h : W.val (T.mu x₀ e j - algebraMap C F γ) < 1) :
      W.red (T.mu x₀ e j) ∈ Q.V ∧ Q.res (W.red (T.mu x₀ e j)) ≠ 0 := by
    rw [(red_eq_residue hγ.le h).2, Q.res_algebraMap]
    exact ⟨Q.algebraMap_mem _, residue_ne_zero_of_norm_eq_one hγ⟩
  by_cases h1 : ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖
  · refine hconst 1 (by simp) ?_
    rw [T.mu_eq_one hx₀ e j h1, map_one, sub_sub_cancel_left, Valuation.map_neg, map_mul,
      TypeTwo.valuation_algebraMap, map_div₀ W.val, TypeTwo.valuation_algebraMap, hec, div_one]
    have hβ : ‖(T.b j - T.a (T.chi e)) / T.c (T.chi e)‖₊ ≤ 1 := by
      rw [nnnorm_div, div_le_one (nnnorm_pos.2 (T.hc _))]; exact_mod_cast h1
    calc ‖(T.b j - T.a (T.chi e)) / T.c (T.chi e)‖₊ * ‖T.ce e‖₊ ≤ 1 * ‖T.ce e‖₊ := by gcongr
      _ < 1 := by rw [one_mul]; exact_mod_cast hce
  by_cases h2 : ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.par e)‖
  · -- `μ = x̃ - δ` with `|δ| = 1`
    have hδ : ‖(T.b j - T.a (T.chi e)) / T.c (T.par e)‖ = 1 := by
      rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 (T.hc _))]
      exact le_antisymm h2 (T.norm_b_sub e j h1)
    have hδv : W.val (algebraMap C F ((T.b j - T.a (T.chi e)) / T.c (T.par e))) ≤ 1 := by
      rw [TypeTwo.valuation_algebraMap]; exact_mod_cast hδ.le
    have hecV : W.red (T.ec x₀ e) ∈ Q.V := Q.valuation_le_one_iff.1 hQ.le
    rw [T.mu_eq_sub e j h1 h2, TypeTwo.red_sub hec.le hδv, TypeTwo.red_algebraMap _ hδ.le]
    refine ⟨sub_mem hecV (Q.algebraMap_mem _), ?_⟩
    rw [Q.res_sub_algebraMap hecV, Q.res_eq_zero_of_lt_one hQ, zero_sub, neg_ne_zero]
    exact residue_ne_zero_of_norm_eq_one hδ
  · refine hconst 1 (by simp) ?_
    rw [T.mu_eq_add e j h1 h2, map_one, add_sub_cancel_left, map_mul, hec, mul_one,
      TypeTwo.valuation_algebraMap, nnnorm_div]
    have h3 : ‖T.c (T.par e)‖ < ‖T.a (T.chi e) - T.b j‖ := by
      rw [← norm_neg (T.a (T.chi e) - T.b j), neg_sub]; exact not_le.1 h2
    have h3' : ‖T.c (T.par e)‖₊ < ‖T.a (T.chi e) - T.b j‖₊ := by exact_mod_cast h3
    exact (div_lt_one (lt_of_le_of_lt zero_le h3')).2 h3'

/-- **The twist is a unit at the inner branches.** -/
lemma res_red_mu_chi {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.chi e)) W)
    (Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring))
    (hQ : Q.valuation (W.red (algebraMap C F (T.ce e) / T.ec x₀ e)) < 1) (j : T.ι) :
    W.red (T.mu x₀ e j) ∈ Q.V ∧ Q.res (W.red (T.mu x₀ e j)) ≠ 0 := by
  have hvc : W.val (T.vc x₀ (T.chi e)) = 1 := hW.valuation_self
  have hec : W.val (T.ec x₀ e) = ‖T.ce e‖₊ := by
    rw [T.vc_chi_eq (x₀ := x₀) e, map_mul, TypeTwo.valuation_algebraMap, hvc, mul_one]
  have hce : ‖T.ce e‖₊ < 1 := by exact_mod_cast T.norm_ce_lt_one e
  have hinner : W.val (algebraMap C F (T.ce e) / T.ec x₀ e) = 1 := by
    rw [T.inner_eq (x₀ := x₀) e, map_inv₀, hvc, inv_one]
  have hconst (γ : C) (hγ : ‖γ‖ = 1) (h : W.val (T.mu x₀ e j - algebraMap C F γ) < 1) :
      W.red (T.mu x₀ e j) ∈ Q.V ∧ Q.res (W.red (T.mu x₀ e j)) ≠ 0 := by
    rw [(red_eq_residue hγ.le h).2, Q.res_algebraMap]
    exact ⟨Q.algebraMap_mem _, residue_ne_zero_of_norm_eq_one hγ⟩
  by_cases h1 : ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.chi e)‖
  · -- `μ = 1 - β' ȳ`
    set β' := (T.b j - T.a (T.chi e)) / T.c (T.chi e)
    have hβ : ‖β'‖ ≤ 1 := by
      simp only [β', norm_div]
      rw [div_le_one (norm_pos_iff.2 (T.hc _))]; exact h1
    have hβ' : W.val (algebraMap C F β') ≤ 1 := by
      rw [TypeTwo.valuation_algebraMap]; exact_mod_cast hβ
    have hprod : W.val (algebraMap C F β' * (algebraMap C F (T.ce e) / T.ec x₀ e)) ≤ 1 := by
      rw [map_mul, hinner, mul_one]; exact hβ'
    rw [T.mu_eq_one hx₀ e j h1, TypeTwo.red_sub (by simp) hprod, TypeTwo.red_one,
      TypeTwo.red_mul hβ' hinner.le, TypeTwo.red_algebraMap _ hβ]
    have hinV : W.red (algebraMap C F (T.ce e) / T.ec x₀ e) ∈ Q.V :=
      Q.valuation_le_one_iff.1 hQ.le
    have hsmall : Q.valuation (algebraMap 𝓀 _ (residue (HenselComplete.integers C)
        ⟨β', (HenselComplete.mem_integers_iff β').2 hβ⟩) *
          W.red (algebraMap C F (T.ce e) / T.ec x₀ e)) < 1 := by
      rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (Q.valuation_algebraMap_le_one _) zero_le hQ
    refine ⟨sub_mem (one_mem _) (Q.valuation_le_one_iff.1 hsmall.le), ?_⟩
    rw [Q.res_eq_of_valuation_sub_lt_one (c := 1) (by
      rw [map_one, sub_sub_cancel_left, Valuation.map_neg]; exact hsmall)]
    exact one_ne_zero
  by_cases h2 : ‖T.b j - T.a (T.chi e)‖ ≤ ‖T.c (T.par e)‖
  · set δ := (T.b j - T.a (T.chi e)) / T.c (T.par e)
    have hδ : ‖-δ‖ = 1 := by
      simp only [δ, norm_neg, norm_div]
      rw [div_eq_one_iff_eq (norm_ne_zero_iff.2 (T.hc _))]
      exact le_antisymm h2 (T.norm_b_sub e j h1)
    refine hconst (-δ) hδ ?_
    rw [T.mu_eq_sub e j h1 h2, _root_.map_neg, sub_neg_eq_add, sub_add_cancel, hec]
    exact hce
  · refine hconst 1 (by simp) ?_
    rw [T.mu_eq_add e j h1 h2, map_one, add_sub_cancel_left, map_mul, hec,
      TypeTwo.valuation_algebraMap, nnnorm_div]
    have h3 : ‖T.c (T.par e)‖ < ‖T.a (T.chi e) - T.b j‖ := by
      rw [← norm_neg (T.a (T.chi e) - T.b j), neg_sub]; exact not_le.1 h2
    have h3' : ‖T.c (T.par e)‖₊ < ‖T.a (T.chi e) - T.b j‖₊ := by exact_mod_cast h3
    calc ‖T.c (T.par e)‖₊ / ‖T.a (T.chi e) - T.b j‖₊ * ‖T.ce e‖₊ ≤ 1 * ‖T.ce e‖₊ := by
          gcongr
          exact ((div_lt_one (lt_of_le_of_lt zero_le h3')).2 h3').le
      _ < 1 := by rw [one_mul]; exact hce

end Residues


end Twist



end TreeCount

end SemistableReduction
