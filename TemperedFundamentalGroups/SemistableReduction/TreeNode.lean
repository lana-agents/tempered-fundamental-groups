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

end Twist


end TreeCount

end SemistableReduction
