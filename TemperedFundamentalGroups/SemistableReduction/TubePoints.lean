/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTube

/-!
# Points over the node and the constancy of their tube degrees

Blueprint §9.9, W7 layer S5 (points). Let `nodeRing c = O_C[x, c/x]` (`0 < |c| < 1`) and
`F' / C(x)` finite separable, `R' = integralClosure (nodeRing c) F'`.

* `nodeRing` is integrally closed with fraction field `C(x)` (`isIntegrallyClosed_nodeRing`,
  `isFractionRing_nodeRing`, from `AnnulusModel.isIntegrallyClosed_nodeChart`), so the
  characteristic polynomial of an element integral over `nodeRing` has coefficients in `nodeRing`
  (`exists_lift_normPoly`);
* integral elements have value `≤ 1` at every extension `w'` of a Gauss point `w_{0,s}` of the
  open segment (`valuation_le_one_of_isIntegral`);
* `center w'`: the centre `{y ∈ R' : w'(y) < 1}` of an extension `w'` of `w_{0,s}`, a maximal
  ideal of `R'` over the node (`center_isMaximal`, `comap_center`);
* `tubeDegree s P' = Σ_{w' ∣ w_{0,s}, centre w' = P'} e(w') f(w')`;
* **`tubeDegree_eq`**: for `s, s'` in the open segment, `tubeDegree s P' = tubeDegree s' P'`.
  Proof: an element `e ∈ R'` with `e ≡ 1` at `P'` and `e ∈ Q` for the (finitely many) other
  centres at `s` and `s'` (products of elements of `Q` that are `≡ 1` at `P'`; no Chinese remainder
  theorem or finiteness of `R'` needed); then `w'(e - 1) < 1` iff `centre w' = P'`, and the tube
  count (`GaussTube.sum_ramificationIdx_mul_inertiaDeg_eq`) of `e - 1` does not depend on `s`.
-/

open Polynomial NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability TubeCount ZariskiModel IntermediateField

universe u

section Integral

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

lemma isGaussCoord_X :
    IsGaussCoord (NormedField.valuation (K := C))
      (gaussRat (NormedField.valuation (K := C)) 0 1) RatFunc.X := by
  have := isGaussCoord_gaussCoord (v := NormedField.valuation (K := C)) (a := 0) (c := 1)
    (r := 1) (by simp)
  convert this using 1
  simp [gaussCoord, gaussLin]

theorem isIntegrallyClosed_nodeRing {c : C} (hc0 : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    IsIntegrallyClosed (nodeRing c) :=
  isIntegrallyClosed_nodeChart isGaussCoord_X hc0
    (by rw [NormedField.valuation_apply]; exact_mod_cast hc1)

lemma algebraMap_mem_nodeRing {c b : C} (hb : ‖b‖ ≤ 1) :
    algebraMap C (RatFunc C) b ∈ nodeRing c := by
  refine baseRing_le_nodeChart ⟨b, ?_, rfl⟩
  change NormedField.valuation b ≤ 1
  rw [NormedField.valuation_apply]
  exact_mod_cast hb

lemma polynomial_mem_nodeRing (c : C) {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) :
    algebraMap C[X] (RatFunc C) Q ∈ nodeRing c := by
  rw [Q.as_sum_range_C_mul_X_pow, map_sum]
  refine Subring.sum_mem _ fun i _ ↦ ?_
  rw [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  exact Subring.mul_mem _ (by simpa [RatFunc.algebraMap_C] using algebraMap_mem_nodeRing (hQ i))
    (Subring.pow_mem _ (self_mem_nodeChart (v := NormedField.valuation (K := C))) _)

omit [IsUltrametricDist C] in
lemma exists_scale (Q : C[X]) : ∃ d : C, d ≠ 0 ∧ ‖d‖ ≤ 1 ∧ ∀ i, ‖d * Q.coeff i‖ ≤ 1 := by
  classical
  rcases Q.support.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_ne_zero, by simp, fun i ↦ ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem] at h
    have := h i
    rw [mem_support_iff, not_not] at this
    simp [this]
  obtain ⟨j, hj, hmax⟩ := Q.support.exists_max_image (fun i ↦ ‖Q.coeff i‖) h
  have hj0 : Q.coeff j ≠ 0 := mem_support_iff.1 hj
  have hle : ∀ i, ‖Q.coeff i‖ ≤ ‖Q.coeff j‖ := fun i ↦ by
    by_cases hi : i ∈ Q.support
    · exact hmax i hi
    · rw [notMem_support_iff.1 hi, norm_zero]
      exact norm_nonneg _
  by_cases h1 : ‖Q.coeff j‖ ≤ 1
  · exact ⟨1, one_ne_zero, by simp, fun i ↦ by rw [one_mul]; exact (hle i).trans h1⟩
  · push Not at h1
    refine ⟨(Q.coeff j)⁻¹, inv_ne_zero hj0, ?_, fun i ↦ ?_⟩
    · rw [norm_inv]
      exact inv_le_one_of_one_le₀ h1.le
    · rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hj0), mul_one]
      exact hle i

theorem isFractionRing_nodeRing (c : C) : IsFractionRing (nodeRing c) (RatFunc C) := by
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨d₁, hd₁0, hd₁, h₁⟩ := exists_scale z.num
  obtain ⟨d₂, hd₂0, hd₂, h₂⟩ := exists_scale z.denom
  have hmem : ∀ (Q : C[X]) (d d' : C), ‖d'‖ ≤ 1 → (∀ i, ‖d * Q.coeff i‖ ≤ 1) →
      algebraMap C[X] (RatFunc C) (Polynomial.C (d * d') * Q) ∈ nodeRing c := by
    intro Q d d' hd' hQ
    refine polynomial_mem_nodeRing c fun i ↦ ?_
    rw [coeff_C_mul, mul_comm d d', mul_assoc, norm_mul]
    exact mul_le_one₀ hd' (norm_nonneg _) (hQ i)
  refine ⟨⟨_, hmem z.num d₁ d₂ hd₂ h₁⟩, ⟨_, hmem z.denom d₂ d₁ hd₁ h₂⟩, ?_⟩
  change z = algebraMap C[X] (RatFunc C) (Polynomial.C (d₁ * d₂) * z.num) /
    algebraMap C[X] (RatFunc C) (Polynomial.C (d₂ * d₁) * z.denom)
  rw [mul_comm d₂ d₁, map_mul (algebraMap C[X] (RatFunc C)) (Polynomial.C (d₁ * d₂)) z.num,
    map_mul (algebraMap C[X] (RatFunc C)) (Polynomial.C (d₁ * d₂)) z.denom,
    mul_div_mul_left _ _ (by simp [hd₁0, hd₂0]), RatFunc.num_div_denom]

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

/-- The characteristic polynomial of an element integral over the node chart has coefficients in
the node chart. -/
theorem exists_lift_normPoly {c : C} (hc0 : c ≠ 0) (hc1 : ‖c‖ ≤ 1) {y : F'}
    (hy : IsIntegral (nodeRing c) y) :
    ∃ P : (nodeRing c)[X], P.map (nodeRing c).subtype = normPoly (RatFunc C) y := by
  haveI := isIntegrallyClosed_nodeRing hc0 hc1
  haveI := isFractionRing_nodeRing c
  refine ⟨minpoly (nodeRing c) y ^ Module.finrank (RatFunc C)⟮y⟯ F', ?_⟩
  rw [Polynomial.map_pow, normPoly, minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc C) hy]
  rfl

/-- An element integral over the node chart has value `≤ 1` at every extension of a Gauss point
of the open segment. -/
theorem valuation_le_one_of_isIntegral {c : C} {s : ℝ≥0ˣ} (hs : s ∈ segment c)
    (w' : GaussExtension (0 : C) s F') {y : F'} (hy : IsIntegral (nodeRing c) y) :
    w'.1 y ≤ 1 := by
  let φ : nodeRing c →+* w'.1.integer :=
    { toFun := fun a ↦ ⟨algebraMap (RatFunc C) F' a, by
        change w'.1 _ ≤ 1
        rw [← Valuation.comap_apply, w'.2]
        exact gaussRat_le_one a.2 hs⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hint : IsIntegral w'.1.integer y :=
    IsIntegral.map_of_comp_eq φ (RingHom.id F') (by ext; rfl) hy
  exact (Valuation.integer.integers w'.1).mem_of_integral hint

/-- The node ideal is maximal (its residue field is `k`). -/
theorem tubeIdeal_isMaximal {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0) : (tubeIdeal c).IsMaximal := by
  obtain ⟨s, hs⟩ : (segment c).Nonempty := by
    obtain ⟨t, ht1, ht2⟩ := exists_between hc
    refine ⟨Units.mk0 ⟨t, (norm_nonneg c).trans ht1.le⟩ ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) h
      simp only [NNReal.coe_zero] at this
      exact (norm_pos_iff.2 hc0).ne' (le_antisymm (this ▸ ht1.le) (norm_nonneg c))
    · change ‖c‖₊ < ⟨t, _⟩
      exact_mod_cast ht1
    · change (⟨t, _⟩ : ℝ≥0) < 1
      exact_mod_cast ht2
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h ↦ by simp [mem_tubeIdeal_iff _ hs] at h, fun J x hJ hx hxJ ↦ ?_⟩
  obtain ⟨κ, hκ, h⟩ := exists_const x.2
  have hκ1 : ‖κ‖ = 1 := le_antisymm hκ (not_lt.1 fun hlt ↦
    hx ((mem_tubeIdeal_iff x hs).2 ((gaussRat_lt_one_iff h hs).2 hlt)))
  have hκ0 : κ ≠ 0 := norm_ne_zero_iff.1 (by rw [hκ1]; exact one_ne_zero)
  let b : nodeRing c := ⟨algebraMap C (RatFunc C) κ⁻¹,
    algebraMap_mem_nodeRing (by rw [norm_inv, hκ1, inv_one])⟩
  have hmem : x * b - 1 ∈ tubeIdeal c := by
    refine (mem_tubeIdeal_iff _ hs).2 ?_
    have hk : algebraMap C (RatFunc C) κ ≠ 0 := by simpa using hκ0
    have : ((x * b - 1 : nodeRing c) : RatFunc C) =
        ((x : RatFunc C) - algebraMap C (RatFunc C) κ) * algebraMap C (RatFunc C) κ⁻¹ := by
      change (x : RatFunc C) * algebraMap C (RatFunc C) κ⁻¹ - 1 = _
      rw [map_inv₀, sub_mul, mul_inv_cancel₀ hk]
    rw [this, map_mul, gaussRat_C, nnnorm_inv]
    have : ‖κ‖₊ = 1 := by ext; simpa using hκ1
    rw [this, inv_one, mul_one]
    exact h s hs
  have := J.sub_mem (J.mul_mem_right b hxJ) (hJ hmem)
  simpa using this

end Integral

section Points

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] {c : C}
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

variable (c F') in
/-- The integral closure `R'` of the node chart in `F'`. -/
noncomputable abbrev Rint : Subalgebra (nodeRing c) F' := integralClosure (nodeRing c) F'

/-- The centre `{y ∈ R' : w'(y) < 1}` of an extension `w'` of a Gauss point of the open
segment. -/
noncomputable def center {s : ℝ≥0ˣ} (hs : s ∈ segment c) (w' : GaussExtension (0 : C) s F') :
    Ideal (Rint c F') where
  carrier := {y | w'.1 (y : F') < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at ha hb ⊢
    exact (Valuation.map_add _ _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' r y hy := by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Subalgebra.coe_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (valuation_le_one_of_isIntegral hs w' r.2)
      zero_le hy

lemma mem_center_iff {s : ℝ≥0ˣ} (hs : s ∈ segment c) (w' : GaussExtension (0 : C) s F')
    (y : Rint c F') : y ∈ center hs w' ↔ w'.1 (y : F') < 1 := Iff.rfl

lemma comap_center {s : ℝ≥0ˣ} (hs : s ∈ segment c) (w' : GaussExtension (0 : C) s F') :
    (center hs w').comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c := by
  ext a
  rw [Ideal.mem_comap, mem_center_iff, mem_tubeIdeal_iff a hs]
  change w'.1 (algebraMap (RatFunc C) F' a) < 1 ↔ _
  rw [← Valuation.comap_apply, w'.2]

theorem center_isPrime {s : ℝ≥0ˣ} (hs : s ∈ segment c) (w' : GaussExtension (0 : C) s F') :
    (center hs w').IsPrime := by
  refine ⟨fun h ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · have : (1 : Rint c F') ∈ center hs w' := h ▸ Submodule.mem_top
    simp [mem_center_iff] at this
  · rw [mem_center_iff, Subalgebra.coe_mul, map_mul] at hxy
    by_contra! H
    rw [mem_center_iff, mem_center_iff, not_lt, not_lt] at H
    have h1 := le_antisymm (valuation_le_one_of_isIntegral hs w' x.2) H.1
    have h2 := le_antisymm (valuation_le_one_of_isIntegral hs w' y.2) H.2
    rw [h1, h2, mul_one] at hxy
    exact lt_irrefl 1 hxy

theorem center_isMaximal (hc : ‖c‖ < 1) (hc0 : c ≠ 0) {s : ℝ≥0ˣ} (hs : s ∈ segment c)
    (w' : GaussExtension (0 : C) s F') : (center hs w').IsMaximal := by
  haveI := center_isPrime hs w'
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := nodeRing c) _ ?_
  rw [comap_center]
  exact tubeIdeal_isMaximal hc hc0

open Classical in
/-- The **tube degree** of a point `P'` of `Spec R'` at the radius `s`: the sum of the local
degrees `e f` of the extensions of `w_{0,s}` centred at `P'`. -/
noncomputable def tubeDegree {s : ℝ≥0ˣ} (hs : s ∈ segment c)
    [Fintype (GaussExtension (0 : C) s F')] (P' : Ideal (Rint c F')) : ℕ :=
  ∑ w' ∈ Finset.univ.filter (fun w' : GaussExtension (0 : C) s F' ↦ center hs w' = P'),
    ramificationIdx (RatFunc C) w'.1 *
      inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 s) w'.1

/-- A separating element: `e ≡ 1` at the maximal ideal `P'`, `e ∈ Q` for finitely many other
maximal ideals `Q`. -/
lemma exists_separating {R : Type*} [CommRing R] (P' : Ideal R) [hP' : P'.IsMaximal]
    (T : Finset (Ideal R)) (hT : ∀ Q ∈ T, Q.IsMaximal ∧ Q ≠ P') :
    ∃ e : R, e - 1 ∈ P' ∧ ∀ Q ∈ T, e ∈ Q := by
  classical
  have h : ∀ Q ∈ T, ∃ a ∈ Q, a - 1 ∈ P' := by
    intro Q hQ
    have hsup := (hT Q hQ).1.coprime_of_ne hP' (hT Q hQ).2
    have h1 : (1 : R) ∈ Q ⊔ P' := hsup ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨a, ha, ?_⟩
    rw [show a - 1 = -b by rw [← hab]; ring]
    exact P'.neg_mem hb
  choose! a ha using h
  refine ⟨∏ Q ∈ T, a Q, ?_, fun Q hQ ↦ ?_⟩
  · rw [← Ideal.Quotient.eq, map_prod, map_one]
    refine Finset.prod_eq_one fun Q hQ ↦ ?_
    rw [← map_one (Ideal.Quotient.mk P'), Ideal.Quotient.eq]
    exact (ha Q hQ).2
  · rw [← Finset.mul_prod_erase T a hQ]
    exact Q.mul_mem_right _ (ha Q hQ).1

variable [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [FiniteDimensional (RatFunc C) F'] [Algebra.IsSeparable (RatFunc C) F']

include hp hp1 in
/-- **Constancy of the tube degree along the open segment** (S5): for a maximal ideal `P'` of
`R'` and two radii `s, s'` of the open segment (in the value group of `C`),
`tubeDegree s P' = tubeDegree s' P'`. -/
theorem tubeDegree_eq (hc : ‖c‖ < 1) (hc0 : c ≠ 0) {s s' : ℝ≥0ˣ} (hs : s ∈ segment c)
    (hs' : s' ∈ segment c) {cs cs' : C} (hcs : NormedField.valuation cs = (s : ℝ≥0))
    (hcs' : NormedField.valuation cs' = (s' : ℝ≥0)) [Fintype (GaussExtension (0 : C) s F')]
    [Fintype (GaussExtension (0 : C) s' F')] (P' : Ideal (Rint c F')) [P'.IsMaximal] :
    tubeDegree hs P' = tubeDegree hs' P' := by
  classical
  set T : Finset (Ideal (Rint c F')) :=
    (Finset.univ.image (center hs) ∪ Finset.univ.image (center hs')).erase P'
  obtain ⟨e, he1, heQ⟩ := exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    refine ⟨?_, hne⟩
    rcases Finset.mem_union.1 hQ with hQ | hQ <;> obtain ⟨w', -, rfl⟩ := Finset.mem_image.1 hQ
    exacts [center_isMaximal hc hc0 hs w', center_isMaximal hc hc0 hs' w']
  set y : Rint c F' := e - 1
  obtain ⟨P, hP⟩ := exists_lift_normPoly hc0 hc.le y.2
  have key : ∀ {t : ℝ≥0ˣ} (ht : t ∈ segment c) (w' : GaussExtension (0 : C) t F'),
      center ht w' ∈ Finset.univ.image (center hs) ∪ Finset.univ.image (center hs') →
      (w'.1 (y : F') < 1 ↔ center ht w' = P') := by
    intro t ht w' hmem
    constructor
    · intro hlt
      by_contra hne
      have he : w'.1 (e : F') < 1 :=
        (mem_center_iff ht w' e).1 (heQ _ (Finset.mem_erase.2 ⟨hne, hmem⟩))
      have : w'.1 ((y : F')) = 1 := by
        rw [show (y : F') = -1 + (e : F') by simp [y]; ring,
          Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, map_one]; exact he),
          Valuation.map_neg, map_one]
      exact lt_irrefl 1 (this ▸ hlt)
    · intro h
      rw [← mem_center_iff ht, h]
      exact he1
  have hcount : ∀ {t : ℝ≥0ˣ} (ht : t ∈ segment c) {ct : C}
      (hct : NormedField.valuation ct = (t : ℝ≥0)) [Fintype (GaussExtension (0 : C) t F')],
      (∀ w' : GaussExtension (0 : C) t F', center ht w' ∈
        Finset.univ.image (center hs) ∪ Finset.univ.image (center hs')) →
      tubeDegree ht P' = (P.map (Ideal.Quotient.mk (tubeIdeal c))).natTrailingDegree := by
    intro t ht ct hct _ hall
    rw [← sum_ramificationIdx_mul_inertiaDeg_eq hp hp1 hct ht (y : F') P hP
      fun w' ↦ valuation_le_one_of_isIntegral ht w' y.2, tubeDegree]
    exact Finset.sum_congr (Finset.filter_congr fun w' _ ↦ (key ht w' (hall w')).symm) fun _ _ ↦
      rfl
  rw [hcount hs hcs fun w' ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ w')),
    hcount hs' hcs' fun w' ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ w'))]

end Points

end GaussTube

end SemistableReduction
