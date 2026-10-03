/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TubePoints
import TemperedFundamentalGroups.SemistableReduction.GaussTreeNormal

/-!
# Counting extensions over a residue disc

Blueprint §9.10, layer L2 (B1, B2). Let `discRing = O_C[x] ⊆ C(x)` be the chart of the Gauss point
`w_{0,1}` (`polyChart`), and `discIdeal` its maximal ideal `(𝔪_C, x)` of the residue point
`x̄ = 0`, i.e. of the open disc `U = {|x| < 1}`. A *disc valuation* is a real valuation `ν` of
`C(x)` extending the norm of `C` with `ν(x) < 1` (a point of `U` of any type 1–4 that is a
valuation, in particular the Gauss points `w_{0,s}`, `s < 1`, and the type-4 points in `U`).

* `valuation_le_one`: disc valuations are `≤ 1` on `discRing`;
* **`mem_discIdeal_iff`**: for every disc valuation `ν`, `a ∈ discIdeal ↔ ν a < 1`; i.e. all
  points of `U` have the same centre on the chart (write `a = Q(0) + x · (Q div x)(x)`);
* **`sum_natDegree_eq_natTrailingDegree` (B1, the disc count)**: for `y ∈ F'` integral over
  `discRing` and a lift `P ∈ discRing[X]` of its characteristic polynomial, the sum of the local
  degrees `[\hat F'_{ν'} : \hat C(x)_ν]` over the extensions `ν'` of a disc valuation `ν` with
  `ν'(y) < 1` is `natTrailingDegree (P mod discIdeal)`: it does not depend on `ν`. This is S5's
  tube count (`TubeCount.sum_natDegree_eq_natTrailingDegree`) for the disc chart; the local
  degrees are the degrees of the factors of the minimal polynomial over the completion
  (`LocalGlobal`), which is how they enter at type-4 points (where they are defects).
* `isIntegrallyClosed_discRing`, `exists_lift_normPoly`: lifts of characteristic polynomials of
  integral elements exist; `discIdeal_isMaximal`;
* `DRint`, `center`: the integral closure `R'` of the chart in `F'` and the centre
  `{y : w'(y) < 1}` of a valuation over a disc valuation, a maximal ideal over `discIdeal`
  (`center_isMaximal`, `comap_center`);
* **`discDegree_eq` (B2)**: the *disc degree* of a maximal ideal `P'` of `R'` (the sum of the
  local degrees of the extensions of `ν` centred at `P'`) is the same for all disc valuations
  `ν`. In particular, at a type-4 point `ξ` of the disc it equals the disc degree at any Gauss
  point `w_{0,s}`, `s < 1` (`isDiscVal_gaussRat`).
-/

open Polynomial NNReal IntermediateField

namespace SemistableReduction

namespace DiscCount

open TubeCount LocalGlobal GaussTube DenseCompletion

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

/-! ### The disc chart -/

variable (C) in
/-- The chart `O_C[x]` of the Gauss point `w_{0,1}`. -/
noncomputable abbrev discRing : Subring (RatFunc C) :=
  polyChart (NormedField.valuation (K := C)) RatFunc.X

/-- The coefficients of a polynomial with Gauss norm `≤ 1` have norm `≤ 1`. -/
lemma nnnorm_coeff_le_one {Q : C[X]} (hQ : Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1)
    (i : ℕ) : ‖Q.coeff i‖₊ ≤ 1 :=
  coeff_le_one_of_sup_le_one hQ i

/-- A real valuation of `C(x)` extending the norm of `C` with `ν(x) < 1`: a point of the open
disc `|x| < 1`. -/
structure IsDiscVal (ν : Valuation (RatFunc C) ℝ≥0) : Prop where
  map_C : ∀ c : C, ν (algebraMap C (RatFunc C) c) = ‖c‖₊
  X_lt_one : ν RatFunc.X < 1

variable {ν : Valuation (RatFunc C) ℝ≥0}

omit [IsUltrametricDist C] in
/-- A polynomial in `x` with integral coefficients has value `≤ 1` at a disc valuation. -/
lemma valuation_aeval_le_one (hν : IsDiscVal ν) {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖₊ ≤ 1) :
    ν (aeval RatFunc.X Q) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, map_pow, hν.map_C]
  exact mul_le_one' (hQ i) (pow_le_one₀ zero_le hν.X_lt_one.le)

/-- Disc valuations are `≤ 1` on the disc chart. -/
lemma valuation_le_one (hν : IsDiscVal ν) {a : RatFunc C} (ha : a ∈ discRing C) : ν a ≤ 1 := by
  obtain ⟨Q, hQ, rfl⟩ := mem_polyChart_iff.1 ha
  exact valuation_aeval_le_one hν (nnnorm_coeff_le_one hQ)

omit [IsUltrametricDist C] in
/-- **The value at a disc valuation is `< 1` iff the constant coefficient is in `𝔪_C`.** -/
lemma valuation_aeval_lt_one_iff (hν : IsDiscVal ν) {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖₊ ≤ 1) :
    ν (aeval RatFunc.X Q) < 1 ↔ ‖Q.coeff 0‖₊ < 1 := by
  have hdecomp : aeval RatFunc.X Q =
      algebraMap C (RatFunc C) (Q.coeff 0) + RatFunc.X * aeval RatFunc.X Q.divX := by
    conv_lhs => rw [← X_mul_divX_add Q]
    rw [map_add, map_mul, aeval_X, aeval_C, add_comm]
  have hrest : ν (RatFunc.X * aeval RatFunc.X Q.divX) < 1 := by
    rw [map_mul]
    refine (mul_le_of_le_one_right' ?_).trans_lt hν.X_lt_one
    exact valuation_aeval_le_one hν fun i ↦ by rw [coeff_divX]; exact hQ _
  rw [hdecomp]
  constructor
  · intro h
    by_contra h0
    have h1 : ν (algebraMap C (RatFunc C) (Q.coeff 0)) = 1 := by
      rw [hν.map_C]
      exact le_antisymm (hQ 0) (not_lt.1 h0)
    rw [Valuation.map_add_eq_of_lt_left _ (h1 ▸ hrest), h1] at h
    exact lt_irrefl _ h
  · intro h
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ hrest)
    rwa [hν.map_C]

variable (C) in
/-- The ideal `(𝔪_C, x)` of the disc chart: the centre of every point of the disc `|x| < 1`. -/
def discIdeal : Ideal (discRing C) where
  carrier := {a | ∃ Q : C[X], (∀ i, ‖Q.coeff i‖₊ ≤ 1) ∧ aeval RatFunc.X Q = (a : RatFunc C) ∧
    ‖Q.coeff 0‖₊ < 1}
  add_mem' := by
    rintro _ _ ⟨P, hP, hPa, hP0⟩ ⟨Q, hQ, hQa, hQ0⟩
    refine ⟨P + Q, fun i ↦ ?_, by rw [map_add, hPa, hQa]; rfl, ?_⟩
    · rw [coeff_add]
      exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le (hP i) (hQ i))
    · rw [coeff_add]
      exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans_lt (max_lt hP0 hQ0)
  zero_mem' := ⟨0, by simp, by simp, by simp⟩
  smul_mem' := by
    rintro ⟨_, hb⟩ _ ⟨Q, hQ, hQa, hQ0⟩
    obtain ⟨R, hR, rfl⟩ := mem_polyChart_iff.1 hb
    have hR' := nnnorm_coeff_le_one hR
    refine ⟨R * Q, fun i ↦ ?_, by rw [map_mul, hQa]; rfl, ?_⟩
    · rw [coeff_mul]
      refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun x _ ↦ ?_
      rw [nnnorm_mul]
      exact mul_le_one' (hR' _) (hQ _)
    · rw [mul_coeff_zero, nnnorm_mul]
      exact (mul_le_of_le_one_left' (hR' 0)).trans_lt hQ0

/-- **All points of the disc have the same centre on the chart.** -/
theorem mem_discIdeal_iff (hν : IsDiscVal ν) (a : discRing C) :
    a ∈ discIdeal C ↔ ν a < 1 := by
  constructor
  · rintro ⟨Q, hQ, hQa, hQ0⟩
    rw [← hQa]
    exact (valuation_aeval_lt_one_iff hν hQ).2 hQ0
  · intro h
    obtain ⟨Q, hQ, hQa⟩ := mem_polyChart_iff.1 a.2
    have hQ' := nnnorm_coeff_le_one hQ
    refine ⟨Q, hQ', hQa, ?_⟩
    rw [← hQa] at h
    exact (valuation_aeval_lt_one_iff hν hQ').1 h

/-! ### The chart is integrally closed -/

theorem isFractionRing_discRing : IsFractionRing (discRing C) (RatFunc C) :=
  isGaussCoord_X.isFractionRing_polyChart

theorem isIntegrallyClosed_discRing : IsIntegrallyClosed (discRing C) := by
  haveI := isFractionRing_discRing (C := C)
  let e : (NormedField.valuation (K := C)).valuationSubring[X] ≃+* discRing C :=
    (AlgEquiv.ofInjective _ (ZariskiModel.aeval_injective' isGaussCoord_X)).toRingEquiv.trans
      (RingEquiv.subringCongr (ZariskiModel.range_aeval _))
  exact IsIntegrallyClosed.of_equiv e

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

/-- The characteristic polynomial of an element integral over the disc chart has coefficients in
the disc chart. -/
theorem exists_lift_normPoly {y : F'} (hy : IsIntegral (discRing C) y) :
    ∃ P : (discRing C)[X], P.map (discRing C).subtype = normPoly (RatFunc C) y := by
  haveI := isIntegrallyClosed_discRing (C := C)
  haveI := isFractionRing_discRing (C := C)
  refine ⟨minpoly (discRing C) y ^ Module.finrank (RatFunc C)⟮y⟯ F', ?_⟩
  rw [Polynomial.map_pow, normPoly, minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc C) hy]
  rfl

/-- An element integral over the disc chart has value `≤ 1` at every valuation of `F'` whose
restriction to `C(x)` is a disc valuation. -/
theorem valuation_le_one_of_isIntegral {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal (w'.comap (algebraMap (RatFunc C) F'))) {y : F'}
    (hy : IsIntegral (discRing C) y) : w' y ≤ 1 := by
  let φ : discRing C →+* w'.integer :=
    { toFun := fun a ↦ ⟨algebraMap (RatFunc C) F' a, by
        change w' _ ≤ 1
        rw [← Valuation.comap_apply]
        exact valuation_le_one hw' a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hint : IsIntegral w'.integer y :=
    IsIntegral.map_of_comp_eq φ (RingHom.id F') (by ext; rfl) hy
  exact (Valuation.integer.integers w').mem_of_integral hint

/-! ### B1: the disc count -/

variable (ν) in
/-- `C(x)` with the absolute value of a disc valuation `ν`. -/
abbrev DiscField : Type u := WithAbs ν.toAbsoluteValue

omit [IsUltrametricDist C] in
lemma norm_algebraMap_discField [hν : Fact (IsDiscVal ν)] (c : C) :
    ‖algebraMap C (DiscField ν) c‖ = ‖c‖ := by
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs,
    Valuation.toAbsoluteValue_apply, hν.out.map_C, coe_nnnorm]

noncomputable instance [Fact (IsDiscVal ν)] : NormedAlgebra C (DiscField ν) where
  norm_smul_le c x := le_of_eq (by rw [Algebra.smul_def, norm_mul, norm_algebraMap_discField])

noncomputable instance [Fact (IsDiscVal ν)] : NontriviallyNormedField (DiscField ν) where
  __ : NormedField (DiscField ν) := inferInstance
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
    ⟨algebraMap C _ x, by rwa [norm_algebraMap_discField]⟩

/-! ### B2: points over the residue point and their disc degrees -/

/-- The Gauss points `w_{0,s}`, `s < 1`, are disc valuations. -/
lemma isDiscVal_gaussRat {s : ℝ≥0ˣ} (hs : (s : ℝ≥0) < 1) :
    IsDiscVal (gaussRat (NormedField.valuation (K := C)) 0 s) :=
  ⟨gaussRat_C s, by rw [gaussRat_X]; exact hs⟩

/-- Disc valuations exist (`w_{0,1/2}`). -/
lemma exists_isDiscVal : ∃ ν : Valuation (RatFunc C) ℝ≥0, IsDiscVal ν :=
  ⟨_, isDiscVal_gaussRat (s := Units.mk0 (1 / 2) (by norm_num)) (by
    change (1 / 2 : ℝ≥0) < 1
    rw [one_div]
    exact inv_lt_one_of_one_lt₀ (by norm_num))⟩

lemma algebraMap_mem_discRing {c : C} (hc : ‖c‖₊ ≤ 1) :
    algebraMap C (RatFunc C) c ∈ discRing C :=
  mem_polyChart_iff.2 ⟨Polynomial.C c, by rw [Gauss.sup_C, NormedField.valuation_apply]; exact hc,
    aeval_C _ _⟩

/-- **The disc ideal is maximal**: modulo `(𝔪_C, x)`, an element `Q(x)` with `|Q(0)| = 1` is
congruent to the unit `Q(0)`. -/
theorem discIdeal_isMaximal : (discIdeal C).IsMaximal := by
  obtain ⟨ν₀, hν₀⟩ := exists_isDiscVal (C := C)
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h ↦ ?_, fun J x hJ hx hxJ ↦ ?_⟩
  · rw [mem_discIdeal_iff hν₀] at h
    simp at h
  obtain ⟨Q, hQ, hQa⟩ := mem_polyChart_iff.1 x.2
  have hQ' := nnnorm_coeff_le_one hQ
  have hQ0 : ‖Q.coeff 0‖₊ = 1 :=
    le_antisymm (hQ' 0) (not_lt.1 fun h ↦ hx ⟨Q, hQ', hQa, h⟩)
  have hc0 : Q.coeff 0 ≠ 0 := by
    rintro h
    rw [h, nnnorm_zero] at hQ0
    exact zero_ne_one hQ0
  set c : discRing C := ⟨_, algebraMap_mem_discRing hQ0.le⟩
  set d : discRing C := ⟨algebraMap C (RatFunc C) (Q.coeff 0)⁻¹,
    algebraMap_mem_discRing (by rw [nnnorm_inv, hQ0, inv_one])⟩
  have hcd : d * c = 1 := Subtype.ext (by
    change algebraMap C (RatFunc C) _ * algebraMap C (RatFunc C) _ = 1
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one])
  have hxc : x - c ∈ discIdeal C := by
    refine ⟨Q - Polynomial.C (Q.coeff 0), fun i ↦ ?_, ?_, ?_⟩
    · rw [coeff_sub, coeff_C]
      split_ifs
      · subst_vars
        simp
      · rw [sub_zero]
        exact hQ' i
    · rw [map_sub, hQa, aeval_C]
      rfl
    · simp
  have hcJ : c ∈ J := by
    have := J.sub_mem hxJ (hJ hxc)
    rwa [sub_sub_cancel] at this
  rw [← hcd]
  exact J.mul_mem_left d hcJ

variable (C F') in
/-- The integral closure `R'` of the disc chart in `F'`. -/
noncomputable abbrev DRint : Subalgebra (discRing C) F' := integralClosure (discRing C) F'

/-- The centre `{y ∈ R' : w'(y) < 1}` of a valuation of `F'` over a disc valuation. -/
noncomputable def center {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal (w'.comap (algebraMap (RatFunc C) F'))) : Ideal (DRint C F') where
  carrier := {y | w' (y : F') < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at ha hb ⊢
    exact (Valuation.map_add _ _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' r y hy := by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Subalgebra.coe_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (valuation_le_one_of_isIntegral hw' r.2)
      zero_le hy

lemma mem_center_iff {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal (w'.comap (algebraMap (RatFunc C) F'))) (y : DRint C F') :
    y ∈ center hw' ↔ w' (y : F') < 1 := Iff.rfl

lemma comap_center {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal (w'.comap (algebraMap (RatFunc C) F'))) :
    (center hw').comap (algebraMap (discRing C) (DRint C F')) = discIdeal C := by
  ext a
  rw [Ideal.mem_comap, mem_center_iff, mem_discIdeal_iff hw' a]
  rfl

theorem center_isMaximal {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal (w'.comap (algebraMap (RatFunc C) F'))) : (center hw').IsMaximal := by
  have hprime : (center hw').IsPrime := by
    refine ⟨fun h ↦ ?_, fun {x y} hxy ↦ ?_⟩
    · have : (1 : DRint C F') ∈ center hw' := h ▸ Submodule.mem_top
      simp [mem_center_iff] at this
    · rw [mem_center_iff, Subalgebra.coe_mul, map_mul] at hxy
      by_contra! H
      rw [mem_center_iff, mem_center_iff, not_lt, not_lt] at H
      have h1 := le_antisymm (valuation_le_one_of_isIntegral hw' x.2) H.1
      have h2 := le_antisymm (valuation_le_one_of_isIntegral hw' y.2) H.2
      rw [h1, h2, mul_one] at hxy
      exact lt_irrefl 1 hxy
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := discRing C) _ ?_
  rw [comap_center]
  exact discIdeal_isMaximal

variable [FiniteDimensional (RatFunc C) F'] [Algebra.IsSeparable (RatFunc C) F']

omit [IsUltrametricDist C] in
/-- The extension of `ν` attached to a factor restricts to `ν`, a disc valuation. -/
lemma isDiscVal_comap_extValuation [hν : Fact (IsDiscVal ν)]
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F') :
    IsDiscVal ((extValuation g).comap (algebraMap (RatFunc C) F')) := by
  have h := extValuation_comap g
  have key : ∀ a : RatFunc C,
      (extValuation g).comap (algebraMap (RatFunc C) F') a = ν a := by
    intro a
    have := congrArg (fun v : Valuation (DiscField ν) ℝ≥0 ↦ v (WithAbs.toAbs _ a)) h
    simp only [Valuation.comap_apply, valuation_withAbs] at this
    rw [Valuation.comap_apply]
    exact this
  exact ⟨fun c ↦ by rw [key, hν.out.map_C], by rw [key]; exact hν.out.X_lt_one⟩

/-- **B1 (the disc count).** For a disc valuation `ν`, `y ∈ F'` integral over the disc chart and
a lift `P` of its characteristic polynomial to the chart, the sum of the local degrees of the
extensions of `ν` (factors of the minimal polynomial over the completion) at which `y` has value
`< 1` is the trailing degree of `P` modulo `(𝔪_C, x)`; in particular it is the same for all
points of the disc `|x| < 1`. -/
theorem sum_natDegree_eq_natTrailingDegree [hν : Fact (IsDiscVal ν)] {y : F'}
    (hy : IsIntegral (discRing C) y) (P : (discRing C)[X])
    (hP : P.map (discRing C).subtype = normPoly (RatFunc C) y) :
    ∑ g ∈ Finset.univ.filter (fun g : Factor (DiscField ν)
        (UniformSpace.Completion (DiscField ν)) F' ↦ ‖toLocal g y‖ < 1), g.1.natDegree =
      (P.map (Ideal.Quotient.mk (discIdeal C))).natTrailingDegree := by
  classical
  haveI : Infinite (RatFunc C) :=
    Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
  haveI : Infinite (DiscField ν) :=
    Infinite.of_injective _ (algebraMap C (DiscField ν)).injective
  set e : RatFunc C ≃+* DiscField ν := (WithAbs.equiv _).symm
  set ι : discRing C →+* DiscField ν := e.toRingHom.comp (discRing C).subtype
  have hPι : P.map ι = normPoly (DiscField ν) y := by
    rw [← Polynomial.map_map, hP]
    exact normPoly_map_ringEquiv e (by ext; rfl) y
  have h𝔭 : ∀ a : discRing C, a ∈ discIdeal C ↔ ‖ι a‖ < 1 := by
    intro a
    rw [mem_discIdeal_iff hν.out a, WithAbs.norm_eq_apply_ofAbs]
    exact NNReal.coe_lt_one.symm
  have hy' : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F',
      ‖toLocal g y‖ ≤ 1 := fun g ↦ by
    have := valuation_le_one_of_isIntegral (isDiscVal_comap_extValuation g) hy
    rw [extValuation_apply] at this
    exact_mod_cast this
  exact TubeCount.sum_natDegree_eq_natTrailingDegree ι _ h𝔭 P hPι hy'

open Classical in
variable (ν) in
/-- The **disc degree** of a point `P'` of `Spec R'` over the residue point, seen from a disc
valuation `ν`: the sum of the local degrees of the extensions of `ν` centred at `P'`. -/
noncomputable def discDegree [Fact (IsDiscVal ν)] (P' : Ideal (DRint C F')) : ℕ :=
  ∑ g ∈ Finset.univ.filter (fun g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F' ↦
      center (isDiscVal_comap_extValuation g) = P'), g.1.natDegree

/-- **B2: the disc degree does not depend on the point of the disc.** For two disc valuations
`ν, ν'` (any types: Gauss points, type-4 points, …) and a maximal ideal `P'` of `R'`,
`discDegree ν P' = discDegree ν' P'`. Proof as for S5: a separating `e ∈ R'` (`e ≡ 1` at `P'`,
`e` in the other centres) and B1 for `e − 1`. -/
theorem discDegree_eq (ν' : Valuation (RatFunc C) ℝ≥0) [Fact (IsDiscVal ν)]
    [Fact (IsDiscVal ν')] (P' : Ideal (DRint C F')) [P'.IsMaximal] :
    discDegree ν P' = discDegree ν' P' := by
  classical
  set T : Finset (Ideal (DRint C F')) :=
    (Finset.univ.image (fun g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F' ↦
        center (isDiscVal_comap_extValuation g)) ∪
      Finset.univ.image (fun g : Factor (DiscField ν') (UniformSpace.Completion (DiscField ν'))
        F' ↦ center (isDiscVal_comap_extValuation g))).erase P'
  obtain ⟨e, he1, heQ⟩ := GaussTube.exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    refine ⟨?_, hne⟩
    rcases Finset.mem_union.1 hQ with hQ | hQ <;> obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hQ
    exacts [center_isMaximal _, center_isMaximal _]
  set y : DRint C F' := e - 1
  obtain ⟨P, hP⟩ := exists_lift_normPoly y.2
  have key : ∀ {w' : Valuation F' ℝ≥0} (hw' : IsDiscVal (w'.comap (algebraMap (RatFunc C) F'))),
      center hw' ∈ insert P' T → (w' (y : F') < 1 ↔ center hw' = P') := by
    intro w' hw' hmem
    constructor
    · intro hlt
      by_contra hne
      have hmemT : center hw' ∈ T := by
        rcases Finset.mem_insert.1 hmem with h | h
        · exact absurd h hne
        · exact h
      have he : w' (e : F') < 1 := (mem_center_iff hw' e).1 (heQ _ hmemT)
      have : w' ((y : F')) = 1 := by
        rw [show (y : F') = -1 + (e : F') by simp [y]; ring,
          Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, map_one]; exact he),
          Valuation.map_neg, map_one]
      exact lt_irrefl 1 (this ▸ hlt)
    · intro h
      rw [← mem_center_iff hw', h]
      exact he1
  have hcount : ∀ (μ : Valuation (RatFunc C) ℝ≥0) [Fact (IsDiscVal μ)],
      (∀ g : Factor (DiscField μ) (UniformSpace.Completion (DiscField μ)) F',
        center (isDiscVal_comap_extValuation g) ∈ insert P' T) →
      discDegree μ P' = (P.map (Ideal.Quotient.mk (discIdeal C))).natTrailingDegree := by
    intro μ _ hall
    rw [← sum_natDegree_eq_natTrailingDegree (ν := μ) y.2 P hP, discDegree]
    refine Finset.sum_congr (Finset.filter_congr fun g _ ↦ ?_) fun _ _ ↦ rfl
    rw [← key _ (hall g), extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
  have hmemT : ∀ Q : Ideal (DRint C F'), Q ∈ (Finset.univ.image (fun g : Factor (DiscField ν)
        (UniformSpace.Completion (DiscField ν)) F' ↦ center (isDiscVal_comap_extValuation g)) ∪
      Finset.univ.image (fun g : Factor (DiscField ν') (UniformSpace.Completion (DiscField ν'))
        F' ↦ center (isDiscVal_comap_extValuation g))) → Q ∈ insert P' T := by
    intro Q hQ
    by_cases hQP : Q = P'
    · exact hQP ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hQP, hQ⟩)
  rw [hcount ν fun g ↦ hmemT _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ g))),
    hcount ν' fun g ↦ hmemT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ g)))]

end DiscCount

end SemistableReduction
