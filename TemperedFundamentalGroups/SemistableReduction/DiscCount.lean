/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TubePoints
import TemperedFundamentalGroups.SemistableReduction.GaussTreeNormal

/-!
# Counting extensions over a residue disc

Blueprint §9.10, layer L2 (B1, B2). Let `t = (x - a) / c` (`c ≠ 0`), `discRing a c = O_C[t]`
the chart of the Gauss point `w_{a,|c|}` (`polyChart`), and `discIdeal a c = (𝔪_C, t)` the
maximal ideal of the residue point `t̄ = 0`, i.e. of the open disc `U = {|x - a| < |c|}`. A *disc
valuation* (`IsDiscVal a c ν`, bundled `DiscVal a c`) is a real valuation `ν` of `C(x)`
extending the norm of `C` with `ν(t) < 1`: a point of `U` of any type 2–4 that is a valuation
(Gauss points inside `U`, type-4 points of `U`).

* `valuation_le_one`: disc valuations are `≤ 1` on the chart;
* **`mem_discIdeal_iff`**: for every disc valuation `ν`, `f ∈ discIdeal a c ↔ ν f < 1`: all points
  of `U` have the same centre on the chart (write `f = Q(0) + t · (Q div X)(t)`);
* `isIntegrallyClosed_discRing`, `exists_lift_normPoly`: characteristic polynomials of integral
  elements lift to the chart; `discIdeal_isMaximal`;
* **`sum_natDegree_eq_natTrailingDegree` (B1, the disc count)**: for `y ∈ F'` integral over the
  chart and a lift `P` of its characteristic polynomial, the sum of the local degrees
  `[\hat F'_{ν'} : \hat C(x)_ν]` (degrees of the factors of the minimal polynomial over the
  completion, `LocalGlobal`) over the extensions `ν'` of `ν` with `ν'(y) < 1` is
  `natTrailingDegree (P mod (𝔪_C, t))`, independent of `ν` (S5's tube count for the disc chart);
* `DRint`, `center`: the integral closure `R'` of the chart in `F'` and the centre
  `{y : w'(y) < 1}` of a valuation over a disc valuation, a maximal ideal over `discIdeal`
  (`center_isMaximal`, `comap_center`);
* **`discDegree_eq` (B2)**: the *disc degree* of a maximal ideal `P'` of `R'` (the sum of the
  local degrees of the extensions of `ν` centred at `P'`) is the same for all disc valuations
  `ν`; at a type-4 point of `U` it is a sum of defects, at a Gauss point a sum of `e · f`;
* **`discDegree_pos` (B4a)**: every maximal ideal of `R'` over `(𝔪_C, t)` is the centre of an
  extension of *every* disc valuation (positive disc degree; Cayley–Hamilton for an element of
  `P'` outside the other centres);
* **`existsUnique_of_discDegree_eq_one` (B5)**: at a point of disc degree `1`, every disc valuation
  has exactly one extension centred there, and its local factor has degree `1` (the completions
  agree).
-/

open Polynomial NNReal IntermediateField

namespace SemistableReduction

namespace DiscCount

open TubeCount LocalGlobal GaussTube DenseCompletion

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

/-! ### The disc chart -/

variable (a c : C)

/-- The chart `O_C[t]`, `t = (x - a) / c`, of the Gauss point `w_{a,|c|}`. -/
noncomputable abbrev discRing : Subring (RatFunc C) :=
  polyChart (NormedField.valuation (K := C)) (gaussCoord a c)

/-- The coefficients of a polynomial with Gauss norm `≤ 1` have norm `≤ 1`. -/
lemma nnnorm_coeff_le_one {Q : C[X]} (hQ : Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1)
    (i : ℕ) : ‖Q.coeff i‖₊ ≤ 1 :=
  coeff_le_one_of_sup_le_one hQ i

/-- A real valuation of `C(x)` extending the norm of `C` with `ν((x - a) / c) < 1`: a point of
the open disc `|x - a| < |c|`. -/
structure IsDiscVal (ν : Valuation (RatFunc C) ℝ≥0) : Prop where
  map_C : ∀ c : C, ν (algebraMap C (RatFunc C) c) = ‖c‖₊
  X_lt_one : ν (gaussCoord a c) < 1

variable {a c} {ν : Valuation (RatFunc C) ℝ≥0}

omit [IsUltrametricDist C] in
/-- A polynomial in `x` with integral coefficients has value `≤ 1` at a disc valuation. -/
lemma valuation_aeval_le_one (hν : IsDiscVal a c ν) {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖₊ ≤ 1) :
    ν (aeval (gaussCoord a c) Q) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, map_pow, hν.map_C]
  exact mul_le_one' (hQ i) (pow_le_one₀ zero_le hν.X_lt_one.le)

/-- Disc valuations are `≤ 1` on the disc chart. -/
lemma valuation_le_one (hν : IsDiscVal a c ν) {f : RatFunc C} (hf : f ∈ discRing a c) :
    ν f ≤ 1 := by
  obtain ⟨Q, hQ, rfl⟩ := mem_polyChart_iff.1 hf
  exact valuation_aeval_le_one hν (nnnorm_coeff_le_one hQ)

omit [IsUltrametricDist C] in
/-- **The value at a disc valuation is `< 1` iff the constant coefficient is in `𝔪_C`.** -/
lemma valuation_aeval_lt_one_iff (hν : IsDiscVal a c ν) {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖₊ ≤ 1) :
    ν (aeval (gaussCoord a c) Q) < 1 ↔ ‖Q.coeff 0‖₊ < 1 := by
  have hdecomp : aeval (gaussCoord a c) Q =
      algebraMap C (RatFunc C) (Q.coeff 0) + gaussCoord a c * aeval (gaussCoord a c) Q.divX := by
    conv_lhs => rw [← X_mul_divX_add Q]
    rw [map_add, map_mul, aeval_X, aeval_C, add_comm]
  have hrest : ν (gaussCoord a c * aeval (gaussCoord a c) Q.divX) < 1 := by
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

variable (a c) in
/-- The ideal `(𝔪_C, t)` of the disc chart: the centre of every point of the disc
`|x - a| < |c|`. -/
def discIdeal : Ideal (discRing a c) where
  carrier := {f | ∃ Q : C[X], (∀ i, ‖Q.coeff i‖₊ ≤ 1) ∧ aeval (gaussCoord a c) Q = (f : RatFunc C) ∧
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
theorem mem_discIdeal_iff (hν : IsDiscVal a c ν) (f : discRing a c) :
    f ∈ discIdeal a c ↔ ν f < 1 := by
  constructor
  · rintro ⟨Q, hQ, hQa, hQ0⟩
    rw [← hQa]
    exact (valuation_aeval_lt_one_iff hν hQ).2 hQ0
  · intro h
    obtain ⟨Q, hQ, hQa⟩ := mem_polyChart_iff.1 f.2
    have hQ' := nnnorm_coeff_le_one hQ
    refine ⟨Q, hQ', hQa, ?_⟩
    rw [← hQa] at h
    exact (valuation_aeval_lt_one_iff hν hQ').1 h

/-! ### The chart is integrally closed -/

/-- `(x - a) / c` is a Gauss coordinate of `w_{a,|c|}`. -/
lemma isGaussCoord_disc (hc : c ≠ 0) :
    IsGaussCoord (NormedField.valuation (K := C))
      (gaussRat (NormedField.valuation (K := C)) a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc)))
      (gaussCoord a c) :=
  isGaussCoord_gaussCoord (by rw [NormedField.valuation_apply, Units.val_mk0])

theorem isFractionRing_discRing (hc : c ≠ 0) : IsFractionRing (discRing a c) (RatFunc C) :=
  (isGaussCoord_disc (a := a) hc).isFractionRing_polyChart

theorem isIntegrallyClosed_discRing (hc : c ≠ 0) : IsIntegrallyClosed (discRing a c) := by
  haveI := isFractionRing_discRing (a := a) hc
  let e : (NormedField.valuation (K := C)).valuationSubring[X] ≃+* discRing a c :=
    (AlgEquiv.ofInjective _ (ZariskiModel.aeval_injective'
      (isGaussCoord_disc (a := a) hc))).toRingEquiv.trans
      (RingEquiv.subringCongr (ZariskiModel.range_aeval _))
  exact IsIntegrallyClosed.of_equiv e

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

/-- The characteristic polynomial of an element integral over the disc chart has coefficients in
the disc chart. -/
theorem exists_lift_normPoly (hc : c ≠ 0) {y : F'} (hy : IsIntegral (discRing a c) y) :
    ∃ P : (discRing a c)[X], P.map (discRing a c).subtype = normPoly (RatFunc C) y := by
  haveI := isIntegrallyClosed_discRing (a := a) hc
  haveI := isFractionRing_discRing (a := a) hc
  refine ⟨minpoly (discRing a c) y ^ Module.finrank (RatFunc C)⟮y⟯ F', ?_⟩
  rw [Polynomial.map_pow, normPoly, minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc C) hy]
  rfl

/-- An element integral over the disc chart has value `≤ 1` at every valuation of `F'` whose
restriction to `C(x)` is a disc valuation. -/
theorem valuation_le_one_of_isIntegral {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal a c (w'.comap (algebraMap (RatFunc C) F'))) {y : F'}
    (hy : IsIntegral (discRing a c) y) : w' y ≤ 1 := by
  let φ : discRing a c →+* w'.integer :=
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

variable (a c) in
/-- A disc valuation, bundled. -/
structure DiscVal where
  /-- The valuation. -/
  val : Valuation (RatFunc C) ℝ≥0
  isDiscVal : IsDiscVal a c val

/-- `C(x)` with the absolute value of a disc valuation `ν`. -/
abbrev DiscField (ν : DiscVal a c) : Type u := WithAbs ν.val.toAbsoluteValue

omit [IsUltrametricDist C] in
lemma norm_algebraMap_discField (ν : DiscVal a c) (b : C) :
    ‖algebraMap C (DiscField ν) b‖ = ‖b‖ := by
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs,
    Valuation.toAbsoluteValue_apply, ν.isDiscVal.map_C, coe_nnnorm]

noncomputable instance (ν : DiscVal a c) : NormedAlgebra C (DiscField ν) where
  norm_smul_le b x := le_of_eq (by rw [Algebra.smul_def, norm_mul, norm_algebraMap_discField])

noncomputable instance (ν : DiscVal a c) : NontriviallyNormedField (DiscField ν) where
  __ : NormedField (DiscField ν) := inferInstance
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
    ⟨algebraMap C _ x, by rwa [norm_algebraMap_discField]⟩

/-! ### B2: points over the residue point and their disc degrees -/

lemma algebraMap_mem_discRing {b : C} (hb : ‖b‖₊ ≤ 1) :
    algebraMap C (RatFunc C) b ∈ discRing a c :=
  mem_polyChart_iff.2 ⟨Polynomial.C b, by rw [Gauss.sup_C, NormedField.valuation_apply]; exact hb,
    aeval_C _ _⟩

/-- **The disc ideal is maximal**: modulo `(𝔪_C, x)`, an element `Q(x)` with `|Q(0)| = 1` is
congruent to the unit `Q(0)`. -/
theorem discIdeal_isMaximal (hc : c ≠ 0) : (discIdeal a c).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h ↦ ?_, fun J x hJ hx hxJ ↦ ?_⟩
  · -- `Q((x - a) / c) = 1` forces `Q = 1` (a Gauss coordinate is transcendental)
    obtain ⟨Q, -, hQa, hQ0⟩ := h
    have h0 : aeval (gaussCoord a c) (Q - 1) = 0 := by
      rw [map_sub, hQa, map_one]
      exact sub_self _
    rw [(isGaussCoord_disc (a := a) hc).aeval_eq_zero_iff, sub_eq_zero] at h0
    rw [h0, coeff_one_zero, nnnorm_one] at hQ0
    exact lt_irrefl 1 hQ0
  obtain ⟨Q, hQ, hQa⟩ := mem_polyChart_iff.1 x.2
  have hQ' := nnnorm_coeff_le_one hQ
  have hQ0 : ‖Q.coeff 0‖₊ = 1 :=
    le_antisymm (hQ' 0) (not_lt.1 fun h ↦ hx ⟨Q, hQ', hQa, h⟩)
  have hc0 : Q.coeff 0 ≠ 0 := by
    rintro h
    rw [h, nnnorm_zero] at hQ0
    exact zero_ne_one hQ0
  set u : discRing a c := ⟨_, algebraMap_mem_discRing hQ0.le⟩
  set d : discRing a c := ⟨algebraMap C (RatFunc C) (Q.coeff 0)⁻¹,
    algebraMap_mem_discRing (by rw [nnnorm_inv, hQ0, inv_one])⟩
  have hcd : d * u = 1 := Subtype.ext (by
    change algebraMap C (RatFunc C) _ * algebraMap C (RatFunc C) _ = 1
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one])
  have hxc : x - u ∈ discIdeal a c := by
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
  have hcJ : u ∈ J := by
    have := J.sub_mem hxJ (hJ hxc)
    rwa [sub_sub_cancel] at this
  rw [← hcd]
  exact J.mul_mem_left d hcJ

variable (a c F') in
/-- The integral closure `R'` of the disc chart in `F'`. -/
noncomputable abbrev DRint : Subalgebra (discRing a c) F' := integralClosure (discRing a c) F'

/-- The centre `{y ∈ R' : w'(y) < 1}` of a valuation of `F'` over a disc valuation. -/
noncomputable def center {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal a c (w'.comap (algebraMap (RatFunc C) F'))) : Ideal (DRint a c F') where
  carrier := {y | w' (y : F') < 1}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at hf hg ⊢
    exact (Valuation.map_add _ _ _).trans_lt (max_lt hf hg)
  zero_mem' := by simp
  smul_mem' r y hy := by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Subalgebra.coe_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (valuation_le_one_of_isIntegral hw' r.2)
      zero_le hy

lemma mem_center_iff {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal a c (w'.comap (algebraMap (RatFunc C) F'))) (y : DRint a c F') :
    y ∈ center hw' ↔ w' (y : F') < 1 := Iff.rfl

lemma comap_center {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal a c (w'.comap (algebraMap (RatFunc C) F'))) :
    (center hw').comap (algebraMap (discRing a c) (DRint a c F')) = discIdeal a c := by
  ext f
  rw [Ideal.mem_comap, mem_center_iff, mem_discIdeal_iff hw' f]
  rfl

theorem center_isMaximal (hc : c ≠ 0) {w' : Valuation F' ℝ≥0}
    (hw' : IsDiscVal a c (w'.comap (algebraMap (RatFunc C) F'))) : (center hw').IsMaximal := by
  have hprime : (center hw').IsPrime := by
    refine ⟨fun h ↦ ?_, fun {x y} hxy ↦ ?_⟩
    · have : (1 : DRint a c F') ∈ center hw' := h ▸ Submodule.mem_top
      simp [mem_center_iff] at this
    · rw [mem_center_iff, Subalgebra.coe_mul, map_mul] at hxy
      by_contra! H
      rw [mem_center_iff, mem_center_iff, not_lt, not_lt] at H
      have h1 := le_antisymm (valuation_le_one_of_isIntegral hw' x.2) H.1
      have h2 := le_antisymm (valuation_le_one_of_isIntegral hw' y.2) H.2
      rw [h1, h2, mul_one] at hxy
      exact lt_irrefl 1 hxy
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := discRing a c) _ ?_
  rw [comap_center]
  exact discIdeal_isMaximal hc

variable [FiniteDimensional (RatFunc C) F'] [Algebra.IsSeparable (RatFunc C) F']

omit [IsUltrametricDist C] in
/-- The extension of `ν` attached to a factor restricts to `ν`, a disc valuation. -/
lemma isDiscVal_comap_extValuation {ν : DiscVal a c}
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F') :
    IsDiscVal a c ((extValuation g).comap (algebraMap (RatFunc C) F')) := by
  have h := extValuation_comap g
  have key : ∀ a : RatFunc C,
      (extValuation g).comap (algebraMap (RatFunc C) F') a = ν.val a := by
    intro a
    have := congrArg (fun v : Valuation (DiscField ν) ℝ≥0 ↦ v (WithAbs.toAbs _ a)) h
    simp only [Valuation.comap_apply, valuation_withAbs] at this
    rw [Valuation.comap_apply]
    exact this
  exact ⟨fun b ↦ by rw [key, ν.isDiscVal.map_C], by rw [key]; exact ν.isDiscVal.X_lt_one⟩

/-- **B1 (the disc count).** For a disc valuation `ν`, `y ∈ F'` integral over the disc chart and
a lift `P` of its characteristic polynomial to the chart, the sum of the local degrees of the
extensions of `ν` (factors of the minimal polynomial over the completion) at which `y` has value
`< 1` is the trailing degree of `P` modulo `(𝔪_C, x)`; in particular it is the same for all
points of the disc `|x| < 1`. -/
theorem sum_natDegree_eq_natTrailingDegree (ν : DiscVal a c) {y : F'}
    (hy : IsIntegral (discRing a c) y) (P : (discRing a c)[X])
    (hP : P.map (discRing a c).subtype = normPoly (RatFunc C) y) :
    ∑ g ∈ Finset.univ.filter (fun g : Factor (DiscField ν)
        (UniformSpace.Completion (DiscField ν)) F' ↦ ‖toLocal g y‖ < 1), g.1.natDegree =
      (P.map (Ideal.Quotient.mk (discIdeal a c))).natTrailingDegree := by
  classical
  haveI : Infinite (RatFunc C) :=
    Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
  haveI : Infinite (DiscField ν) :=
    Infinite.of_injective _ (algebraMap C (DiscField ν)).injective
  set e : RatFunc C ≃+* DiscField ν := (WithAbs.equiv _).symm
  set ι : discRing a c →+* DiscField ν := e.toRingHom.comp (discRing a c).subtype
  have hPι : P.map ι = normPoly (DiscField ν) y := by
    rw [← Polynomial.map_map, hP]
    exact normPoly_map_ringEquiv e (by ext; rfl) y
  have h𝔭 : ∀ f : discRing a c, f ∈ discIdeal a c ↔ ‖ι f‖ < 1 := by
    intro f
    rw [mem_discIdeal_iff ν.isDiscVal f, WithAbs.norm_eq_apply_ofAbs]
    exact NNReal.coe_lt_one.symm
  have hy' : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F',
      ‖toLocal g y‖ ≤ 1 := fun g ↦ by
    have := valuation_le_one_of_isIntegral (isDiscVal_comap_extValuation g) hy
    rw [extValuation_apply] at this
    exact_mod_cast this
  exact TubeCount.sum_natDegree_eq_natTrailingDegree ι _ h𝔭 P hPι hy'

open Classical in
/-- The **disc degree** of a point `P'` of `Spec R'` over the residue point, seen from a disc
valuation `ν`: the sum of the local degrees of the extensions of `ν` centred at `P'`. -/
noncomputable def discDegree (ν : DiscVal a c) (P' : Ideal (DRint a c F')) : ℕ :=
  ∑ g ∈ Finset.univ.filter (fun g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F' ↦
      center (isDiscVal_comap_extValuation g) = P'), g.1.natDegree

/-- **B2: the disc degree does not depend on the point of the disc.** For two disc valuations
`ν, ν'` (any types: Gauss points, type-4 points, …) and a maximal ideal `P'` of `R'`,
`discDegree ν P' = discDegree ν' P'`. Proof as for S5: a separating `e ∈ R'` (`e ≡ 1` at `P'`,
`e` in the other centres) and B1 for `e − 1`. -/
theorem discDegree_eq (hc : c ≠ 0) (ν ν' : DiscVal a c) (P' : Ideal (DRint a c F'))
    [P'.IsMaximal] :
    discDegree ν P' = discDegree ν' P' := by
  classical
  set T : Finset (Ideal (DRint a c F')) :=
    (Finset.univ.image (fun g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F' ↦
        center (isDiscVal_comap_extValuation g)) ∪
      Finset.univ.image (fun g : Factor (DiscField ν') (UniformSpace.Completion (DiscField ν'))
        F' ↦ center (isDiscVal_comap_extValuation g))).erase P'
  obtain ⟨e, he1, heQ⟩ := GaussTube.exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    refine ⟨?_, hne⟩
    rcases Finset.mem_union.1 hQ with hQ | hQ <;> obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hQ
    exacts [center_isMaximal hc _, center_isMaximal hc _]
  set y : DRint a c F' := e - 1
  obtain ⟨P, hP⟩ := exists_lift_normPoly hc y.2
  have key : ∀ {w' : Valuation F' ℝ≥0}
      (hw' : IsDiscVal a c (w'.comap (algebraMap (RatFunc C) F'))),
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
  have hcount : ∀ μ : DiscVal a c,
      (∀ g : Factor (DiscField μ) (UniformSpace.Completion (DiscField μ)) F',
        center (isDiscVal_comap_extValuation g) ∈ insert P' T) →
      discDegree μ P' = (P.map (Ideal.Quotient.mk (discIdeal a c))).natTrailingDegree := by
    intro μ hall
    rw [← sum_natDegree_eq_natTrailingDegree μ y.2 P hP, discDegree]
    refine Finset.sum_congr (Finset.filter_congr fun g _ ↦ ?_) fun _ _ ↦ rfl
    rw [← key _ (hall g), extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
  have hmemT : ∀ Q : Ideal (DRint a c F'), Q ∈ (Finset.univ.image (fun g : Factor (DiscField ν)
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

/-- **B4a: every point over the residue point is reached from every point of the disc.** For a
maximal ideal `P'` of `R'` over `(𝔪_C, t)` and any disc valuation `ν`, some extension of `ν` is
centred at `P'`: `0 < discDegree ν P'`. Proof: `f ∈ P'` outside the other centres; by B1 the
disc degree of `P'` is the trailing degree of the reduced characteristic polynomial of `f`,
which is positive since its constant term `± N(f) ∈ f R' ∩ O_C[t] ⊆ P' ∩ O_C[t]` lies in
`(𝔪_C, t)` (Cayley–Hamilton). -/
theorem discDegree_pos (hc : c ≠ 0) (ν : DiscVal a c) (P' : Ideal (DRint a c F')) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing a c) (DRint a c F')) = discIdeal a c) :
    0 < discDegree ν P' := by
  classical
  set T : Finset (Ideal (DRint a c F')) :=
    (Finset.univ.image (fun g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F' ↦
        center (isDiscVal_comap_extValuation g))).erase P'
  obtain ⟨e, he1, heQ⟩ := GaussTube.exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hQ
    exact ⟨center_isMaximal hc _, hne⟩
  set f : DRint a c F' := 1 - e
  have hfP : f ∈ P' := by
    have := P'.neg_mem he1
    rwa [neg_sub] at this
  obtain ⟨P, hP⟩ := exists_lift_normPoly hc f.2
  have hfilter : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F',
      ‖toLocal g (f : F')‖ < 1 ↔ center (isDiscVal_comap_extValuation g) = P' := by
    intro g
    have hval : ‖toLocal g (f : F')‖ < 1 ↔ extValuation g (f : F') < 1 := by
      rw [extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
    rw [hval]
    constructor
    · intro hlt
      by_contra hne
      have hmem : center (isDiscVal_comap_extValuation g) ∈ T :=
        Finset.mem_erase.2 ⟨hne, Finset.mem_image_of_mem _ (Finset.mem_univ g)⟩
      have he : extValuation g (e : F') < 1 :=
        (mem_center_iff (isDiscVal_comap_extValuation g) e).1 (heQ _ hmem)
      have : extValuation g (f : F') = 1 := by
        rw [show (f : F') = 1 + -(e : F') by simp [f]; ring,
          Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, map_one]; exact he),
          map_one]
      exact lt_irrefl 1 (this ▸ hlt)
    · intro h
      rw [← mem_center_iff (isDiscVal_comap_extValuation g), h]
      exact hfP
  have hcount := sum_natDegree_eq_natTrailingDegree ν f.2 P hP
  rw [show discDegree ν P' = _ from Finset.sum_congr (Finset.filter_congr fun g _ ↦
    (hfilter g).symm) fun _ _ ↦ rfl, hcount]
  -- the constant term of `P` lies in the disc ideal
  have hPmonic : P.Monic := by
    have hm := monic_normPoly (F := RatFunc C) (f : F')
    rw [← hP] at hm
    exact monic_of_injective (discRing a c).subtype_injective hm
  have h0 : P.coeff 0 ∈ discIdeal a c := by
    rw [← hP', Ideal.mem_comap]
    have hroot : aeval f P = 0 := by
      apply Subtype.val_injective
      change (DRint a c F').val (aeval f P) = 0
      rw [← aeval_algHom_apply, aeval_def, show algebraMap (discRing a c) F' =
        (algebraMap (RatFunc C) F').comp (discRing a c).subtype from rfl, ← eval₂_map, hP,
        ← aeval_def, normPoly, map_pow]
      change aeval (f : F') (minpoly (RatFunc C) (f : F')) ^ _ = 0
      rw [minpoly.aeval, zero_pow Module.finrank_pos.ne']
    have hdecomp := congrArg (aeval f) (X_mul_divX_add P)
    rw [map_add, map_mul, aeval_X, aeval_C, hroot] at hdecomp
    have : algebraMap (discRing a c) (DRint a c F') (P.coeff 0) = -(f * aeval f P.divX) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hdecomp
    rw [this]
    exact P'.neg_mem (P'.mul_mem_right _ hfP)
  have hne : P.map (Ideal.Quotient.mk (discIdeal a c)) ≠ 0 :=
    (hPmonic.map _).ne_zero_of_ne (by
      haveI := discIdeal_isMaximal (a := a) hc
      exact zero_ne_one)
  refine Nat.pos_of_ne_zero fun h ↦ ?_
  rw [natTrailingDegree_eq_zero] at h
  rcases h with h | h
  · exact hne h
  · exact h (by rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact h0)


/-- **B5 (degree-one disc points).** If a point `P'` has disc degree `1` at one disc valuation,
then at every disc valuation `ν` exactly one extension of `ν` is centred at `P'`, and its factor
has degree `1`: the completion of `F'` at it is the completion of `C(x)` at `ν`. -/
theorem existsUnique_of_discDegree_eq_one (hc : c ≠ 0) (ν₀ ν : DiscVal a c)
    (P' : Ideal (DRint a c F')) [P'.IsMaximal] (h1 : discDegree ν₀ P' = 1) :
    ∃! g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F',
      center (isDiscVal_comap_extValuation g) = P' ∧ g.1.natDegree = 1 := by
  classical
  rw [discDegree_eq hc ν₀ ν P', discDegree] at h1
  set S := Finset.univ.filter (fun g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F' ↦ center (isDiscVal_comap_extValuation g) = P')
  have hpos : ∀ g ∈ S, 1 ≤ g.1.natDegree := fun g _ ↦
    Nat.one_le_iff_ne_zero.2 (irreducible_of_mem_factors g.2).natDegree_pos.ne'
  -- a sum of positive integers equal to `1` has exactly one term, equal to `1`
  have hcard : S.card ≤ 1 := by
    have := Finset.card_nsmul_le_sum S (fun g ↦ g.1.natDegree) 1 hpos
    rw [smul_eq_mul, mul_one, h1] at this
    exact this
  obtain ⟨g, hg⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h
    rw [h, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have hS : S = {g} := Finset.eq_singleton_iff_unique_mem.2
    ⟨hg, fun g' hg' ↦ Finset.card_le_one.1 hcard _ hg' _ hg⟩
  have hdeg : g.1.natDegree = 1 := by
    rw [hS, Finset.sum_singleton] at h1
    exact h1
  refine ⟨g, ⟨(Finset.mem_filter.1 hg).2, hdeg⟩, fun g' hg' ↦ ?_⟩
  have : g' ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hg'.1⟩
  rw [hS] at this
  exact Finset.mem_singleton.1 this

end DiscCount

end SemistableReduction
