/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourInterfaces
import TemperedFundamentalGroups.SemistableReduction.VertexMatch

/-!
# Disc degrees and branch orders; sheets are smooth

Blueprint §9.12, leaf T4, part (G). For the normalized vertex chart `R' = DRint 0 1 G` (the
integral closure of `O_C[x]` in `G`) and a maximal ideal `P'` over the residue point `(𝔪_C, x)`:

* `placeHomD_polyD`, `mem_discIdeal_iff_placeHomD`: the reduction of the chart at a branch is
  the value at `x̄ = 0`;
* `map_lift_eq_prodD`: the reduction at a branch of a lift of the characteristic polynomial of
  `y ∈ R'` is `∏_v ∏_{Q : x̄(Q) = 0} (X - ȳ_v(Q)) ^ ord_Q x̄` (the norm specialization of S6, for
  the disc chart);
* **`discDegree_eq_vertexDegreeD`**, **`discDegreeSum`** (B1 for the disc chart): the disc
  degree of `P'` is the sum of `ord_Q x̄` over the branches `(v, Q)` through `P'`;
* **`sheetSmooth`**: a point of disc degree one is smooth (`exists_eq_of_uniformizer` with
  `t = x`).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open FundamentalInequality GaussStability GaussFibre GaussTube DiscCount SmoothVertex PlaceNorm
  TubeCount LocalGlobal

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

local notation "κ₁" => ResidueField (Valuation.valuationSubring (gauss1 C))

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

/-! ### The reduction of the chart at a branch -/

section Reduction

lemma placeHomD_xD (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : placeHomD v hQ xD = 0 :=
  Q.res_eq_zero_of_lt_one (valuation_x_lt_one hQ)

lemma placeHomD_constD (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (b : HenselComplete.integers C) :
    placeHomD v hQ (constD b) = residue _ b := by
  change Q.res (redD v (constD b)) = _
  rw [redD_constD, Q.res_algebraMap]

lemma placeHomD_apply (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (y : DRint (0 : C) 1 F') :
    placeHomD v hQ y = Q.res (red C (y : F') v) := rfl

/-- The reduction at a branch of a polynomial in `x` is the residue of its constant term. -/
lemma placeHomD_polyD (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (P : C[X]) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    placeHomD v hQ (polyD P hP) =
      residue _ ⟨P.coeff 0, (HenselComplete.mem_integers_iff _).2 (hP 0)⟩ := by
  have hP' : ∀ i, ‖P.divX.coeff i‖ ≤ 1 := fun i ↦ by rw [coeff_divX]; exact hP _
  have heq : (polyD P hP : DRint (0 : C) 1 F') =
      constD ⟨P.coeff 0, (HenselComplete.mem_integers_iff _).2 (hP 0)⟩ +
        xD * polyD P.divX hP' := by
    apply Subtype.ext
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, coe_polyD]
    change aeval (xF C F') P = algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) (P.coeff 0)) +
      xF C F' * aeval (xF C F') P.divX
    conv_lhs => rw [← X_mul_divX_add P]
    rw [map_add, map_mul, aeval_X, aeval_C, ← IsScalarTower.algebraMap_apply, add_comm]
  rw [heq, map_add, map_mul, placeHomD_constD, placeHomD_xD, zero_mul, add_zero]

/-- An element of the chart lies in the disc ideal iff its reduction at a branch vanishes. -/
lemma mem_discIdeal_iff_placeHomD (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (a : discRing (0 : C) 1) :
    a ∈ discIdeal (0 : C) 1 ↔
      placeHomD v hQ (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') a) = 0 := by
  have hrep : ∀ (P : C[X]) (hP : ∀ i, ‖P.coeff i‖ ≤ 1),
      aeval (gaussCoord (0 : C) 1) P = (a : RatFunc C) →
      algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') a = polyD P hP := by
    intro P hP hPa
    apply Subtype.ext
    rw [coe_polyD, aeval_xF, ← RatFunc.aeval_X_left_eq_algebraMap, ← gaussCoord_zero_one, hPa]
    rfl
  constructor
  · rintro ⟨P, hP, hPa, hP0⟩
    have hP' : ∀ i, ‖P.coeff i‖ ≤ 1 := fun i ↦ by exact_mod_cast hP i
    rw [hrep P hP' hPa, placeHomD_polyD, residue_eq_zero_iff,
      HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
    exact_mod_cast hP0
  · intro h
    obtain ⟨P, hP, hPa⟩ := mem_polyChart_iff.1 a.2
    have hP' : ∀ i, ‖P.coeff i‖₊ ≤ 1 := nnnorm_coeff_le_one hP
    have hP'' : ∀ i, ‖P.coeff i‖ ≤ 1 := fun i ↦ by exact_mod_cast hP' i
    rw [hrep P hP'' hPa, placeHomD_polyD, residue_eq_zero_iff,
      HenselComplete.mem_maximalIdeal_iff_norm_lt_one] at h
    exact ⟨P, hP', hPa, by exact_mod_cast h⟩

end Reduction

/-! ### The norm specialization at a branch -/

section Identity

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) [Fintype (Ext C F')]
include hp hp1

/-- **The reduction of the characteristic polynomial at a branch of the vertex chart.** For
`y ∈ R'` with characteristic polynomial lifted to `P` over the disc chart, the image of `P` under
the reduction at a branch `Q₀` (`x̄ = 0` on `κ(v₀)`) is
`∏_v ∏_{Q : x̄(Q) = 0} (X - ȳ_v(Q)) ^ ord_Q x̄`. -/
theorem map_lift_eq_prodD (y : DRint (0 : C) 1 F') (P : (discRing (0 : C) 1)[X])
    (hP : P.map (discRing (0 : C) 1).subtype = normPoly (RatFunc C) (y : F')) (v₀ : Ext C F')
    {Q₀ : CurvePlace 𝓀 (ResidueField v₀.1.valuationSubring)}
    (hQ₀ : Q₀ ∈ zeros 𝓀 (red C (xF C F') v₀)) :
    P.map ((placeHomD v₀ hQ₀).comp (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F'))) =
      ∏ v : Ext C F', ∏ Q ∈ zeros 𝓀 (red C (xF C F') v),
        (X - Polynomial.C (Q.res (red C (y : F') v))) ^ ord (red C (xF C F') v) Q := by
  classical
  set n := Module.finrank (RatFunc C) F'
  have he : ∀ v : Ext C F', ramificationIdx (RatFunc C) v.1 = 1 := ramificationIdx_eq_one
  have hsum := sum_inertiaDeg_eq hp hp1 (F := F')
  set ψ := (placeHomD v₀ hQ₀).comp (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F'))
  refine eq_of_infinite_eval_eq _ _ (Set.infinite_univ.mono fun t _ ↦ ?_)
  obtain ⟨κ, rfl⟩ := residue_surjective t
  have hκ1 : ‖(κ : C)‖ ≤ 1 := (HenselComplete.mem_integers_iff _).1 κ.2
  set t₀ : discRing (0 : C) 1 := ⟨algebraMap C (RatFunc C) κ, algebraMap_mem_discRing' κ⟩
  have hψt : ψ t₀ = residue _ κ := placeHomD_constD v₀ hQ₀ κ
  simp only [Set.mem_setOf_eq]
  rw [← hψt, eval_map, eval₂_at_apply, hψt]
  -- the element `z = y - κ` and its norm
  set z : F' := (y : F') - algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) κ)
  have hκv (v : Ext C F') : v.1 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) κ)) ≤ 1 := by
    rw [← IsScalarTower.algebraMap_apply, valuation_algebraMap_C']
    exact_mod_cast hκ1
  have hzv (v : Ext C F') : v.1 z ≤ 1 :=
    (Valuation.map_sub _ _ _).trans (max_le (valuation_le_one_D v y) (hκv v))
  have hz : gnorm C z ≤ 1 := gnorm_le_iff.2 hzv
  obtain ⟨hN1, hres⟩ := residue_norm_eq_prod he hsum hz
  have hPe : ((P.eval t₀ : discRing (0 : C) 1) : RatFunc C) =
      (-1) ^ n * Algebra.norm (RatFunc C) z := by
    have h1 : ((P.eval t₀ : discRing (0 : C) 1) : RatFunc C) =
        (normPoly (RatFunc C) (y : F')).eval (t₀ : RatFunc C) := by
      rw [← hP, eval_map]
      exact (eval₂_at_apply (discRing (0 : C) 1).subtype t₀).symm
    have h2 := norm_sub_algebraMap (F := RatFunc C) (y : F') (t₀ : RatFunc C)
    rw [h1, h2, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  set M : discRing (0 : C) 1 := (-1) ^ n * P.eval t₀
  have hM : (M : RatFunc C) = Algebra.norm (RatFunc C) z := by
    simp only [M, Subring.coe_mul, Subring.coe_pow, Subring.coe_neg, Subring.coe_one, hPe]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have hPM : P.eval t₀ = (-1) ^ n * M := by
    simp only [M]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rw [hPM, map_mul, map_pow, _root_.map_neg, map_one]
  -- the reduction of the norm at the vertex
  have hψM : ψ M = Q₀.res (algebraMap κ₁ (ResidueField v₀.1.valuationSubring)
      (∏ v : Ext C F', Algebra.norm κ₁ (red C z v))) := by
    change Q₀.res (red C (algebraMap (RatFunc C) F' (M : RatFunc C)) v₀) = _
    rw [← hres, ← red_algebraMap_rat v₀ hN1, hM]
  -- the zeros on each residue curve and the reductions of `z`
  have hzred (v : Ext C F') : red C z v = red C (y : F') v -
      algebraMap 𝓀 (ResidueField v.1.valuationSubring) (residue _ κ) := by
    rw [red_sub (valuation_le_one_D v y) (hκv v), ← IsScalarTower.algebraMap_apply,
      red_algebraMap_C (κ : C) (by exact_mod_cast hκ1)]
  have hyV (v : Ext C F') {Q' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
      (hQ' : Q' ∈ zeros 𝓀 (red C (xF C F') v)) : red C (y : F') v ∈ Q'.V :=
    redD_mem_V v y (xbar_mem_V v hQ')
  have hzQ (v : Ext C F') : ∀ Q' ∈ zeros 𝓀 (red C (xF C F') v), red C z v ∈ Q'.V :=
    fun Q' hQ' ↦ by
      rw [hzred]
      exact sub_mem (hyV v hQ') (Q'.algebraMap_mem _)
  have hfac (v : Ext C F') :
      algebraMap κ₁ (ResidueField v₀.1.valuationSubring) (Algebra.norm κ₁ (red C z v)) ∈ Q₀.V ∧
      Q₀.res (algebraMap κ₁ (ResidueField v₀.1.valuationSubring) (Algebra.norm κ₁ (red C z v))) =
        ∏ Q' ∈ zeros 𝓀 (red C (xF C F') v),
          (Q'.res (red C (y : F') v) - residue _ κ) ^ ord (red C (xF C F') v) Q' := by
    obtain ⟨Qv, hQv⟩ := exists_mem_zeros v
    obtain ⟨hmem, hval⟩ := res_norm_residue v hQv (hzQ v)
    obtain ⟨hmem0, hval0⟩ := res_algebraMap_eq _ v v₀ hQv hQ₀ hmem
    refine ⟨hmem0, ?_⟩
    rw [hval0, hval]
    refine Finset.prod_congr rfl fun Q' hQ' ↦ ?_
    rw [hzred, Q'.res_sub_algebraMap (hyV v hQ')]
  rw [hψM, map_prod, CurvePlace.res_prod _ _ _ fun v _ ↦ (hfac v).1]
  simp_rw [fun v ↦ (hfac v).2]
  -- compare with the evaluation of the product
  simp only [eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  have hsign : ∏ v : Ext C F', ∏ Q ∈ zeros 𝓀 (red C (xF C F') v),
      ((-1 : 𝓀) ^ ord (red C (xF C F') v) Q) = (-1) ^ n := by
    rw [show n = _ from (sum_sum_ord hp hp1 (F' := F')).symm, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun v _ ↦ by rw [Finset.prod_pow_eq_pow_sum]
  rw [← hsign, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun Q _ ↦ ?_
  rw [← mul_pow, neg_one_mul, neg_sub]

end Identity

/-! ### Disc degree = sum of branch orders -/

section Matching

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) [Fintype (Ext C F')]
  [Algebra.IsSeparable (RatFunc C) F']

open Classical in
/-- The **vertex degree** of a point `P'` of `R' = DRint 0 1 F'`: the sum of `ord_Q x̄` over the
branches `(v, Q)` whose point is `P'`. -/
noncomputable def vertexDegreeD (P' : Ideal (DRint (0 : C) 1 F')) : ℕ :=
  ∑ v : Ext C F', ∑ Q ∈ (zeros 𝓀 (red C (xF C F') v)).attach,
    if placeIdealD v Q.2 = P' then ord (red C (xF C F') v) Q.1 else 0

include hp hp1 in
/-- **B1 for the vertex chart (S6 for the disc chart).** For a maximal ideal `P'` of
`R' = DRint 0 1 F'` and a disc valuation `ν` of the open unit disc, the disc degree of `P'` (the
sum of the local degrees of the extensions of `ν` centred at `P'`) equals the vertex degree of
`P'` (the sum of `ord_Q x̄` over the branches through `P'`). -/
theorem discDegree_eq_vertexDegreeD (ν : DiscVal (0 : C) 1) (P' : Ideal (DRint (0 : C) 1 F'))
    [hP' : P'.IsMaximal] :
    discDegree ν P' = vertexDegreeD P' := by
  classical
  -- the finitely many maximal ideals to separate from `P'`
  set T₁ : Finset (Ideal (DRint (0 : C) 1 F')) :=
    Finset.univ.image (fun g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F' ↦
      center (isDiscVal_comap_extValuation g))
  set T₂ : Finset (Ideal (DRint (0 : C) 1 F')) := Finset.univ.biUnion fun v : Ext C F' ↦
    (zeros 𝓀 (red C (xF C F') v)).attach.image fun Q ↦ placeIdealD v Q.2
  set T := (T₁ ∪ T₂).erase P'
  obtain ⟨e, he1, heQ⟩ := exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    refine ⟨?_, hne⟩
    rcases Finset.mem_union.1 hQ with hQ | hQ
    · obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hQ
      exact center_isMaximal one_ne_zero _
    · obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.1 hQ
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hv
      exact placeIdealD_isMaximal v Q.2
  set y : DRint (0 : C) 1 F' := e - 1
  obtain ⟨P, hP⟩ := exists_lift_normPoly one_ne_zero y.2
  -- the disc side
  have hdisc : discDegree ν P' =
      (P.map (Ideal.Quotient.mk (discIdeal (0 : C) 1))).natTrailingDegree := by
    rw [← sum_natDegree_eq_natTrailingDegree ν y.2 P hP, discDegree]
    refine Finset.sum_congr (Finset.filter_congr fun g _ ↦ ?_) fun _ _ ↦ rfl
    have hval : ‖toLocal g (y : F')‖ < 1 ↔ extValuation g (y : F') < 1 := by
      rw [extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
    rw [hval]
    constructor
    · intro h
      rw [← mem_center_iff (isDiscVal_comap_extValuation g), h]
      exact he1
    · intro hlt
      by_contra hne
      have he : extValuation g (e : F') < 1 := (mem_center_iff _ e).1
        (heQ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_univ g))⟩))
      have hy1 : extValuation g ((y : F')) = 1 := by
        rw [show (y : F') = -1 + (e : F') by simp [y]; ring,
          Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, map_one]; exact he),
          Valuation.map_neg, map_one]
      exact lt_irrefl 1 (hy1 ▸ hlt)
  rw [hdisc]
  -- the vertex side
  obtain ⟨v₀⟩ : Nonempty (Ext C F') := by
    rw [← Fintype.card_pos_iff, ← Finset.card_univ]
    by_contra h0
    simp only [not_lt, nonpos_iff_eq_zero, Finset.card_eq_zero] at h0
    have := sum_inertiaDeg_eq hp hp1 (F := F')
    rw [h0, Finset.sum_empty] at this
    exact Module.finrank_pos.ne' this.symm
  obtain ⟨Q₀, hQ₀⟩ := exists_mem_zeros v₀
  set ψ := (placeHomD v₀ hQ₀).comp (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F'))
  have hsupp : (P.map (Ideal.Quotient.mk (discIdeal (0 : C) 1))).natTrailingDegree =
      (P.map ψ).natTrailingDegree := by
    unfold natTrailingDegree trailingDegree
    congr 2
    ext i
    simp only [mem_support_iff, coeff_map, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    rw [mem_discIdeal_iff_placeHomD v₀ hQ₀]
    rfl
  rw [hsupp, map_lift_eq_prodD hp hp1 y P hP v₀ hQ₀, ← rootMultiplicity_eq_natTrailingDegree']
  -- the multiplicity of the root `0`
  rw [rootMultiplicity_prod_monic _ _ (fun v ↦ monic_prod_of_monic _ _ fun Q _ ↦
    (monic_X_sub_C _).pow _), vertexDegreeD]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [rootMultiplicity_prod_X_sub_C_pow, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun Q _ ↦ ?_
  have hy : Q.1.res (red C (y : F') v) = placeHomD v Q.2 e - 1 := by
    rw [← placeHomD_apply v Q.2, _root_.map_sub, map_one]
  have hiff : Q.1.res (red C (y : F') v) = 0 ↔ placeIdealD v Q.2 = P' := by
    constructor
    · intro h0
      by_contra hne
      have heQ' := heQ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _,
          Finset.mem_image.2 ⟨Q, Finset.mem_attach _ _, rfl⟩⟩)⟩)
      rw [mem_placeIdealD_iff] at heQ'
      rw [hy] at h0
      change Q.1.res (redD v e) - 1 = 0 at h0
      rw [heQ', zero_sub, neg_eq_zero] at h0
      exact one_ne_zero h0
    · intro h
      rw [← placeHomD_apply v Q.2, ← RingHom.mem_ker, ← placeIdealD, h]
      exact he1
  simp only [hiff]

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- The vertex degree as a sum over the branches through `P'`. -/
lemma vertexDegreeD_eq_sum (P' : Ideal (DRint (0 : C) 1 F')) :
    vertexDegreeD P' = ∑ b : OuterBranch C F',
      (open Classical in if b ∈ discBranches P' then ord (red C (xF C F') b.1) b.2.1 else 0) := by
  classical
  rw [Fintype.sum_sigma, vertexDegreeD]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun Q _ ↦ ?_
  simp only [discBranches, Set.mem_setOf_eq]

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- The vertex degree as a finite sum over the branches through `P'`. -/
lemma vertexDegreeD_eq_finsum (P' : Ideal (DRint (0 : C) 1 F')) :
    vertexDegreeD P' = ∑ᶠ (b : OuterBranch C F') (_ : b ∈ discBranches P'),
      ord (red C (xF C F') b.1) b.2.1 := by
  classical
  rw [vertexDegreeD_eq_sum, finsum_mem_def, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Set.indicator_apply]

end Matching

/-! ### The interfaces `DiscDegreeSum` and `SheetSmooth` -/

section Interfaces

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **(1′) `DiscDegreeSum`**: the disc degree of a point over the residue point of the vertex chart
is the sum of `ord_Q x̄` over the branches through it. -/
theorem discDegreeSum (G : Type*) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
    [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
    [Algebra.IsSeparable (RatFunc C) G] : DiscDegreeSum (C := C) G := by
  intro ν P' _ _
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  rw [discDegree_eq_vertexDegreeD hp hp1, vertexDegreeD_eq_finsum]

include hp hp1 in
/-- A point of disc degree one carries exactly one branch, and `x̄` is a uniformizer there. -/
theorem exists_branch_of_discDegree_eq_one {G : Type*} [Field G] [Algebra (RatFunc C) G]
    [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
    [Algebra.IsSeparable (RatFunc C) G] (ν : DiscVal (0 : C) 1)
    (P' : Ideal (DRint (0 : C) 1 G)) [P'.IsMaximal] (h1 : discDegree ν P' = 1) :
    ∃ b : OuterBranch C G, discBranches P' = {b} ∧ ord (red C (xF C G) b.1) b.2.1 = 1 := by
  classical
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  rw [discDegree_eq_vertexDegreeD hp hp1, vertexDegreeD_eq_sum] at h1
  set f : OuterBranch C G → ℕ := fun b ↦
    if b ∈ discBranches P' then ord (red C (xF C G) b.1) b.2.1 else 0
  have hf1 : ∀ b ∈ discBranches P', 1 ≤ f b := fun b hb ↦ by
    simp only [f, if_pos hb]
    exact one_le_ord b.2.2
  have hle : ∀ b, f b ≤ 1 := fun b ↦
    h1 ▸ Finset.single_le_sum (f := f) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ b)
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1.trans_ne one_ne_zero)
  have hbS : b ∈ discBranches P' := by
    by_contra h
    exact hb (by simp only [if_neg h])
  refine ⟨b, Set.eq_singleton_iff_unique_mem.2 ⟨hbS, fun b' hb' ↦ ?_⟩, ?_⟩
  · by_contra hne
    have := Finset.sum_le_sum_of_subset (f := f) (Finset.subset_univ {b', b})
    rw [Finset.sum_pair hne, h1] at this
    have := hf1 b' hb'
    have := hf1 b hbS
    omega
  · have := le_antisymm (hle b) (hf1 b hbS)
    simpa [f, if_pos hbS] using this

include hp hp1 in
/-- **(1) `SheetSmooth`: a sheet point is smooth.** A point of the vertex chart of disc degree one
carries one branch `(v, Q)` with `ord_Q x̄ = 1` (`DiscDegreeSum`), so `x` reduces to a
uniformizer at `Q` and `exists_eq_of_uniformizer` applies. -/
theorem sheetSmooth (G : Type*) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
    [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
    [Algebra.IsSeparable (RatFunc C) G] : SheetSmooth (C := C) G := by
  intro ν P' _ _ h1
  obtain ⟨⟨v, Q, hQ⟩, hS, hord⟩ := exists_branch_of_discDegree_eq_one hp hp1 ν P' h1
  have hP' : placeIdealD v hQ = P' := by
    have : (⟨v, Q, hQ⟩ : OuterBranch C G) ∈ discBranches P' := hS ▸ rfl
    exact this
  refine ⟨⟨v, Q, hQ⟩, hS, fun α hα ↦ ?_⟩
  have hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C G) v)), R ≠ Q →
      placeIdealD v hR ≠ placeIdealD v hQ := by
    intro R hR hne heq
    have hmem : (⟨v, R, hR⟩ : OuterBranch C G) ∈ discBranches P' := by
      change placeIdealD v hR = P'
      rw [heq, hP']
    rw [hS, Set.mem_singleton_iff, Sigma.mk.inj_iff] at hmem
    exact hne (congrArg Subtype.val (eq_of_heq hmem.2))
  have ht : Q.valuation (redD v (xD (F' := G))) = exp (-1) := by
    rw [redD_xD, valuation_x hQ]
    simp only at hord
    rw [hord]
    rfl
  obtain ⟨y, s, hs, hys⟩ := exists_eq_of_uniformizer hp hp1 v hQ hoth ht hα
  exact ⟨y, s, hP' ▸ hs, hys⟩

end Interfaces

end TypeFour

end SemistableReduction
