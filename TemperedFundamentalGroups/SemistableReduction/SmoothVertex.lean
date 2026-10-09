/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothPoint
import TemperedFundamentalGroups.SemistableReduction.NodeDouble
import TemperedFundamentalGroups.SemistableReduction.DiscCount

/-!
# Smooth points over the residue point of the vertex chart

Blueprint §9.9, S7(c) (one branch, over `C`; input of §9.10 A6). Let `R' = DRint 0 1 F'` be the
integral closure of the vertex chart `O_C[x]` (the disc chart of `w_{0,1}`, `DiscCount`) in `F'`,
`v` an extension of the Gauss point `w_{0,1}` with residue curve `κ(v)`, `ρ = redD : R' → κ(v)` the
reduction, and `Q` a zero of `x̄` on `κ(v)` with point `P' = placeIdealD` (a maximal ideal of `R'`
over `(𝔪_C, x)`).

* `isIntegral_of_le` (**maximum principle for the vertex chart**): an element integral over `C[x]`
  of value `≤ 1` at all extensions of `w_{0,1}` is integral over `O_C[x]`;
* `redD_isIntegral`, `exists_redD_eq_aeval`, `exists_span`, `exists_frac`, `exists_tau`: the
  reduction of `R'` at `v` (integral over `k[x̄]`, normalization finitely spanned, fractions,
  clearing poles away from `P'`), as for the node chart (`NodeSide`);
* **`exists_eq_of_uniformizer`** (`δ_y = 0` on the branch): if no other zero of `x̄` on `κ(v)` has
  the point `P'` and some `t ∈ R'` reduces to a uniformizer at `Q`, then the local ring of the
  reduction at `P'` is `O_Q`: every `a ∈ O_Q` is `ρ y / ρ s` with `s ∉ P'`;
* `exists_eq_of_jets`: closedness (reaching `O_Q` modulo every power suffices).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

namespace SmoothVertex

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm GaussTube DiscCount

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-! ### The vertex chart -/

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma gaussCoord_zero_one : gaussCoord (0 : C) 1 = RatFunc.X := by
  rw [gaussCoord, gaussLin, inv_one, map_one, one_mul, map_zero, sub_zero,
    RatFunc.algebraMap_X]

omit [IsAlgClosed C] in
lemma mem_discRing_iff {f : RatFunc C} :
    f ∈ discRing (0 : C) 1 ↔ ∃ Q : C[X], Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1 ∧
      algebraMap C[X] (RatFunc C) Q = f := by
  rw [mem_polyChart_iff, gaussCoord_zero_one]
  simp only [RatFunc.aeval_X_left_eq_algebraMap]

omit [IsAlgClosed C] in
lemma X_mem_discRing : (RatFunc.X : RatFunc C) ∈ discRing (0 : C) 1 :=
  mem_discRing_iff.2 ⟨X, by rw [Gauss.sup_X, Units.val_one], RatFunc.algebraMap_X⟩

omit [IsAlgClosed C] in
lemma algebraMap_mem_discRing' (b : HenselComplete.integers C) :
    algebraMap C (RatFunc C) b ∈ discRing (0 : C) 1 :=
  algebraMap_mem_discRing (by exact_mod_cast (HenselComplete.mem_integers_iff _).1 b.2)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma valuation_algebraMap_le (v : Ext C F') {f : RatFunc C} (hf : f ∈ discRing (0 : C) 1) :
    v.1 (algebraMap (RatFunc C) F' f) ≤ 1 := by
  obtain ⟨Q, hQ, rfl⟩ := mem_discRing_iff.1 hf
  rw [valuation_algebraMap, gauss1_algebraMap]
  exact hQ

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma valuation_le_one_D (v : Ext C F') (y : DRint (0 : C) 1 F') : v.1 (y : F') ≤ 1 := by
  let φ : discRing (0 : C) 1 →+* v.1.integer :=
    { toFun := fun a ↦ ⟨algebraMap (RatFunc C) F' a, valuation_algebraMap_le v a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hint : IsIntegral v.1.integer (y : F') :=
    IsIntegral.map_of_comp_eq φ (RingHom.id F') (by ext; rfl) y.2
  exact (Valuation.integer.integers v.1).mem_of_integral hint

/-- The reduction `R' → κ(v)`. -/
noncomputable def redD (v : Ext C F') :
    DRint (0 : C) 1 F' →+* ResidueField v.1.valuationSubring where
  toFun y := red C (y : F') v
  map_one' := by simp [red_one]
  map_mul' y z := by
    simp only [Subalgebra.coe_mul]
    exact red_mul (valuation_le_one_D v y) (valuation_le_one_D v z)
  map_zero' := by simp [red_zero]
  map_add' y z := by
    simp only [Subalgebra.coe_add]
    exact red_add (valuation_le_one_D v y) (valuation_le_one_D v z)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma redD_apply (v : Ext C F') (y : DRint (0 : C) 1 F') : redD v y = red C (y : F') v := rfl

/-- `x` as an element of `R'`. -/
noncomputable def xD : DRint (0 : C) 1 F' :=
  algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') ⟨RatFunc.X, X_mem_discRing⟩

/-- The constants of `O_C` as elements of `R'`. -/
noncomputable def constD (b : HenselComplete.integers C) : DRint (0 : C) 1 F' :=
  algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') ⟨_, algebraMap_mem_discRing' b⟩

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma redD_xD (v : Ext C F') : redD v (xD (F' := F')) = red C (xF C F') v := rfl

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
lemma redD_constD (v : Ext C F') (b : HenselComplete.integers C) :
    redD v (constD b) = algebraMap 𝓀 _ (residue _ b) := by
  rw [redD_apply]
  change red C (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) b)) v = _
  rw [← IsScalarTower.algebraMap_apply,
    red_algebraMap_C _ (by exact_mod_cast (HenselComplete.mem_integers_iff _).1 b.2)]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- Every polynomial in `x̄` is a reduction. -/
lemma exists_redD_eq_aeval (v : Ext C F') (P : 𝓀[X]) :
    ∃ y : DRint (0 : C) 1 F', redD v y = aeval (red C (xF C F') v) P := by
  obtain ⟨Q, rfl⟩ := map_surjective _ (residue_surjective (R := HenselComplete.integers C)) P
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), constD (Q.coeff i) * xD ^ i, ?_⟩
  rw [map_sum, aeval_eq_sum_range' (n := Q.natDegree + 1)
    (Nat.lt_succ_of_le natDegree_map_le)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, redD_constD, redD_xD, coeff_map, Algebra.smul_def]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- Reductions of the chart lie in `k[x̄]`. -/
lemma redD_algebraMap_mem (v : Ext C F') (a : discRing (0 : C) 1) :
    redD v (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') a) ∈
      Algebra.adjoin 𝓀 {red C (xF C F') v} := by
  obtain ⟨a, ha⟩ := a
  have hle (b : RatFunc C) (hb : b ∈ discRing (0 : C) 1) :
      v.1 (algebraMap (RatFunc C) F' b) ≤ 1 := valuation_algebraMap_le v hb
  change red C (algebraMap (RatFunc C) F' a) v ∈ _
  induction ha using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, hb, rfl⟩ | hz
    · have hb' : ‖b‖₊ ≤ 1 := by
        have : NormedField.valuation b ≤ 1 := hb
        rwa [NormedField.valuation_apply] at this
      rw [← IsScalarTower.algebraMap_apply, red_algebraMap_C _ hb']
      exact Subalgebra.algebraMap_mem _ _
    · rw [Set.mem_singleton_iff.1 hz, gaussCoord_zero_one]
      exact Algebra.self_mem_adjoin_singleton _ _
  | zero => simp [red_zero]
  | one => simp [red_one]
  | add a b ha' hb' ha hb =>
    rw [map_add, red_add (hle a ha') (hle b hb')]
    exact add_mem ha hb
  | neg a ha' ha =>
    rw [_root_.map_neg, red_neg (hle a ha')]
    exact neg_mem ha
  | mul a b ha' hb' ha hb =>
    rw [map_mul, red_mul (hle a ha') (hle b hb')]
    exact mul_mem ha hb

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- Reductions of `R'` are integral over `k[x̄]`. -/
lemma redD_isIntegral (v : Ext C F') (y : DRint (0 : C) 1 F') :
    IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) (redD v y) := by
  obtain ⟨p, hm, hp⟩ := y.2
  let ψ : discRing (0 : C) 1 →+* Algebra.adjoin 𝓀 {red C (xF C F') v} :=
    ((redD v).comp (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F'))).codRestrict
      (Algebra.adjoin 𝓀 {red C (xF C F') v}).toSubring fun a ↦ redD_algebraMap_mem v a
  refine ⟨p.map ψ, hm.map ψ, ?_⟩
  rw [eval₂_map]
  have h : (algebraMap (Algebra.adjoin 𝓀 {red C (xF C F') v}) _).comp ψ =
      (redD v).comp (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) := rfl
  rw [h, ← hom_eval₂]
  have h2 : eval₂ (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) y p = 0 := by
    apply Subtype.ext
    have := hom_eval₂ p (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F'))
      (DRint (0 : C) 1 F').val.toRingHom y
    exact this.trans hp
  rw [h2, map_zero]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- Reductions of `R'` lie in every place of `κ(v)` containing `x̄`. -/
lemma redD_mem_V (v : Ext C F') (y : DRint (0 : C) 1 F')
    {R : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)} (hx : red C (xF C F') v ∈ R.V) :
    redD v y ∈ R.V :=
  isIntegral_mem_V v (redD_isIntegral v y) hx

/-! ### The point of a branch -/

section Place

lemma xbar_mem_V (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : red C (xF C F') v ∈ Q.V :=
  Q.valuation_le_one_iff.1 (valuation_x_lt_one hQ).le

/-- The reduction of `R'` at the branch `Q`: `y ↦ ȳ(Q)`. -/
noncomputable def placeHomD (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : DRint (0 : C) 1 F' →+* 𝓀 where
  toFun y := Q.res (redD v y)
  map_one' := by rw [map_one, Q.res_one]
  map_mul' y z := by
    rw [map_mul, Q.res_mul (redD_mem_V v y (xbar_mem_V v hQ)) (redD_mem_V v z (xbar_mem_V v hQ))]
  map_zero' := by rw [map_zero, Q.res_zero]
  map_add' y z := by
    rw [map_add, Q.res_add (redD_mem_V v y (xbar_mem_V v hQ)) (redD_mem_V v z (xbar_mem_V v hQ))]

lemma placeHomD_surjective (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : Function.Surjective (placeHomD v hQ) := by
  intro t
  obtain ⟨κ, rfl⟩ := residue_surjective t
  refine ⟨constD κ, ?_⟩
  change Q.res (redD v (constD κ)) = _
  rw [redD_constD, Q.res_algebraMap]

/-- The point `P'` of the branch `Q`: a maximal ideal of `R'`. -/
noncomputable def placeIdealD (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : Ideal (DRint (0 : C) 1 F') :=
  RingHom.ker (placeHomD v hQ)

lemma placeIdealD_isMaximal (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : (placeIdealD v hQ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (placeHomD_surjective v hQ)

lemma mem_placeIdealD_iff (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (y : DRint (0 : C) 1 F') :
    y ∈ placeIdealD v hQ ↔ Q.res (redD v y) = 0 := RingHom.mem_ker

lemma redD_ne_zero_of_notMem (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) {y : DRint (0 : C) 1 F'}
    (hy : y ∉ placeIdealD v hQ) : redD v y ≠ 0 := fun h ↦ hy <| by
  rw [mem_placeIdealD_iff, h, Q.res_zero]

end Place

/-! ### Spanning and clearing poles -/

/-- **The integral closure of `k[x̄]` is spanned over `ρ(R')` by finitely many elements.** -/
theorem exists_span (v : Ext C F') :
    ∃ G : Finset (ResidueField v.1.valuationSubring),
      (∀ g ∈ G, IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) g) ∧
      ∀ α, IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) α →
        ∃ r : ResidueField v.1.valuationSubring → DRint (0 : C) 1 F',
          α = ∑ g ∈ G, redD v (r g) * g := by
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_red_x (F := F') v)
  obtain ⟨G, hG, hsp⟩ := CurveGenerators.exists_generators (transcendental_red_x (F := F') v)
  refine ⟨G, hG, fun α hα ↦ ?_⟩
  obtain ⟨c', hc'⟩ := hsp α hα
  choose r hr using fun g ↦ exists_redD_eq_aeval v (c' g)
  exact ⟨r, by rw [hc']; exact Finset.sum_congr rfl fun g _ ↦ by rw [hr]⟩

/-- **Clearing poles away from the point.** If `P'` is not the point of any other zero of `x̄`
on `κ(v)`, every `g ∈ O_Q` becomes integral over `k[x̄]` after multiplication by the reduction of
some `τ ∈ R' ∖ P'`. -/
theorem exists_tau (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v))
    (hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v)), R ≠ Q →
      placeIdealD v hR ≠ placeIdealD v hQ)
    {g : ResidueField v.1.valuationSubring} (hg : g ∈ Q.V) :
    ∃ τ : DRint (0 : C) 1 F', τ ∉ placeIdealD v hQ ∧
      IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) (redD v τ * g) := by
  classical
  set xb := red C (xF C F') v
  set P' := placeIdealD v hQ
  haveI : P'.IsMaximal := placeIdealD_isMaximal v hQ
  have hQx : Q.res xb = 0 := Q.res_eq_zero_of_lt_one (valuation_x_lt_one hQ)
  set S : Finset (CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :=
    (CurvePlace.finite_setOf_notMem g).toFinset.filter fun R ↦ xb ∈ R.V
  have hS (R) : R ∈ S ↔ g ∉ R.V ∧ xb ∈ R.V := by
    simp [S, Set.Finite.mem_toFinset]
  have hy (R : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (hR : R ∈ S) :
      ∃ y : DRint (0 : C) 1 F', y ∉ P' ∧ R.valuation (redD v y) < 1 := by
    obtain ⟨hgR, hxR⟩ := (hS R).1 hR
    have hRQ : R ≠ Q := fun h ↦ hgR (h ▸ hg)
    by_cases hz : R ∈ zeros 𝓀 xb
    · have hne := hoth R hz hRQ
      have hnle : ¬ placeIdealD v hz ≤ P' := fun hle ↦
        hne ((placeIdealD_isMaximal v hz).eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hle)
      obtain ⟨y, hyR, hyP⟩ := Set.not_subset.1 hnle
      refine ⟨y, hyP, ?_⟩
      rw [SetLike.mem_coe, mem_placeIdealD_iff] at hyR
      have := R.valuation_sub_res_lt_one (redD_mem_V v y (xbar_mem_V v hz))
      rwa [hyR, map_zero, sub_zero] at this
    · obtain ⟨κ₀, hκ₀⟩ := residue_surjective (R.res xb)
      refine ⟨xD - constD κ₀, fun hmem ↦ ?_, ?_⟩
      · rw [mem_placeIdealD_iff] at hmem
        rw [_root_.map_sub, redD_xD, redD_constD, hκ₀,
          Q.res_sub_algebraMap (xbar_mem_V v hQ), hQx, zero_sub, neg_eq_zero] at hmem
        apply hz
        rw [mem_zeros]
        intro hinv
        have h1 := R.valuation_sub_res_lt_one hxR
        rw [hmem, map_zero, sub_zero] at h1
        have h2 := R.valuation_le_one_iff.2 hinv
        rw [map_inv₀] at h2
        have hx0 : xb ≠ 0 := red_xF_ne_zero' v
        have := mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2
        rw [mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 hx0)] at this
        exact lt_irrefl 1 this
      · rw [_root_.map_sub, redD_xD, redD_constD, hκ₀]
        exact R.valuation_sub_res_lt_one hxR
  choose! y hyP hyR using hy
  set τ : DRint (0 : C) 1 F' := ∏ R ∈ S, y R ^ R.poleOrder g
  refine ⟨τ, ?_, ?_⟩
  · intro hτ
    obtain ⟨R, hR, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).1 hτ
    exact hyP R hR (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hmem)
  · refine CurveGenerators.isIntegral_of_forall_mem fun R hxR ↦ ?_
    by_cases hR : R ∈ S
    · obtain ⟨hgR, -⟩ := (hS R).1 hR
      have h1 : R.valuation (redD v (y R)) ≤ exp (-1) :=
        WithZero.le_exp_of_lt_exp_add_one (by simpa using hyR R hR)
      have hτR : R.valuation (redD v τ) ≤ exp (-(R.poleOrder g : ℤ)) := by
        simp only [τ, map_prod, map_pow]
        rw [← Finset.mul_prod_erase S _ hR]
        calc R.valuation (redD v (y R)) ^ R.poleOrder g *
              ∏ R' ∈ S.erase R, R.valuation (redD v (y R')) ^ R'.poleOrder g ≤
              exp (-1) ^ R.poleOrder g * 1 := by
              refine mul_le_mul' (pow_le_pow_left₀ zero_le h1 _) (Finset.prod_le_one' fun R' _ ↦
                pow_le_one₀ zero_le (R.valuation_le_one_iff.2 (redD_mem_V v _ hxR)))
          _ = exp (-(R.poleOrder g : ℤ)) := by rw [mul_one, ← exp_nsmul]; simp
      refine R.valuation_le_one_iff.1 ?_
      rw [map_mul, R.valuation_eq_exp_poleOrder hgR]
      calc R.valuation (redD v τ) * exp (R.poleOrder g : ℤ) ≤
            exp (-(R.poleOrder g : ℤ)) * exp (R.poleOrder g : ℤ) := by gcongr
        _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    · have hgR : g ∈ R.V := by
        by_contra h
        exact hR ((hS R).2 ⟨h, hxR⟩)
      exact mul_mem (redD_mem_V v _ hxR) hgR

/-! ### Maximum principle and fractions -/

section Frac

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **The maximum principle for the vertex chart**: an element integral over `C[x]` with value
`≤ 1` at all extensions of `w_{0,1}` is integral over `O_C[x]`. -/
theorem isIntegral_of_le {y : F'} (hint : IsIntegral (Algebra.adjoin C {xF C F'}) y)
    (hout : ∀ v : Ext C F', v.1 y ≤ 1) : IsIntegral (discRing (0 : C) 1) y := by
  classical
  set μ := minpoly (RatFunc C) y
  have hyi : IsIntegral (RatFunc C) y := Algebra.IsIntegral.isIntegral y
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_orthonormal_basis ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F') hp hp1)
  have hint0 : IsIntegral (Algebra.adjoin C {xF C F'}) (xF C F' ^ 0 * y) := by
    rwa [pow_zero, one_mul]
  have hmem (n : ℕ) : μ.coeff n ∈ discRing (0 : C) 1 := by
    obtain ⟨Q, hQ⟩ := minpoly_coeff_mul_pow hint0 n
    rw [zero_mul, pow_zero, mul_one] at hQ
    refine mem_discRing_iff.2 ⟨Q, ?_, hQ.symm⟩
    rw [← gauss1_algebraMap, ← hQ]
    exact gauss1_minpoly_coeff_le hb (gnorm_le_iff.2 hout) n
  have hO : (μ.coeffs : Set (RatFunc C)) ⊆ discRing (0 : C) 1 := fun a ha ↦ by
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 ha
    exact hmem n
  refine ⟨μ.toSubring _ hO, (monic_toSubring _ _ _).2 (minpoly.monic hyi), ?_⟩
  have : (μ.toSubring _ hO).map (discRing (0 : C) 1).subtype = μ := map_toSubring _ _ _
  have h : eval₂ (algebraMap (discRing (0 : C) 1) F') y (μ.toSubring _ hO) = aeval y μ := by
    conv_rhs => rw [← this]
    rw [aeval_def, eval₂_map]
    rfl
  rw [h, minpoly.aeval]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [CharZero C] in
/-- A polynomial in `x` with integral coefficients, as an element of `R'`. -/
lemma polyD_mem {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) :
    algebraMap C[X] (RatFunc C) Q ∈ discRing (0 : C) 1 := by
  refine mem_discRing_iff.2 ⟨Q, Gauss.sup_le_iff.2 fun i ↦ ?_, rfl⟩
  simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply]
  exact_mod_cast hQ i

/-- A polynomial in `x` with integral coefficients, as an element of `R'`. -/
noncomputable def polyD (Q : C[X]) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) : DRint (0 : C) 1 F' :=
  algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') ⟨_, polyD_mem hQ⟩

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [CharZero C] in
lemma coe_polyD (Q : C[X]) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) :
    ((polyD (F' := F') Q hQ : DRint (0 : C) 1 F') : F') = aeval (xF C F') Q :=
  (aeval_xF Q).symm

include hp hp1 in
/-- **Fractions**: every element of `κ(v)` is a quotient of reductions of `R'`. -/
theorem exists_frac (v : Ext C F') (α : ResidueField v.1.valuationSubring) :
    ∃ p q : DRint (0 : C) 1 F', redD v q ≠ 0 ∧ redD v p = α * redD v q := by
  classical
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  obtain ⟨b, hb, -, hres⟩ := exists_orthonormal_basis' ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F') hp hp1)
  set K : Subfield (ResidueField v.1.valuationSubring) := Subfield.closure (redD v).range
  have hR (y : DRint (0 : C) 1 F') : redD v y ∈ K := Subfield.subset_closure ⟨y, rfl⟩
  have hpoly (Q : C[X]) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1)
      (h1 : Gauss.sup (NormedField.valuation (K := C)) 1 Q = 1) :
      redD v (polyD Q hQ) ≠ 0 := by
    rw [redD_apply, coe_polyD, Ne, red_eq_zero_iff (by rw [valuation_aeval_xF, h1]),
      valuation_aeval_xF, h1]
    exact lt_irrefl 1
  -- `κ(w_{0,1})` lands in `K`
  have hbase (φ : ResidueField (gauss1 C).valuationSubring) :
      algebraMap _ (ResidueField v.1.valuationSubring) φ ∈ K := by
    obtain ⟨⟨ψ, hψ⟩, rfl⟩ := residue_surjective φ
    have hψ' : gauss1 C ψ ≤ 1 := hψ
    have hD : ψ.denom ≠ 0 := ψ.denom_ne_zero
    obtain ⟨γ, hγ0, D', hD', hD'1, hD'c⟩ := exists_normalize hD
    set N' : C[X] := Polynomial.C γ⁻¹ * ψ.num
    have hγ' : algebraMap C[X] (RatFunc C) (Polynomial.C γ) ≠ 0 := by simpa using hγ0
    have hψN : ψ * algebraMap C[X] (RatFunc C) D' = algebraMap C[X] (RatFunc C) N' := by
      have hden : algebraMap C[X] (RatFunc C) ψ.denom ≠ 0 := by simpa using hD
      have h1 : ψ * algebraMap C[X] (RatFunc C) ψ.denom = algebraMap C[X] (RatFunc C) ψ.num := by
        have := RatFunc.num_div_denom ψ
        rw [div_eq_iff hden] at this
        exact this.symm
      have e1 : algebraMap C[X] (RatFunc C) (Polynomial.C γ⁻¹) *
          algebraMap C[X] (RatFunc C) (Polynomial.C γ) = 1 := by
        rw [← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hγ0, Polynomial.C_1, map_one]
      refine mul_right_cancel₀ hγ' ?_
      rw [mul_assoc, ← map_mul, mul_comm D', ← hD', h1]
      simp only [N', map_mul]
      rw [mul_comm (algebraMap C[X] (RatFunc C) (Polynomial.C γ⁻¹)), mul_assoc, e1, mul_one]
    have hN'1 : Gauss.sup (NormedField.valuation (K := C)) 1 N' ≤ 1 := by
      rw [← gauss1_algebraMap, ← hψN, map_mul, gauss1_algebraMap, hD'1, mul_one]
      exact hψ'
    have hN'c (i : ℕ) : ‖N'.coeff i‖ ≤ 1 := by
      have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) N' i).trans hN'1
      simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply] at this
      exact_mod_cast this
    have hred : algebraMap _ (ResidueField v.1.valuationSubring)
        (residue (gauss1 C).valuationSubring ⟨ψ, hψ⟩) =
        red C (algebraMap (RatFunc C) F' ψ) v := by
      have := red_algebraMap_mul (w := v) ψ hψ' (f := 1) (by simp)
      rw [mul_one, red_one, mul_one] at this
      exact this.symm
    have hψv : v.1 (algebraMap (RatFunc C) F' ψ) ≤ 1 := by rwa [valuation_algebraMap]
    have hD'v : v.1 (aeval (xF C F') D') ≤ 1 := by rw [valuation_aeval_xF, hD'1]
    have hmul : redD v (polyD N' hN'c) =
        red C (algebraMap (RatFunc C) F' ψ) v * redD v (polyD D' hD'c) := by
      rw [redD_apply, redD_apply, coe_polyD, coe_polyD, ← red_mul hψv hD'v, aeval_xF,
        aeval_xF, ← map_mul, hψN]
    rw [hred, eq_div_of_mul_eq (hpoly D' hD'c hD'1) hmul.symm]
    exact div_mem (hR _) (hR _)
  -- the residues of the orthonormal basis land in `K`
  letI : Algebra C[X] F' := ((algebraMap (RatFunc C) F').comp
    (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples C[X] (RatFunc C)
    (Finset.univ.image b)
  obtain ⟨γ, hγ0, y', hy', hy'1, hy'c⟩ := exists_normalize hy0
  have hint (f : F') (hf : IsIntegral C[X] f) : IsIntegral (Algebra.adjoin C {xF C F'}) f := by
    have hrange : Algebra.adjoin C {xF C F'} = (aeval (xF C F') : C[X] →ₐ[C] F').range :=
      Algebra.adjoin_singleton_eq_range_aeval C (xF C F')
    set ψ : C[X] →+* Algebra.adjoin C {xF C F'} :=
      (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
        (aeval (xF C F') : C[X] →ₐ[C] F').rangeRestrict.toRingHom
    refine IsIntegral.map_of_comp_eq ψ (RingHom.id F') (RingHom.ext fun P ↦ ?_) hf
    change aeval (xF C F') P = algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) P)
    exact aeval_xF P
  have hbasis (l : Fin (inertiaDeg (gauss1 C) v.1)) : red C (b ⟨v, l⟩) v ∈ K := by
    set bl := b ⟨v, l⟩
    have hbl1 : gnorm C bl = 1 := gnorm_basis hb _
    have hyb : IsIntegral C[X] (y • bl) := hyint bl (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    set z : F' := aeval (xF C F') y' * bl
    have hzeq : z = algebraMap C F' γ⁻¹ * (y • bl) := by
      rw [Algebra.smul_def]
      change _ = _ * (algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) y) * bl)
      rw [← aeval_xF, hy', map_mul, aeval_C]
      have : algebraMap C F' γ⁻¹ * algebraMap C F' γ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hγ0, map_one]
      simp only [z]
      linear_combination (aeval (xF C F') y' * bl) * this.symm
    have hmemA (a : F') (ha : a ∈ Algebra.adjoin C {xF C F'}) :
        IsIntegral (Algebra.adjoin C {xF C F'}) a :=
      isIntegral_algebraMap (x := (⟨a, ha⟩ : Algebra.adjoin C {xF C F'}))
    have hzint : IsIntegral (Algebra.adjoin C {xF C F'}) z := by
      rw [hzeq]
      exact IsIntegral.mul (hmemA _ (Subalgebra.algebraMap_mem _ _)) (hint _ hyb)
    have hout : ∀ w : Ext C F', w.1 z ≤ 1 := fun w ↦ by
      simp only [z, map_mul, valuation_aeval_xF, hy'1, one_mul]
      exact (le_gnorm w bl).trans hbl1.le
    have hzR : IsIntegral (discRing (0 : C) 1) z := isIntegral_of_le hp hp1 hzint hout
    set zR : DRint (0 : C) 1 F' := ⟨z, hzR⟩
    set q : DRint (0 : C) 1 F' := polyD y' hy'c
    have hq : redD v q ≠ 0 := hpoly y' hy'c hy'1
    have hzq : redD v zR = redD v q * red C bl v := by
      have hq1 : v.1 (aeval (xF C F') y') ≤ 1 := by rw [valuation_aeval_xF, hy'1]
      rw [redD_apply, redD_apply]
      change red C (aeval (xF C F') y' * bl) v = red C ((polyD y' hy'c : DRint (0 : C) 1 F') :
        F') v * _
      rw [coe_polyD, red_mul hq1 ((le_gnorm v bl).trans hbl1.le)]
    have hbl : red C bl v = redD v zR / redD v q :=
      eq_div_of_mul_eq hq (by rw [mul_comm]; exact hzq.symm)
    rw [hbl]
    exact div_mem (hR _) (hR _)
  -- the residues of the basis span `κ(v)`
  obtain ⟨ℓ, hli, hℓ⟩ := hres v
  haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
    (ResidueField v.1.valuationSubring) := finite_residueField
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; rfl)
  have hℓK (l : Fin (inertiaDeg (gauss1 C) v.1)) : residue v.1.valuationSubring (ℓ l) ∈ K := by
    have hbl : v.1 (b ⟨v, l⟩) ≤ 1 := (le_gnorm v _).trans (gnorm_basis hb _).le
    have : residue v.1.valuationSubring (ℓ l) = red C (b ⟨v, l⟩) v := by
      rw [red_of_le hbl, eq_comm, ← sub_eq_zero, ← _root_.map_sub, residue_eq_zero_iff,
        Valuation.mem_maximalIdeal_iff]
      exact hℓ l
    rw [this]
    exact hbasis l
  have hαK : α ∈ K := by
    have hα : α ∈ Submodule.span (ResidueField (gauss1 C).valuationSubring)
        (Set.range fun l ↦ residue v.1.valuationSubring (ℓ l)) := by rw [hspan]; trivial
    obtain ⟨φ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hα
    refine sum_mem fun l _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (hbase _) (hℓK l)
  obtain ⟨a, ha, d, hd, had⟩ := Subfield.mem_closure_iff.1 hαK
  rw [Subring.closure_eq (redD v).range] at ha hd
  obtain ⟨p', rfl⟩ := ha
  obtain ⟨q', rfl⟩ := hd
  by_cases hq' : redD v q' = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← had, hq', div_zero, map_zero, zero_mul]
  · exact ⟨p', q', hq', by rw [← had, div_mul_cancel₀ _ hq']⟩

/-! ### The smooth point -/

include hp hp1 in
/-- **The local ring of the reduction at `P'` is `O_Q` if it contains a uniformizer** (S7(c),
`δ_y = 0` on the branch, the input of §9.10 A6). Let `Q` be a zero of `x̄` on `κ(v)` whose point
`P'` is not the point of any other zero of `x̄` on `κ(v)`, and let `t ∈ R'` reduce to a
uniformizer at `Q`. Then every `a ∈ O_Q` is `ρ y / ρ s` with `y, s ∈ R'`, `s ∉ P'`. -/
theorem exists_eq_of_uniformizer (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v))
    (hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v)), R ≠ Q →
      placeIdealD v hR ≠ placeIdealD v hQ)
    {t : DRint (0 : C) 1 F'} (ht : Q.valuation (redD v t) = exp (-1))
    {a : ResidueField v.1.valuationSubring} (ha : a ∈ Q.V) :
    ∃ y s : DRint (0 : C) 1 F', s ∉ placeIdealD v hQ ∧ redD v y = a * redD v s := by
  classical
  haveI : (placeIdealD v hQ).IsMaximal := placeIdealD_isMaximal v hQ
  set Ã := (integralClosure (Algebra.adjoin 𝓀 {red C (xF C F') v})
    (ResidueField v.1.valuationSubring)).toSubring
  obtain ⟨G, -, hsp⟩ := exists_span v
  obtain ⟨σ, hσ0, hσ⟩ := SmoothPoint.exists_conductor₁ (redD v) Ã G
    (fun α hα ↦ hsp α hα) (fun g _ ↦ exists_frac hp hp1 v g)
  refine SmoothPoint.exists_eq_of_uniformizer (redD v) Q Ã (placeIdealD v hQ)
    (fun r hr ↦ redD_ne_zero_of_notMem v hQ hr)
    (fun c ↦ ?_) hσ0 (redD_mem_V v σ (xbar_mem_V v hQ)) hσ
    (fun g hg ↦ ?_) ht ha
  · obtain ⟨b, rfl⟩ := residue_surjective c
    exact ⟨constD b, redD_constD v b⟩
  · obtain ⟨τ, hτP, hτ⟩ := exists_tau v hQ hoth hg
    exact ⟨τ, hτP, (mem_integralClosure_iff _ _).2 hτ⟩

include hp hp1 in
/-- **Closedness**: if every `a ∈ O_Q` is reached by `R'_{P'}` modulo every power of the maximal
ideal (`δ_y = 0` in the jet form of S7), it is reached exactly. -/
theorem exists_eq_of_jets (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v))
    (hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v)), R ≠ Q →
      placeIdealD v hR ≠ placeIdealD v hQ)
    {a : ResidueField v.1.valuationSubring}
    (hjet : ∀ M : ℕ, ∃ y s : DRint (0 : C) 1 F', s ∉ placeIdealD v hQ ∧
      Q.valuation (redD v y / redD v s - a) ≤ exp (-(M : ℤ))) :
    ∃ y s : DRint (0 : C) 1 F', s ∉ placeIdealD v hQ ∧ redD v y = a * redD v s := by
  classical
  haveI : (placeIdealD v hQ).IsMaximal := placeIdealD_isMaximal v hQ
  set Ã := (integralClosure (Algebra.adjoin 𝓀 {red C (xF C F') v})
    (ResidueField v.1.valuationSubring)).toSubring
  obtain ⟨G, -, hsp⟩ := exists_span v
  obtain ⟨σ, hσ0, hσ⟩ := SmoothPoint.exists_conductor₁ (redD v) Ã G
    (fun α hα ↦ hsp α hα) (fun g _ ↦ exists_frac hp hp1 v g)
  refine SmoothPoint.exists_eq_of_jets₁ (redD v) Q Ã (placeIdealD v hQ)
    (fun r hr ↦ redD_ne_zero_of_notMem v hQ hr) hσ0 (redD_mem_V v σ (xbar_mem_V v hQ)) hσ
    (fun g hg ↦ ?_) hjet
  obtain ⟨τ, hτP, hτ⟩ := exists_tau v hQ hoth hg
  exact ⟨τ, hτP, (mem_integralClosure_iff _ _).2 hτ⟩

end Frac

end SmoothVertex

end SemistableReduction
