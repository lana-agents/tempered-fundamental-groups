/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W7Statement
import TemperedFundamentalGroups.SemistableReduction.GaussNorm

/-!
# Smooth points over a residue disc of an unramified split cover

Blueprint §9.12 O6.1f (S8.2, type 1, the unramified case). Let `G / C(x)` be finite of degree
`n` and `θ ∈ G` integral over the vertex chart `O_C[x]`, whose minimal polynomial is congruent,
coefficientwise modulo elements of Gauss value `< 1`, to `∏ᵢ (Y - γᵢ)` with `γᵢ ∈ O_C` of pairwise
distinct residues (`SplitDatum`). Then:

* every extension `v` of `w_{0,1}` reduces `θ` to one of the constants `γ̄ᵢ`, and every `γ̄ᵢ` occurs
  (norm formula); hence there are exactly `n` extensions, all with `f = 1`, and `κ(v) = k(x̄)`;
* `x̄` has exactly one zero `Q_v` on each `κ(v)`, of order one;
* the `n` points `placeIdealD v Q_v` are distinct (separated by `θ - γᵢ`) and exhaust the points
  over
  the residue point `x̄ = 0` (disc count);
* **`isDiscSmooth_of_splitDatum`**: every point of `DRint 0 1 G` over the residue point is smooth.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace ClassicalSmooth

open GaussFibre GaussStability FundamentalInequality PlaceNorm DiscCount SmoothVertex GaussTube

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "𝒪" => HenselComplete.integers C

variable (C G) in
/-- **Unramified split datum** at the residue point `x̄ = 0` of `w_{0,1}`. -/
structure SplitDatum (θ : G) {n : ℕ} (γ : Fin n → 𝒪) : Prop where
  card : n = Module.finrank (RatFunc C) G
  integral : IsIntegral (discRing (0 : C) 1) θ
  sep : ∀ i j, i ≠ j → residue 𝒪 (γ i) ≠ residue 𝒪 (γ j)
  coeff : ∀ k, gauss1 C ((minpoly (RatFunc C) θ).coeff k -
    algebraMap C (RatFunc C) (((∏ i, (X - Polynomial.C (γ i))).map (algebraMap 𝒪 C)).coeff k)) < 1

variable {θ : G} {n : ℕ} {γ : Fin n → HenselComplete.integers C}

/-- The model polynomial `∏ᵢ (Y - γᵢ)`. -/
noncomputable def P₀ (γ : Fin n → 𝒪) : 𝒪[X] :=
  ∏ i, (X - Polynomial.C (γ i))

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
  in
lemma valuation_theta_le (h : SplitDatum C G θ γ) (v : Ext C G) : v.1 θ ≤ 1 :=
  valuation_le_one_D v ⟨θ, h.integral⟩

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
  in
/-- Elements of value `< 1` at every extension: a polynomial with coefficients of Gauss value `< 1`,
evaluated at an element of value `≤ 1`. -/
lemma valuation_aeval_lt_one (v : Ext C G) {t : G} (ht : v.1 t ≤ 1) {Q : (RatFunc C)[X]}
    (hQ : ∀ k, gauss1 C (Q.coeff k) < 1) : v.1 (aeval t Q) < 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_lt _ one_ne_zero fun k _ ↦ ?_
  rw [Algebra.smul_def, map_mul, valuation_algebraMap, map_pow]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hQ k) (pow_le_one₀ zero_le ht)

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
  in
lemma P₀_map_residue (γ : Fin n → 𝒪) :
    (P₀ γ).map (residue 𝒪) = ∏ i, (X - Polynomial.C (residue 𝒪 (γ i))) := by
  simp [P₀, Polynomial.map_prod]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
/-- **The reductions of `θ` are among the constants `γ̄ᵢ`.** -/
lemma exists_red_eq (h : SplitDatum C G θ γ) (v : Ext C G) :
    ∃ i, red C θ v = algebraMap 𝓀 _ (residue 𝒪 (γ i)) := by
  set PC : C[X] := (P₀ γ).map (algebraMap 𝒪 C)
  set Qd : (RatFunc C)[X] := minpoly (RatFunc C) θ - PC.map (algebraMap C (RatFunc C))
  have hθ := valuation_theta_le h v
  have hQd : ∀ k, gauss1 C (Qd.coeff k) < 1 := fun k ↦ by
    convert h.coeff k using 3
    simp [Qd, PC, P₀, coeff_map]
  have hsplit : aeval θ (minpoly (RatFunc C) θ) = aeval θ PC + aeval θ Qd := by
    rw [← aeval_map_algebraMap (RatFunc C) θ PC, ← map_add]
    congr 1
    ring
  have hP : aeval θ (minpoly (RatFunc C) θ) = 0 := minpoly.aeval (RatFunc C) θ
  have hlt := valuation_aeval_lt_one v hθ hQd
  have hPC : v.1 (aeval θ PC) < 1 := by
    have : aeval θ PC = -aeval θ Qd := by linear_combination hP - hsplit
    rw [this, Valuation.map_neg]
    exact hlt
  have hred : red C (aeval θ PC) v = 0 := (red_eq_zero_iff hPC.le).2 hPC
  rw [red_aeval_of_le hθ, P₀_map_residue, aeval_def, eval₂_finsetProd] at hred
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hred
  refine ⟨i, ?_⟩
  simpa [sub_eq_zero] using hi

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G] [IsUltrametricDist C] in
/-- The norm of `θ - γ` is a power of `± P(γ)`, `P` the minimal polynomial. -/
lemma norm_sub_eq (b : C) : ∃ m : ℕ, 0 < m ∧
    Algebra.norm (RatFunc C) (θ - algebraMap (RatFunc C) G (algebraMap C (RatFunc C) b)) =
      ((-1) ^ (minpoly (RatFunc C) θ).natDegree *
        (minpoly (RatFunc C) θ).eval (algebraMap C (RatFunc C) b)) ^ m := by
  set x := θ - algebraMap (RatFunc C) G (algebraMap C (RatFunc C) b)
  have hx : IsIntegral (RatFunc C) x := Algebra.IsIntegral.isIntegral x
  refine ⟨Module.finrank (RatFunc C)⟮x⟯ G, Module.finrank_pos, ?_⟩
  rw [Algebra.norm_eq_norm_adjoin (RatFunc C) x, ← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
    IntermediateField.minpoly_gen, minpoly.sub_algebraMap, coeff_zero_eq_eval_zero, eval_comp,
    IntermediateField.adjoin.powerBasis_dim, minpoly.sub_algebraMap, natDegree_comp]
  simp

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
  in
/-- `P(γⱼ)` has Gauss value `< 1`. -/
lemma gauss1_eval_lt_one (h : SplitDatum C G θ γ) (j : Fin n) :
    gauss1 C ((minpoly (RatFunc C) θ).eval (algebraMap C (RatFunc C) (γ j))) < 1 := by
  set PC : C[X] := (P₀ γ).map (algebraMap 𝒪 C)
  set Qd : (RatFunc C)[X] := minpoly (RatFunc C) θ - PC.map (algebraMap C (RatFunc C))
  have hQd : ∀ k, gauss1 C (Qd.coeff k) < 1 := fun k ↦ by
    convert h.coeff k using 3
    simp [Qd, PC, P₀, coeff_map]
  have h0 : PC.eval (γ j : C) = 0 := by
    simp only [PC, P₀, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, eval_prod,
      eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  have hsplit : minpoly (RatFunc C) θ = PC.map (algebraMap C (RatFunc C)) + Qd := by
    simp [Qd]
  rw [hsplit, eval_add, eval_map, eval₂_at_apply, h0, map_zero, zero_add]
  rw [eval_eq_sum_range]
  refine Valuation.map_sum_lt _ one_ne_zero fun k _ ↦ ?_
  rw [map_mul, map_pow, gauss1_algebraMap_C]
  have hγ : ‖((γ j : 𝒪) : C)‖₊ ≤ 1 := by
    exact_mod_cast (HenselComplete.mem_integers_iff _).1 (γ j).2
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hQd k) (pow_le_one₀ zero_le hγ)

section Count

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
  [CharZero C] in
lemma valuation_const_le (v : Ext C G) (b : 𝒪) :
    v.1 (algebraMap (RatFunc C) G (algebraMap C (RatFunc C) (b : C))) ≤ 1 := by
  rw [valuation_algebraMap_C]
  exact_mod_cast (HenselComplete.mem_integers_iff _).1 b.2

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] [CharZero C] in
lemma red_const (v : Ext C G) (b : 𝒪) :
    red C (algebraMap (RatFunc C) G (algebraMap C (RatFunc C) (b : C))) v =
      algebraMap 𝓀 _ (residue 𝒪 b) := by
  rw [← IsScalarTower.algebraMap_apply,
    red_algebraMap_C _ (by exact_mod_cast (HenselComplete.mem_integers_iff _).1 b.2)]

include hp hp1 in
/-- **Every constant `γ̄ⱼ` is a reduction of `θ`** (norm formula). -/
lemma exists_ext_red_eq (h : SplitDatum C G θ γ) (j : Fin n) :
    ∃ v : Ext C G, red C θ v = algebraMap 𝓀 _ (residue 𝒪 (γ j)) := by
  classical
  haveI : Finite (Ext C G) := finite_ext hp hp1
  haveI : Fintype (Ext C G) := Fintype.ofFinite _
  by_contra hne
  push Not at hne
  set y := θ - algebraMap (RatFunc C) G (algebraMap C (RatFunc C) (γ j : C))
  have hv : ∀ v : Ext C G, v.1 y = 1 := by
    intro v
    have hle : v.1 y ≤ 1 := (Valuation.map_sub _ _ _).trans
      (max_le (valuation_theta_le h v) (valuation_const_le v (γ j)))
    refine le_antisymm hle (not_lt.1 fun hlt ↦ hne v ?_)
    have h0 := (red_eq_zero_iff hle).2 hlt
    rw [red_sub (valuation_theta_le h v) (valuation_const_le v (γ j)), red_const,
      sub_eq_zero] at h0
    exact h0
  have hnorm := gaussRat_norm_eq_prod hp hp1 (a := (0 : C)) (r := 1) (c := (1 : C))
    (by simp) (F' := G) y
  simp only [hv, one_pow, Finset.prod_const_one] at hnorm
  obtain ⟨m, hm, hN⟩ := norm_sub_eq (θ := θ) (γ j : C)
  have hlt := gauss1_eval_lt_one h j
  change gauss1 C _ = 1 at hnorm
  rw [hN, map_pow, map_mul, map_pow, Valuation.map_neg, Valuation.map_one, one_pow,
    one_mul] at hnorm
  exact absurd hnorm (pow_lt_one₀ zero_le hlt hm.ne').ne

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] [CharZero C] in
lemma red_xF_notMem (v : Ext C G) :
    red C (xF C G) v ∉ (algebraMap 𝓀 (ResidueField v.1.valuationSubring)).range := by
  rintro ⟨c, hc⟩
  exact transcendental_red_x v (hc ▸ isAlgebraic_algebraMap c)

omit [CharZero C] in
/-- A curve whose coordinate has degree one has exactly one zero, of order one. -/
lemma exists_zeros_eq (v : Ext C G) (hf : inertiaDeg (gauss1 C) v.1 = 1) :
    ∃ Q, zeros 𝓀 (red C (xF C G) v) = {Q} ∧ ord (red C (xF C G) v) Q = 1 := by
  have hs := sum_ord (k := 𝓀) (red_xF_notMem v)
  rw [finrank_adjoin_red_x, hf] at hs
  have hne : (zeros 𝓀 (red C (xF C G) v)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h0
    rw [h0, Finset.sum_empty] at hs
    exact zero_ne_one hs
  obtain ⟨Q, hQ⟩ := hne
  have hle : ∀ R ∈ zeros 𝓀 (red C (xF C G) v), 1 ≤ ord (red C (xF C G) v) R :=
    fun R hR ↦ one_le_ord hR
  have hcard : (zeros 𝓀 (red C (xF C G) v)).card ≤ 1 := by
    calc (zeros 𝓀 (red C (xF C G) v)).card = ∑ _R ∈ zeros 𝓀 (red C (xF C G) v), 1 := by simp
      _ ≤ ∑ R ∈ zeros 𝓀 (red C (xF C G) v), ord (red C (xF C G) v) R := Finset.sum_le_sum hle
      _ = 1 := hs
  have hQs : zeros 𝓀 (red C (xF C G) v) = {Q} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨hQ, fun R hR ↦
      Finset.card_le_one.1 hcard R hR Q hQ⟩
  refine ⟨Q, hQs, ?_⟩
  rw [hQs, Finset.sum_singleton] at hs
  exact hs

include hp hp1 in
/-- **Counting**: every extension has `f = 1`, and `v ↦ (index of red θ)` is a bijection. -/
lemma count (h : SplitDatum C G θ γ) :
    (∀ v : Ext C G, inertiaDeg (gauss1 C) v.1 = 1) ∧
      ∃ ι : Ext C G ≃ Fin n,
        ∀ v, red C θ v = algebraMap 𝓀 _ (residue 𝒪 (γ (ι v))) := by
  classical
  haveI : Finite (Ext C G) := finite_ext hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  choose ι hι using exists_red_eq h
  have hres_inj : ∀ i j, residue 𝒪 (γ i) = residue 𝒪 (γ j) → i = j := fun i j hij ↦ by
    by_contra hne
    exact h.sep i j hne hij
  have hsurj : Function.Surjective ι := by
    intro j
    obtain ⟨v, hv⟩ := exists_ext_red_eq hp hp1 h j
    refine ⟨v, hres_inj _ _ ?_⟩
    have := (hι v).symm.trans hv
    exact (algebraMap 𝓀 (ResidueField v.1.valuationSubring)).injective this
  have hcard : n ≤ Fintype.card (Ext C G) := by
    simpa using Fintype.card_le_of_surjective ι hsurj
  have hsum := sum_inertiaDeg_eq hp hp1 (F := G)
  rw [← h.card] at hsum
  have hpos : ∀ v : Ext C G, 1 ≤ inertiaDeg (gauss1 C) v.1 := fun v ↦ by
    haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField v.1.valuationSubring) := finite_residueField
    exact Module.finrank_pos
  have hall : ∀ v : Ext C G, inertiaDeg (gauss1 C) v.1 = 1 := by
    have heq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun _ ↦ 1)
      (g := fun v : Ext C G ↦ inertiaDeg (gauss1 C) v.1) fun v _ ↦ hpos v).1 (by
        refine le_antisymm (Finset.sum_le_sum fun v _ ↦ hpos v) ?_
        rw [hsum]
        simpa using hcard)
    exact fun v ↦ (heq v (Finset.mem_univ v)).symm
  refine ⟨hall, Equiv.ofBijective ι ⟨?_, hsurj⟩, hι⟩
  refine (Fintype.bijective_iff_surjective_and_card ι).2 ⟨hsurj, ?_⟩ |>.1
  have : Fintype.card (Ext C G) ≤ n := by
    rw [← hsum, ← Finset.card_univ]
    calc Finset.univ.card = ∑ _v : Ext C G, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun v _ ↦ hpos v
  simpa using le_antisymm this hcard

end Count

section Points

/-- A point of the special fibre over `x̄ = 0` lies over the residue point of the chart. -/
lemma comap_placeIdealD (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G) v)) :
    (placeIdealD v hQ).comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) =
      discIdeal (0 : C) 1 := by
  haveI := placeIdealD_isMaximal v hQ
  refine ((discIdeal_isMaximal (a := (0 : C)) one_ne_zero).eq_of_le
    (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance)) ?_).symm
  rintro f ⟨Q', hQ', hQa, hQ0⟩
  rw [Ideal.mem_comap, mem_placeIdealD_iff]
  -- lift `Q'` to `O_C`
  set R : 𝒪[X] := ∑ i ∈ Finset.range (Q'.natDegree + 1),
    Polynomial.monomial i ⟨Q'.coeff i, (HenselComplete.mem_integers_iff _).2 (by
      exact_mod_cast hQ' i)⟩
  have hR : R.map (algebraMap 𝒪 C) = Q' := by
    ext i
    simp only [R, Polynomial.map_sum, Polynomial.map_monomial, finsetSum_coeff, coeff_monomial]
    by_cases hi : i < Q'.natDegree + 1
    · rw [Finset.sum_eq_single i (fun j _ hj ↦ if_neg hj)
        (fun h ↦ absurd (Finset.mem_range.2 hi) h),
        if_pos rfl]
      rfl
    · rw [Finset.sum_eq_zero fun j hj ↦ if_neg fun h : j = i ↦ hi (h ▸ Finset.mem_range.1 hj),
        coeff_eq_zero_of_natDegree_lt (by omega)]
  have hx := xbar_mem_V v hQ
  have hf : redD v (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G) f) =
      aeval (red C (xF C G) v) (R.map (residue 𝒪)) := by
    rw [redD_apply]
    change red C (algebraMap (RatFunc C) G (f : RatFunc C)) v = _
    rw [← hQa, gaussCoord_zero_one, ← hR, ← aeval_algebraMap_apply, ← red_aeval_of_le]
    · rw [xF, valuation_algebraMap, gauss1_X]
  rw [hf]
  -- the constant term vanishes
  have h0 : (R.map (residue 𝒪)).coeff 0 = 0 := by
    rw [coeff_map, residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
    have : (R.coeff 0 : C) = Q'.coeff 0 := by rw [← hR, coeff_map]; rfl
    rw [this]
    exact_mod_cast hQ0
  have hdecomp : R.map (residue 𝒪) = X * (R.map (residue 𝒪)).divX := by
    conv_lhs => rw [← divX_mul_X_add (R.map (residue 𝒪)), h0, map_zero, add_zero]
    ring
  rw [hdecomp, map_mul, aeval_X]
  have hmem : aeval (red C (xF C G) v) (R.map (residue 𝒪)).divX ∈ Q.V := by
    rw [aeval_def, eval₂_eq_sum_range]
    exact Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (Q.algebraMap_mem _)
      (Subring.pow_mem _ hx _)
  rw [Q.res_mul hx hmem, Q.res_eq_zero_of_lt_one (valuation_x_lt_one hQ), zero_mul]

/-- The disc valuation `w_{0,1/2}`. -/
noncomputable def νhalf : DiscVal (0 : C) 1 where
  val := gaussRat (NormedField.valuation (K := C)) 0 (Units.mk0 (1 / 2) (by norm_num))
  isDiscVal := ⟨fun c ↦ by rw [gaussRat_algebraMap_C, NormedField.valuation_apply], by
    rw [SmoothVertex.gaussCoord_zero_one, AnnulusUnit.gaussRat_X]
    change (1 / 2 : ℝ≥0) < 1
    norm_num⟩

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G] in
/-- There are at most `[G : C(x)]` local factors. -/
lemma card_factor_le [Algebra.IsSeparable (RatFunc C) G] :
    Fintype.card (LocalGlobal.Factor (DiscField (νhalf (C := C)))
      (UniformSpace.Completion (DiscField (νhalf (C := C)))) G) ≤
      Module.finrank (RatFunc C) G := by
  classical
  have hsum := LocalGlobal.sum_natDegree_factors (F := DiscField (νhalf (C := C)))
    (K := UniformSpace.Completion (DiscField (νhalf (C := C)))) (F' := G)
  have hdeg : Module.finrank (DiscField (νhalf (C := C))) G = Module.finrank (RatFunc C) G :=
    Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv _) (RingEquiv.refl G) (by ext; rfl)
  rw [hdeg] at hsum
  rw [Fintype.card_coe, ← hsum]
  calc _ = ∑ _g ∈ LocalGlobal.factors (DiscField (νhalf (C := C)))
        (UniformSpace.Completion (DiscField (νhalf (C := C)))) G, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun g hg ↦
        (LocalGlobal.irreducible_of_mem_factors hg).natDegree_pos

end Points

section Main

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Smoothness over the residue disc of an unramified split cover**: every point of
`DRint 0 1 G` over the residue point `x̄ = 0` is smooth. -/
theorem isDiscSmooth_of_splitDatum (h : SplitDatum C G θ γ) (P' : Ideal (DRint (0 : C) 1 G))
    [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) = discIdeal (0 : C) 1) :
    IsDiscSmooth P' := by
  classical
  haveI : Finite (Ext C G) := finite_ext hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  obtain ⟨hall, ι, hι⟩ := count hp hp1 h
  choose Q hQ using fun v ↦ exists_zeros_eq v (hall v)
  have hQm : ∀ v, Q v ∈ zeros 𝓀 (red C (xF C G) v) := fun v ↦ by
    rw [(hQ v).1]; exact Finset.mem_singleton_self _
  let θD : DRint (0 : C) 1 G := ⟨θ, h.integral⟩
  let y : Fin n → DRint (0 : C) 1 G := fun i ↦ θD - constD (γ i)
  have hredy : ∀ v i, redD v (y i) = algebraMap 𝓀 _ (residue 𝒪 (γ (ι v))) -
      algebraMap 𝓀 _ (residue 𝒪 (γ i)) := by
    intro v i
    simp only [y, map_sub, redD_constD]
    rw [redD_apply]
    exact congrArg (· - _) (hι v)
  set Pt : Ext C G → Ideal (DRint (0 : C) 1 G) := fun v ↦ placeIdealD v (hQm v) with hPt
  have hmem : ∀ v, y (ι v) ∈ Pt v := fun v ↦ by
    rw [hPt, mem_placeIdealD_iff, hredy, sub_self, (Q v).res_zero]
  have hnot : ∀ v v', v ≠ v' → y (ι v) ∉ Pt v' := fun v v' hne hm ↦ by
    rw [hPt, mem_placeIdealD_iff, hredy, ← map_sub, (Q v').res_algebraMap, sub_eq_zero] at hm
    exact h.sep _ _ (fun e ↦ hne (ι.injective e).symm) hm
  have hinj : ∀ v v', Pt v = Pt v' → v = v' := fun v v' he ↦ by
    by_contra hne
    exact hnot v v' hne (he ▸ hmem v)
  -- every point over the residue point is a centre of a local factor
  have hcen : ∀ P₁ : Ideal (DRint (0 : C) 1 G), P₁.IsMaximal →
      P₁.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) = discIdeal (0 : C) 1 →
      P₁ ∈ Finset.univ.image fun g : LocalGlobal.Factor (DiscField (νhalf (C := C)))
        (UniformSpace.Completion (DiscField (νhalf (C := C)))) G ↦
          DiscCount.center (isDiscVal_comap_extValuation g) := by
    intro P₁ hP₁ hc
    have hpos := discDegree_pos (a := (0 : C)) one_ne_zero νhalf P₁ hc
    rw [discDegree, Finset.sum_pos_iff] at hpos
    obtain ⟨g, hg, -⟩ := hpos
    exact Finset.mem_image.2 ⟨g, Finset.mem_univ _, (Finset.mem_filter.1 hg).2⟩
  obtain ⟨v, rfl⟩ : ∃ v, Pt v = P' := by
    by_contra hno
    push Not at hno
    set T := insert P' (Finset.univ.image Pt)
    have hT : T ⊆ Finset.univ.image fun g : LocalGlobal.Factor (DiscField (νhalf (C := C)))
        (UniformSpace.Completion (DiscField (νhalf (C := C)))) G ↦
          DiscCount.center (isDiscVal_comap_extValuation g) := by
      intro P₁ hP₁
      rcases Finset.mem_insert.1 hP₁ with rfl | hP₁
      · exact hcen P₁ inferInstance hP'
      · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hP₁
        exact hcen _ (placeIdealD_isMaximal v (hQm v)) (comap_placeIdealD v (hQm v))
    have hcardT : T.card = n + 1 := by
      rw [Finset.card_insert_of_notMem (fun hm ↦ by
        obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hm
        exact hno v hv), Finset.card_image_of_injective _ fun v v' ↦ hinj v v',
        Finset.card_univ, Fintype.card_congr ι, Fintype.card_fin]
    have := (Finset.card_le_card hT).trans Finset.card_image_le
    rw [hcardT, Finset.card_univ] at this
    have := this.trans (card_factor_le (C := C) (G := G))
    rw [← h.card] at this
    omega
  -- the smooth point
  refine ⟨⟨v, Q v, hQm v⟩, ?_, fun α hα ↦ ?_⟩
  · ext ⟨v', R, hR⟩
    rw [Set.mem_singleton_iff]
    constructor
    · intro hb
      have hRQ : R = Q v' := by
        have := hR
        rw [(hQ v').1, Finset.mem_singleton] at this
        exact this
      subst hRQ
      have hvv : v' = v := hinj v' v hb
      subst hvv
      rfl
    · intro hb
      cases hb
      rfl
  · have hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C G) v)), R ≠ Q v →
        placeIdealD v hR ≠ placeIdealD v (hQm v) := fun R hR hne ↦ by
      rw [(hQ v).1, Finset.mem_singleton] at hR
      exact absurd hR hne
    have ht : (Q v).valuation (redD v (xD (F' := G))) = exp (-1) := by
      rw [redD_xD, valuation_x (hQm v), (hQ v).2]
      rfl
    exact SmoothVertex.exists_eq_of_uniformizer hp hp1 v (hQm v) hoth ht hα

end Main

end ClassicalSmooth

end SemistableReduction
