/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TubeSkeleton
import TemperedFundamentalGroups.SemistableReduction.KummerSheet
import TemperedFundamentalGroups.SemistableReduction.KummerBase

/-!
# A coordinate at a smooth disc point

Blueprint §9.12, O11 (D⇒), lemma (L), first part. Let `G / C(x)` be finite and `P'` a point of
the normalized disc chart `R' = DRint 0 1 G` over `(𝔪_C, x)`. For `s ∈ R'` the element
`u = s + xᵐ` (`m` larger than the `x`-degrees of an integral equation of `s` over `O_C[x]`) makes
`x` integral over `O_C[u]`, so that `R'` lies in the normalized disc chart `R'_u` of the coordinate
`u` (`ClassicalSmooth.Coord`).

* `isIntegral_of_sub_pow`, `exists_integral_eq`, `isIntegral_xF_coord`: the integrality of `x`;
* `isIntegral_coord`, `incl`: `R' ⊆ R'_u`;
* `valuation_red_coord`: `u` still reduces to a uniformizer at a zero `Q` of `x̄` if `s` does;
* `comap_eq_gauss1_of_sub`, `valuation_sub_eq_one`: a criterion for the Gauss point;
* `psi`, `branch_of_ker`: the reduction of `R'` at a branch of `u`; a branch of `u` whose point is
  a point `P'` of `R'` (containing `x` and `u`) is a branch of `x` through `P'`.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace SmoothDisc

open FundamentalInequality GaussStability GaussFibre PlaceNorm GaussTube DiscCount SmoothVertex
  ClassicalSmooth TubeCount

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- If `(U - xᵐ)ᴺ + Σ_{i<N} gᵢ(x) (U - xᵐ)ⁱ = 0` with `deg gᵢ ≤ D < m`, then `x` is integral. -/
theorem isIntegral_of_sub_pow {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {x : A} (U : R) {m N D : ℕ} (hm : D < m) (g : ℕ → R[X]) (hg : ∀ i < N, (g i).natDegree ≤ D)
    (h : (algebraMap R A U - x ^ m) ^ N +
      ∑ i ∈ Finset.range N, aeval x (g i) * (algebraMap R A U - x ^ m) ^ i = 0) :
    IsIntegral R x := by
  classical
  nontriviality R
  set L : R[X] := X ^ m - Polynomial.C U
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
  have hLm : L.Monic := monic_X_pow_sub_C U hm0.ne'
  have hLdeg : L.natDegree = m := natDegree_X_pow_sub_C
  set q : R[X] := ∑ i ∈ Finset.range N, Polynomial.C ((-1) ^ N * (-1) ^ i) * g i * L ^ i
  have hq : q.degree < (L ^ N).degree := by
    rw [degree_eq_natDegree (hLm.pow N).ne_zero, hLm.natDegree_pow, hLdeg]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add (degree_mul_le _ _) (degree_pow_le _ _)) ?_
    refine lt_of_le_of_lt (add_le_add (add_le_add degree_C_le (degree_le_natDegree)) le_rfl) ?_
    rw [degree_eq_natDegree hLm.ne_zero, hLdeg]
    have : (g i).natDegree + i * m < N * m := by
      have := hg i hi'
      calc (g i).natDegree + i * m ≤ D + i * m := by omega
        _ < m + i * m := by omega
        _ = (i + 1) * m := by ring
        _ ≤ N * m := Nat.mul_le_mul_right _ hi'
    have h2 : ((0 : WithBot ℕ) + ((g i).natDegree : WithBot ℕ)) + (i • (m : WithBot ℕ)) =
        (((g i).natDegree + i * m : ℕ) : WithBot ℕ) := by
      simp [nsmul_eq_mul]
    rw [h2]
    exact_mod_cast this
  refine ⟨L ^ N + q, (hLm.pow N).add_of_left hq, ?_⟩
  have hL : aeval x L = -(algebraMap R A U - x ^ m) := by
    simp [L]
  have key : aeval x (L ^ N + q) = (-1) ^ N * ((algebraMap R A U - x ^ m) ^ N +
      ∑ i ∈ Finset.range N, aeval x (g i) * (algebraMap R A U - x ^ m) ^ i) := by
    simp only [q, map_add, map_pow, map_sum, map_mul, aeval_C, hL, mul_add, Finset.mul_sum]
    congr 1
    · rw [neg_pow, mul_comm]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [neg_pow]
      simp only [map_neg, map_one]
      rw [show ((-1 : A) ^ N * (-1) ^ i * aeval x (g i) *
          ((-1) ^ i * (algebraMap R A U - x ^ m) ^ i)) = (-1) ^ N * aeval x (g i) *
            (((-1) ^ i * (-1) ^ i) * (algebraMap R A U - x ^ m) ^ i) by ring,
        ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul, mul_assoc]
  rw [← aeval_def, key, h, mul_zero]


omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
/-- Degree bound for the coefficients of an integral equation over the vertex chart. -/
lemma exists_integral_eq (y : DRint (0 : C) 1 G) :
    ∃ (N D : ℕ) (A : ℕ → C[X]), (∀ i j, ‖(A i).coeff j‖ ≤ 1) ∧ (∀ i < N, (A i).natDegree ≤ D) ∧
      (y : G) ^ N + ∑ i ∈ Finset.range N, aeval (xF C G) (A i) * (y : G) ^ i = 0 := by
  classical
  obtain ⟨f, hfm, hf⟩ := y.2
  have hc : ∀ i, ∃ A : C[X], (∀ j, ‖A.coeff j‖ ≤ 1) ∧
      algebraMap C[X] (RatFunc C) A = (f.coeff i : RatFunc C) := fun i ↦ by
    obtain ⟨A, hA, hAf⟩ := mem_discRing_iff.1 (f.coeff i).2
    exact ⟨A, fun j ↦ by exact_mod_cast nnnorm_coeff_le_one hA j, hAf⟩
  choose A hA1 hAf using hc
  refine ⟨f.natDegree, (Finset.range f.natDegree).sup fun i ↦ (A i).natDegree, A, hA1,
    fun i hi ↦ Finset.le_sup (f := fun i ↦ (A i).natDegree) (Finset.mem_range.2 hi), ?_⟩
  have h := hf
  rw [hfm.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at h
  rw [← h]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval₂_mul, eval₂_C, eval₂_X_pow, aeval_xF, hAf]
  rfl

/-- An element whose reduction has valuation `exp (-1)` at a place of a residue curve is
transcendental over `C`. -/
lemma transcendental_of_red (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {f : G} (hf : Q.valuation (red C f v) = exp (-1)) : Transcendental C f := by
  refine transcendental_of_notMem_range fun ⟨c, hc⟩ ↦ ?_
  subst hc
  by_cases hc1 : ‖c‖₊ ≤ 1
  · rw [red_algebraMap_C c hc1] at hf
    by_cases h0 : residue (HenselComplete.integers C) ⟨c, by simpa using hc1⟩ = 0
    · rw [h0, map_zero, map_zero] at hf
      exact exp_ne_zero hf.symm
    · rw [valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one h0] at hf
      have : (exp (-1) : ℤᵐ⁰) < 1 := by rw [← exp_zero, exp_lt_exp]; norm_num
      exact this.ne' hf
  · rw [red, dif_neg (by rwa [valuation_algebraMap_C']), map_zero] at hf
    exact exp_ne_zero hf.symm

/-- The coordinate `u = t + xᵐ`: its reduction at a zero `Q` of `x̄` still has order one. -/
lemma valuation_red_coord (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G) v)) {t : G} (ht1 : v.1 t ≤ 1)
    (ht : Q.valuation (red C t v) = exp (-1)) {m : ℕ} (hm : 2 ≤ m) :
    Q.valuation (red C (t + xF C G ^ m) v) = exp (-1) := by
  have hx1 : v.1 (xF C G) ≤ 1 := (valuation_xF v).le
  rw [red_add ht1 (by rw [map_pow]; exact pow_le_one' hx1 m), red_pow hx1]
  refine (Valuation.map_add_eq_of_lt_left _ ?_).trans ht
  rw [ht, map_pow, valuation_x hQ, ← exp_nsmul, exp_lt_exp]
  have := one_le_ord hQ
  simp only [smul_neg, nsmul_eq_mul]
  nlinarith

/-! ### A criterion for the Gauss point -/

omit [IsAlgClosed C] in
/-- A valuation of `F` extending the norm of `C`, with `w(x) ≤ 1` and `w(x - β) = 1` for every
`|β| ≤ 1`, lies over the Gauss point `w_{0,1}`. -/
lemma comap_eq_gauss1_of_sub [IsAlgClosed C] {F : Type*} [Field F] [Algebra (RatFunc C) F]
    [Algebra C F] [IsScalarTower C (RatFunc C) F] (w : Valuation F ℝ≥0)
    (hC : ∀ c : C, w (algebraMap C F c) = ‖c‖₊) (hx : w (xF C F) ≤ 1)
    (h1 : ∀ β : C, ‖β‖ ≤ 1 → w (xF C F - algebraMap C F β) = 1) :
    w.comap (algebraMap (RatFunc C) F) = gauss1 C := by
  refine valuation_ratFunc_ext_of_linear (fun e ↦ ?_) fun β ↦ ?_
  · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, hC, gauss1_algebraMap_C]
  · have hX : algebraMap (RatFunc C) F (algebraMap C[X] (RatFunc C) (X - Polynomial.C β)) =
        xF C F - algebraMap C F β := by
      rw [← aeval_xF, _root_.map_sub, aeval_X, aeval_C]
    rw [Valuation.comap_apply, hX, gaussRat_algebraMap, gauss_X_sub_C, zero_sub,
      Valuation.map_neg, NormedField.valuation_apply, Units.val_one]
    rcases le_or_gt ‖β‖ 1 with hβ | hβ
    · rw [h1 β hβ, max_eq_right (by exact_mod_cast hβ)]
    · have hβ' : (1 : ℝ≥0) < ‖β‖₊ := by exact_mod_cast hβ
      rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hC]; exact hx.trans_lt hβ'), hC,
        max_eq_left hβ'.le]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
/-- If the reduction of `f` at `v` is not a constant, `v(f - β) = 1` for all `|β| ≤ 1`. -/
lemma valuation_sub_eq_one (v : Ext C G) {f : G} (hf : v.1 f ≤ 1)
    (hr : red C f v ∉ (algebraMap 𝓀 (ResidueField v.1.valuationSubring)).range) {β : C}
    (hβ : ‖β‖ ≤ 1) : v.1 (f - algebraMap C G β) = 1 := by
  have hβ' : v.1 (algebraMap C G β) ≤ 1 := by
    rw [valuation_algebraMap_C']; exact_mod_cast hβ
  have hle : v.1 (f - algebraMap C G β) ≤ 1 := (Valuation.map_sub _ _ _).trans (max_le hf hβ')
  refine le_antisymm hle (not_lt.1 fun hlt ↦ hr ?_)
  have h0 := (red_eq_zero_iff hle).2 hlt
  rw [red_sub hf hβ', red_algebraMap_C β (by exact_mod_cast hβ), sub_eq_zero] at h0
  exact ⟨_, h0.symm⟩

/-! ### The coordinate `u` -/

section Coord

variable {u : G} (hu : Transcendental C u)

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) G]
  [Algebra (RatFunc C) G] [IsScalarTower C (RatFunc C) G] in
lemma xF_coord' : xF C (Coord hu) = toCoord hu u := by
  change coordAlgHom hu RatFunc.X = u
  exact coordAlgHom_X hu

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma finiteDimensional_coord : FiniteDimensional (RatFunc C) (Coord hu) := by
  haveI : IsCurveFunctionField C (Coord hu) :=
    (GaussFibre.isCurveFunctionField_F : IsCurveFunctionField C G)
  refine finiteDimensional_of_transcendental ?_
  rw [xF_coord']
  exact hu

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] [IsScalarTower C (RatFunc C) G] in
lemma aeval_coord (A : C[X]) (hA : ∀ j, ‖A.coeff j‖ ≤ 1) :
    ∃ g : (discRing (0 : C) 1)[X], g.natDegree ≤ A.natDegree ∧
      aeval (toCoord hu (xF C G)) g = toCoord hu (aeval (xF C G) A) := by
  have hco : ((A.map (algebraMap C (RatFunc C))).coeffs : Set (RatFunc C)) ⊆
      ((discRing (0 : C) 1) : Set _) := by
    intro f hf
    obtain ⟨j, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hf
    rw [coeff_map]
    exact algebraMap_mem_discRing (by exact_mod_cast hA j)
  refine ⟨_, (natDegree_toSubring _ _ hco).le.trans (natDegree_map_le), ?_⟩
  have h1 : algebraMap (discRing (0 : C) 1) (Coord hu) =
      (algebraMap (RatFunc C) (Coord hu)).comp (discRing (0 : C) 1).subtype := rfl
  rw [aeval_def, h1, ← eval₂_map, map_toSubring, eval₂_map,
    ← IsScalarTower.algebraMap_eq]
  rfl

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] [IsScalarTower C (RatFunc C) G] in
/-- **`x` is integral over `O_C[u]`** for `u = t + xᵐ`, `m` larger than the `x`-degrees of an
integral equation of `t` over `O_C[x]`. -/
lemma isIntegral_xF_coord {t : G} {N D : ℕ} {A : ℕ → C[X]} (hA1 : ∀ i j, ‖(A i).coeff j‖ ≤ 1)
    (hAD : ∀ i < N, (A i).natDegree ≤ D)
    (heq : t ^ N + ∑ i ∈ Finset.range N, aeval (xF C G) (A i) * t ^ i = 0) {m : ℕ} (hm : D < m)
    (hu : Transcendental C (t + xF C G ^ m)) :
    IsIntegral (discRing (0 : C) 1) (toCoord hu (xF C G)) := by
  choose g hgd hg using fun i ↦ aeval_coord hu (A i) (hA1 i)
  refine isIntegral_of_sub_pow ⟨RatFunc.X, X_mem_discRing⟩ hm g
    (fun i hi ↦ (hgd i).trans (hAD i hi)) ?_
  have hU : algebraMap (discRing (0 : C) 1) (Coord hu) ⟨RatFunc.X, X_mem_discRing⟩ =
      toCoord hu (t + xF C G ^ m) := xF_coord' hu
  simp only [hU, hg]
  have h2 : toCoord hu (t + xF C G ^ m) - toCoord hu (xF C G) ^ m = toCoord hu t := by
    rw [map_add, map_pow, add_sub_cancel_right]
  rw [h2]
  simpa only [map_add, map_pow, map_mul, map_sum, map_zero] using congrArg (toCoord hu) heq

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
/-- Functions of the chart `O_C[x]` lie in the chart `R'_u` once `x` does. -/
lemma mem_drint_coord (hx : IsIntegral (discRing (0 : C) 1) (toCoord hu (xF C G)))
    (f : discRing (0 : C) 1) :
    toCoord hu (algebraMap (RatFunc C) G f) ∈ DRint (0 : C) 1 (Coord hu) := by
  obtain ⟨B, hB, hBf⟩ := mem_discRing_iff.1 f.2
  obtain ⟨g, -, hg⟩ := aeval_coord hu B fun j ↦ by exact_mod_cast nnnorm_coeff_le_one hB j
  rw [← hBf, ← aeval_xF, ← hg]
  exact adjoin_le_integralClosure hx (Polynomial.aeval_mem_adjoin_singleton _ _)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
/-- **`R' ⊆ R'_u`**: elements integral over `O_C[x]` are integral over `O_C[u]`. -/
lemma isIntegral_coord (hx : IsIntegral (discRing (0 : C) 1) (toCoord hu (xF C G)))
    (y : DRint (0 : C) 1 G) : IsIntegral (discRing (0 : C) 1) (toCoord hu (y : G)) := by
  let φ : discRing (0 : C) 1 →+* DRint (0 : C) 1 (Coord hu) :=
    RingHom.codRestrict ((toCoord hu).toRingHom.comp
      ((algebraMap (RatFunc C) G).comp (discRing (0 : C) 1).subtype))
      (DRint (0 : C) 1 (Coord hu)) fun f ↦ mem_drint_coord hu hx f
  obtain ⟨p, hpm, hp⟩ := y.2
  have hint : IsIntegral (DRint (0 : C) 1 (Coord hu)) (toCoord hu (y : G)) := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [eval₂_map]
    have : (algebraMap (DRint (0 : C) 1 (Coord hu)) (Coord hu)).comp φ =
        (toCoord hu).toRingHom.comp (algebraMap (discRing (0 : C) 1) G) := rfl
    rw [this]
    have h2 := hom_eval₂ p (algebraMap (discRing (0 : C) 1) G) (toCoord hu).toRingHom (y : G)
    rw [hp, map_zero] at h2
    exact h2.symm
  exact isIntegral_trans _ hint

end Coord

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
lemma mem_zeros_iff_lt_one {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
    [IsCurveFunctionField k κ] (P : CurvePlace k κ) {f : κ} (hf : f ≠ 0) :
    P ∈ zeros k f ↔ P.valuation f < 1 := by
  have h0 : P.valuation f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  rw [mem_zeros, ← P.valuation_le_one_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (pos_iff_ne_zero.2 h0)

/-! ### The count in the coordinate `u` -/

section Count

variable {u : G} (hu : Transcendental C u)
  (hx : IsIntegral (discRing (0 : C) 1) (toCoord hu (xF C G)))

/-- The inclusion `R' ⊆ R'_u`. -/
noncomputable def incl : DRint (0 : C) 1 G →+* DRint (0 : C) 1 (Coord hu) :=
  RingHom.codRestrict ((toCoord hu).toRingHom.comp (DRint (0 : C) 1 G).val.toRingHom)
    (DRint (0 : C) 1 (Coord hu)) fun y ↦ isIntegral_coord hu hx y

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
lemma coe_incl (y : DRint (0 : C) 1 G) : (incl hu hx y : Coord hu) = toCoord hu (y : G) := rfl

variable [FiniteDimensional (RatFunc C) (Coord hu)]

/-- The reduction of `R'` at a branch `(v'', Q'')` of the coordinate `u`. -/
noncomputable def psi (v'' : Ext C (Coord hu))
    {Q'' : CurvePlace 𝓀 (ResidueField v''.1.valuationSubring)}
    (hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v'')) : DRint (0 : C) 1 G →+* 𝓀 :=
  (placeHomD v'' hQ'').comp (incl hu hx)

omit [FiniteDimensional (RatFunc C) G] in
lemma psi_apply (v'' : Ext C (Coord hu))
    {Q'' : CurvePlace 𝓀 (ResidueField v''.1.valuationSubring)}
    (hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v'')) (y : DRint (0 : C) 1 G) :
    psi hu hx v'' hQ'' y = Q''.res (red C (toCoord hu (y : G)) v'') := rfl

omit [FiniteDimensional (RatFunc C) G] in
lemma psi_surjective (v'' : Ext C (Coord hu))
    {Q'' : CurvePlace 𝓀 (ResidueField v''.1.valuationSubring)}
    (hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v'')) :
    Function.Surjective (psi hu hx v'' hQ'') := by
  intro k
  obtain ⟨κ, rfl⟩ := residue_surjective k
  refine ⟨constD κ, ?_⟩
  have h : incl hu hx (constD κ) = constD κ := Subtype.ext <| by
    rw [coe_incl]
    change algebraMap (RatFunc C) G (algebraMap C (RatFunc C) κ) =
      coordAlgHom hu (algebraMap C (RatFunc C) κ)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  change placeHomD v'' hQ'' (incl hu hx (constD κ)) = _
  rw [h]
  change Q''.res (redD v'' (constD κ)) = _
  rw [redD_constD, Q''.res_algebraMap]

omit [FiniteDimensional (RatFunc C) G] in
lemma ker_psi_isMaximal (v'' : Ext C (Coord hu))
    {Q'' : CurvePlace 𝓀 (ResidueField v''.1.valuationSubring)}
    (hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v'')) :
    (RingHom.ker (psi hu hx v'' hQ'')).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (psi_surjective hu hx v'' hQ'')

/-- **A branch of `u` through the point `P'` is a branch of `x`.** If the kernel of the
reduction at a zero `Q''` of `ū` on `κ(v'')` is the point `P' = placeIdealD v Q` (which contains
`x` and `u`), then `v''` lies over the Gauss point of `x`, `Q''` is a zero of `x̄`, and its point
is `P'`. -/
lemma branch_of_ker (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G) v)) {s : DRint (0 : C) 1 G} (hsu : (s : G) = u)
    (hsP : s ∈ placeIdealD v hQ) (v'' : Ext C (Coord hu))
    {Q'' : CurvePlace 𝓀 (ResidueField v''.1.valuationSubring)}
    (hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v''))
    (hker : RingHom.ker (psi hu hx v'' hQ'') = placeIdealD v hQ) :
    ∃ hv : (v''.1 : Valuation G ℝ≥0).comap (algebraMap (RatFunc C) G) = gauss1 C,
      ∃ hQG : Q'' ∈ zeros 𝓀 (red C (xF C G) ⟨v''.1, hv⟩),
        placeIdealD (⟨v''.1, hv⟩ : Ext C G) hQG = placeIdealD v hQ := by
  set xH : DRint (0 : C) 1 (Coord hu) := ⟨toCoord hu (xF C G), hx⟩
  have hxle : v''.1 (toCoord hu (xF C G)) ≤ 1 := valuation_le_one_D v'' xH
  have hxP : (xD : DRint (0 : C) 1 G) ∈ placeIdealD v hQ := by
    rw [mem_placeIdealD_iff, redD_xD]
    exact Q.res_eq_zero_of_lt_one (valuation_x_lt_one hQ)
  have hres : Q''.res (red C (toCoord hu (xF C G)) v'') = 0 := by
    rw [← hker] at hxP
    exact hxP
  have hmemV : red C (toCoord hu (xF C G)) v'' ∈ Q''.V :=
    redD_mem_V v'' xH (xbar_mem_V v'' hQ'')
  have hC : ∀ c : C, (v''.1 : Valuation G ℝ≥0) (algebraMap C G c) = ‖c‖₊ :=
    valuation_algebraMap_C' v''
  by_cases hr : red C (toCoord hu (xF C G)) v'' ∈
      (algebraMap 𝓀 (ResidueField v''.1.valuationSubring)).range
  · -- the reduction of `x` is constant, hence `0`: `v''` lies in the open disc of `x`
    exfalso
    obtain ⟨k₀, hk₀⟩ := hr
    rw [← hk₀, Q''.res_algebraMap] at hres
    rw [hres, map_zero] at hk₀
    have hxlt : v''.1 (toCoord hu (xF C G)) < 1 := (red_eq_zero_iff hxle).1 hk₀.symm
    have hd : IsDiscVal (0 : C) 1 ((v''.1 : Valuation G ℝ≥0).comap (algebraMap (RatFunc C) G)) :=
      ⟨fun c ↦ by rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]; exact hC c,
        by rw [gaussCoord_zero_one, Valuation.comap_apply]; exact hxlt⟩
    haveI := center_isMaximal one_ne_zero hd
    have hle : center hd ≤ RingHom.ker (psi hu hx v'' hQ'') := fun y hy ↦ by
      have hy' : v''.1 (toCoord hu (y : G)) < 1 := (DiscCount.mem_center_iff hd y).1 hy
      rw [RingHom.mem_ker, psi_apply, (red_eq_zero_iff hy'.le).2 hy', Q''.res_zero]
    have heq : center hd = placeIdealD v hQ := by
      rw [← hker]
      exact (inferInstance : (center hd).IsMaximal).eq_of_le
        (ker_psi_isMaximal hu hx v'' hQ'').ne_top hle
    rw [← heq, DiscCount.mem_center_iff, hsu] at hsP
    have h1 : v''.1 (xF C (Coord hu)) = 1 := valuation_xF v''
    rw [xF_coord'] at h1
    exact (lt_irrefl _) (h1 ▸ hsP)
  · have h1 : ∀ β : C, ‖β‖ ≤ 1 →
        (v''.1 : Valuation G ℝ≥0) (xF C G - algebraMap C G β) = 1 :=
      fun β hβ ↦ valuation_sub_eq_one v'' hxle hr hβ
    have hxle' : (v''.1 : Valuation G ℝ≥0) (xF C G) ≤ 1 := hxle
    have hv := comap_eq_gauss1_of_sub (F := G) (v''.1 : Valuation G ℝ≥0) hC hxle' h1
    have hr0 : red C (toCoord hu (xF C G)) v'' ≠ 0 := fun h0 ↦ hr ⟨0, by rw [h0, map_zero]⟩
    have hQG : Q'' ∈ zeros 𝓀 (red C (xF C G) ⟨v''.1, hv⟩) := by
      refine (mem_zeros_iff_lt_one Q'' hr0).2 ?_
      have := Q''.valuation_sub_res_lt_one hmemV
      rwa [hres, map_zero, sub_zero] at this
    refine ⟨hv, hQG, ?_⟩
    rw [← hker]
    ext y
    rw [mem_placeIdealD_iff, RingHom.mem_ker, psi_apply]
    rfl

end Count

end SmoothDisc

end SemistableReduction
