/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ClassicalSmooth
import TemperedFundamentalGroups.SemistableReduction.S8Transport
import TemperedFundamentalGroups.SemistableReduction.SplitDisc

/-!
# Small residue balls around an unramified classical point are good

Blueprint §9.12 O6.1f (S8.2, unramified case). An **unramified datum** at `a ∈ C`
(`UnramDatum`): `θ ∈ F` whose minimal polynomial has polynomial coefficients `q_k ∈ C[x]` with
`∏ᵢ (Y - γᵢ) = Σ q_k(a) Y^k`, `γᵢ ∈ O_C` of distinct residues. Then for `‖c‖` small the twist
`Aff a c F` carries the split datum of `ClassicalSmooth` (Taylor expansion `q_k(a + c t)`), so
every point over the open disc `|x - a| < |c|` is smooth (`discGood_of_unramDatum`).
-/

open Polynomial IsLocalRing
open scoped NNReal

namespace SemistableReduction

namespace ClassicalSmooth

open GaussFibre DiscCount SmoothVertex AffineTwist

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

local notation "𝒪" => HenselComplete.integers C

variable (C F) in
/-- **Unramified datum** at the classical point `a`. -/
structure UnramDatum (a : C) (θ : F) {n : ℕ} (γ : Fin n → HenselComplete.integers C) : Prop where
  card : n = Module.finrank (RatFunc C) F
  sep : ∀ i j, i ≠ j → residue 𝒪 (γ i) ≠ residue 𝒪 (γ j)
  poly : ∀ k, ∃ q : C[X], algebraMap C[X] (RatFunc C) q = (minpoly (RatFunc C) θ).coeff k ∧
    q.eval a = ((P₀ γ).map (algebraMap 𝒪 C)).coeff k

omit [IsAlgClosed C] in
lemma gaussSup_le_one {Q : C[X]} (h : ∀ i, ‖Q.coeff i‖ ≤ 1) :
    Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1 :=
  Finset.sup_le fun i _ ↦ by
    rw [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply]
    exact_mod_cast h i

omit [IsAlgClosed C] in
lemma gaussSup_lt_one {Q : C[X]} (h : ∀ i, ‖Q.coeff i‖ < 1) :
    Gauss.sup (NormedField.valuation (K := C)) 1 Q < 1 :=
  (Finset.sup_lt_iff (by simp)).2 fun i _ ↦ by
    rw [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply]
    exact_mod_cast h i

omit [IsAlgClosed C] in
/-- `x ↦ c x + a` on polynomials: `q(c x + a)` has the Taylor coefficients of `q` at `a`, scaled. -/
lemma aff_symm_algebraMap (a c : C) (hc : c ≠ 0) (q : C[X]) :
    (aff a c hc).symm (algebraMap C[X] (RatFunc C) q) =
      algebraMap C[X] (RatFunc C) ((taylor a q).comp (Polynomial.C c * X)) := by
  rw [aff, AlgEquiv.ofAlgHom_symm_apply, affHom_algebraMap, gaussCoord_eq]
  have hlin : algebraMap C (RatFunc C) c⁻¹⁻¹ * (RatFunc.X - algebraMap C (RatFunc C) (-a / c)) =
      algebraMap C[X] (RatFunc C) (Polynomial.C c * X + Polynomial.C a) := by
    rw [inv_inv, map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    have hc' : RatFunc.C c ≠ (0 : RatFunc C) := by simpa using hc
    simp only [← RatFunc.algebraMap_C (K := C)]
    field_simp
    simp [map_div₀]
    field_simp
  rw [hlin, aeval_algebraMap_apply, taylor_apply, comp_assoc, ← comp_eq_aeval]
  congr 2
  simp [add_comp]

variable {a : C} {θ : F} {n : ℕ} {γ : Fin n → HenselComplete.integers C}

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [IsAlgClosed C] in
/-- The minimal polynomial of `θ` in the twist `Aff a c F`. -/
lemma minpoly_toAff (c : C) (hc : c ≠ 0) :
    minpoly (RatFunc C) (toAff hc θ : Aff a c hc F) =
      (minpoly (RatFunc C) θ).map ((aff a c hc).symm : RatFunc C →+* RatFunc C) := by
  have hθ : IsIntegral (RatFunc C) θ := Algebra.IsIntegral.isIntegral θ
  symm
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ((minpoly.monic hθ).map _)
  · have := (MulEquiv.irreducible_iff
      (Polynomial.mapEquiv (aff a c hc).symm.toRingEquiv).toMulEquiv).2 (minpoly.irreducible hθ)
    exact this
  · rw [aeval_def, eval₂_map]
    have hcomp : (algebraMap (RatFunc C) (Aff a c hc F)).comp
        ((aff a c hc).symm : RatFunc C →+* RatFunc C) =
          (toAff hc).toRingHom.comp (algebraMap (RatFunc C) F) := by
      ext φ
      change toAff hc (algebraMap (RatFunc C) F (aff a c hc ((aff a c hc).symm φ))) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [hcomp]
    have := hom_eval₂ (minpoly (RatFunc C) θ) (algebraMap (RatFunc C) F)
      (toAff (a := a) hc).toRingHom θ
    exact this.symm.trans (by rw [← aeval_def, minpoly.aeval, map_zero])

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  in
/-- A uniform bound for the Taylor coefficients at `a` of the coefficients of the minimal
polynomial. -/
lemma exists_taylor_bound (h : UnramDatum C F a θ γ) :
    ∃ (q : ℕ → C[X]) (B : ℝ), 0 ≤ B ∧
      (∀ k, algebraMap C[X] (RatFunc C) (q k) = (minpoly (RatFunc C) θ).coeff k) ∧
      (∀ k, (q k).eval a = ((P₀ γ).map (algebraMap 𝒪 C)).coeff k) ∧
      ∀ k j, ‖(taylor a (q k)).coeff j‖ ≤ B := by
  classical
  choose q hq hev using h.poly
  set N := (minpoly (RatFunc C) θ).natDegree
  set B : ℝ := ∑ k ∈ Finset.range (N + 1), ∑ j ∈ Finset.range ((q k).natDegree + 1),
    ‖(taylor a (q k)).coeff j‖
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine ⟨q, B, hB0, hq, hev, fun k j ↦ ?_⟩
  by_cases hk : k ≤ N
  · by_cases hj : j ≤ (q k).natDegree
    · calc ‖(taylor a (q k)).coeff j‖
          ≤ ∑ j ∈ Finset.range ((q k).natDegree + 1), ‖(taylor a (q k)).coeff j‖ :=
            Finset.single_le_sum (f := fun j ↦ ‖(taylor a (q k)).coeff j‖)
              (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.2 (by omega))
        _ ≤ B := Finset.single_le_sum
            (f := fun k ↦ ∑ j ∈ Finset.range ((q k).natDegree + 1), ‖(taylor a (q k)).coeff j‖)
            (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_range.2 (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; omega), norm_zero]
      exact hB0
  · have hq0 : q k = 0 := by
      have h0 := hq k
      rw [coeff_eq_zero_of_natDegree_lt (by omega)] at h0
      exact (IsFractionRing.injective C[X] (RatFunc C)) (by rw [h0, map_zero])
    rw [hq0, map_zero, coeff_zero, norm_zero]
    exact hB0

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [IsAlgClosed C] in
/-- **The split datum on small discs around an unramified point.** -/
theorem exists_splitDatum (h : UnramDatum C F a θ γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ (c : C) (hc : c ≠ 0), ‖c‖ ≤ s₀ →
      SplitDatum C (Aff a c hc F) (toAff hc θ) γ := by
  obtain ⟨q, B, hB0, hq, hev, hB⟩ := exists_taylor_bound h
  refine ⟨1 / (B + 2), by positivity, fun c hc hcs ↦ ?_⟩
  have hs1 : 1 / (B + 2) ≤ 1 / 2 := by gcongr; linarith
  -- the coefficients `T k = q_k(c x + a)`
  set T : ℕ → C[X] := fun k ↦ (taylor a (q k)).comp (Polynomial.C c * X)
  have hTc : ∀ k j, (T k).coeff j = (taylor a (q k)).coeff j * c ^ j := fun k j ↦
    SplitDisc.coeff_comp_C_mul_X _ _ _
  have hT0 : ∀ k, (T k).coeff 0 = ((P₀ γ).map (algebraMap 𝒪 C)).coeff k := fun k ↦ by
    rw [hTc, pow_zero, mul_one, taylor_coeff_zero, hev]
  have hTsmall : ∀ k j, j ≠ 0 → ‖(T k).coeff j‖ < 1 := fun k j hj ↦ by
    rw [hTc, norm_mul, norm_pow]
    have hc1 : ‖c‖ ≤ 1 := hcs.trans (hs1.trans (by norm_num))
    calc ‖(taylor a (q k)).coeff j‖ * ‖c‖ ^ j ≤ B * ‖c‖ := by
          gcongr
          · exact hB k j
          · exact pow_le_of_le_one (norm_nonneg _) hc1 hj
      _ ≤ B * (1 / (B + 2)) := by gcongr
      _ < 1 := by rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hT1 : ∀ k j, ‖(T k).coeff j‖ ≤ 1 := fun k j ↦ by
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hT0, coeff_map]
      exact HenselComplete.norm_le_one _
    · exact (hTsmall k j hj).le
  have hmin : ∀ k, (minpoly (RatFunc C) (toAff hc θ : Aff a c hc F)).coeff k =
      algebraMap C[X] (RatFunc C) (T k) := fun k ↦ by
    rw [minpoly_toAff, coeff_map, ← hq, RingHom.coe_coe, aff_symm_algebraMap]
  refine ⟨by rw [finrank_aff]; exact h.card, ?_, h.sep, fun k ↦ ?_⟩
  · -- integrality over the vertex chart
    have hcoeffs : ↑(minpoly (RatFunc C) (toAff hc θ : Aff a c hc F)).coeffs ⊆
        ((discRing (0 : C) 1 : Subring (RatFunc C)) : Set (RatFunc C)) := fun φ hφ ↦ by
      obtain ⟨k, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hφ
      rw [hmin]
      exact mem_discRing_iff.2 ⟨T k, gaussSup_le_one (hT1 k), rfl⟩
    refine ⟨(minpoly (RatFunc C) (toAff hc θ : Aff a c hc F)).toSubring _ hcoeffs,
      (monic_toSubring _ _ hcoeffs).2 (minpoly.monic (Algebra.IsIntegral.isIntegral _)), ?_⟩
    have := minpoly.aeval (RatFunc C) (toAff hc θ : Aff a c hc F)
    rw [← map_toSubring _ _ hcoeffs, aeval_def, eval₂_map] at this
    exact this
  · rw [hmin]
    change gauss1 C (algebraMap C[X] (RatFunc C) (T k) -
      algebraMap C (RatFunc C) (((P₀ γ).map (algebraMap 𝒪 C)).coeff k)) < 1
    rw [← hT0, show algebraMap C (RatFunc C) ((T k).coeff 0) =
      algebraMap C[X] (RatFunc C) (Polynomial.C ((T k).coeff 0)) from
        (RatFunc.algebraMap_C _).symm, ← map_sub]
    rw [gauss1_algebraMap]
    refine gaussSup_lt_one fun j ↦ ?_
    rw [coeff_sub, coeff_C]
    split_ifs with hj
    · subst hj; simp
    · rw [sub_zero]; exact hTsmall k j hj

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **S8.2, unramified case**: small residue balls around a classical point with an unramified
datum are good. -/
theorem ballGood_of_unramDatum (h : UnramDatum C F a θ γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ c : C, c ≠ 0 → ‖c‖ ≤ s₀ → S8A.BallGood F (Metric.ball a ‖c‖) := by
  obtain ⟨s₀, hs₀, H⟩ := exists_splitDatum h
  refine ⟨s₀, hs₀, fun c hc hcs ↦ (S8A.Transport.ballGood_iff hc).2 ?_⟩
  intro P' hP' hcen
  exact isDiscSmooth_of_splitDatum hp hp1 (H c hc hcs) P' hcen

end ClassicalSmooth

end SemistableReduction
