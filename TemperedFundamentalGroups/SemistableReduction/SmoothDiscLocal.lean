/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothDiscCount

/-!
# The residue class of a smooth point: local analysis

Blueprint §9.12, O11 (D⇒), lemma (L).

* `exists_coord`: at a smooth point `P'` of `R' = DRint 0 1 G` with unique branch `(v, Q)` there is
  `s ∈ R'` with `ord_Q s̄ = 1` and `x` integral over `O_C[s]`;
* `exists_factor_of_count`: a valuation over the disc at which an element with reduced
  characteristic polynomial of trailing degree one is small is the extension attached to a factor
  of degree one, centred at a point of disc degree one;
* `exists_ratFunc_approx_of_natDegree` (density of `C(x)`), `exists_poly_approx_of_discDegree`
  (polynomial approximation, from the germ `DiscGerm.exists_germ`);
* `exists_gaussCoord`: such an extension with a residually transcendental element restricts to a
  Gauss point `w_{a',|c'|}` of `C(x)` (W2/W3, `eq_gaussRat'`).
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace SmoothDisc

open FundamentalInequality GaussStability GaussFibre PlaceNorm GaussTube DiscCount SmoothVertex
  ClassicalSmooth TubeCount DiscGerm LocalGlobal DenseCompletion

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- **A uniformizing coordinate at a smooth point.** At a smooth point `P'` of `R' = DRint 0 1 G`
with unique branch `(v, Q)` there is `s ∈ R'` with `ord_Q s̄ = 1` such that `x` is integral over
`O_C[s]` (`s = s₀ + xᵐ`, `s₀` a lift of a uniformizer of `O_Q`). -/
theorem exists_coord (P' : Ideal (DRint (0 : C) 1 G)) (hP : IsDiscSmooth P') :
    ∃ (v : Ext C G) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
      (hQ : Q ∈ zeros 𝓀 (red C (xF C G) v)), placeIdealD v hQ = P' ∧
      (∀ b : OuterBranch C G, placeIdealD b.1 b.2.2 = placeIdealD v hQ → b = ⟨v, ⟨Q, hQ⟩⟩) ∧
      ∃ (s : DRint (0 : C) 1 G) (hu : Transcendental C (s : G)),
        IsIntegral (discRing (0 : C) 1) (toCoord hu (xF C G)) ∧
          Q.valuation (redD v s) = exp (-1) := by
  obtain ⟨⟨v, ⟨Q, hQ⟩⟩, hbs, hO⟩ := hP
  have hmem : (⟨v, ⟨Q, hQ⟩⟩ : OuterBranch C G) ∈ discBranches P' := by
    rw [hbs]; exact Set.mem_singleton _
  have hPv : placeIdealD v hQ = P' := hmem
  refine ⟨v, Q, hQ, hPv, fun b hb ↦ ?_, ?_⟩
  · have : b ∈ discBranches P' := by
      change placeIdealD b.1 b.2.2 = P'
      rw [hb, hPv]
    rw [hbs] at this
    exact this
  obtain ⟨π, hπ⟩ := Q.exists_valuation_eq_exp_neg_one
  have hexp : (exp (-1) : ℤᵐ⁰) < 1 := by rw [← exp_zero, exp_lt_exp]; norm_num
  have hπV : π ∈ Q.V := Q.valuation_le_one_iff.1 (hπ ▸ hexp.le)
  obtain ⟨y, s', hs', hys⟩ := hO π hπV
  have hs'V : redD v s' ∈ Q.V := redD_mem_V v s' (xbar_mem_V v hQ)
  have hs'1 : Q.valuation (redD v s') = 1 := by
    refine le_antisymm (Q.valuation_le_one_iff.2 hs'V) (not_lt.1 fun hlt ↦ hs' ?_)
    rw [← hPv, mem_placeIdealD_iff]
    exact Q.res_eq_zero_of_lt_one hlt
  have hy : Q.valuation (red C (y : G) v) = exp (-1) := by
    rw [← redD_apply, hys, map_mul, hπ, hs'1, mul_one]
  obtain ⟨N, D, A, hA1, hAD, heq⟩ := exists_integral_eq y
  have hval := valuation_red_coord v hQ (valuation_le_one_D v y) hy (m := D + 2) (by omega)
  have hu : Transcendental C ((y : G) + xF C G ^ (D + 2)) := transcendental_of_red v hval
  have hcoe : ((y + xD ^ (D + 2) : DRint (0 : C) 1 G) : G) = (y : G) + xF C G ^ (D + 2) := by
    rw [Subalgebra.coe_add, Subalgebra.coe_pow]
    rfl
  have key : ∀ (z : G) (_ : z = (y : G) + xF C G ^ (D + 2)) (hu' : Transcendental C z),
      IsIntegral (discRing (0 : C) 1) (toCoord hu' (xF C G)) := by
    rintro z rfl hu'
    exact isIntegral_xF_coord hA1 hAD heq (by omega) hu'
  refine ⟨y + xD ^ (D + 2), hcoe ▸ hu, key _ hcoe _, ?_⟩
  · rw [redD_apply, hcoe]
    exact hval


section Factor

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [Algebra.IsSeparable (RatFunc C) F]

omit [IsAlgClosed C] in
/-- **The factor of a valuation over the disc.** If `W` lies over a disc valuation and some
`e ∈ R'` with `W(e) < 1` has reduced characteristic polynomial of trailing degree `1`, then `W`
is the extension attached to a factor of degree one, centred at a point of disc degree one. -/
theorem exists_factor_of_count {W : Valuation F ℝ≥0} (ν : DiscVal (0 : C) 1)
    (hW : W.comap (algebraMap (RatFunc C) F) = ν.val)
    {e : DRint (0 : C) 1 F} (he : W (e : F) < 1)
    (hcount : ∀ P : (discRing (0 : C) 1)[X],
      P.map (discRing (0 : C) 1).subtype = normPoly (RatFunc C) (e : F) →
        (P.map (Ideal.Quotient.mk (discIdeal (0 : C) 1))).natTrailingDegree = 1) :
    ∃ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F,
      extValuation g = W ∧ g.1.natDegree = 1 ∧
        discDegree ν (center (isDiscVal_comap_extValuation g)) = 1 := by
  classical
  have hext : W.comap (algebraMap (DiscField ν) F) = NormedField.valuation (K := DiscField ν) := by
    refine Valuation.ext fun y ↦ ?_
    have := congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v y.ofAbs) hW
    simp only [Valuation.comap_apply] at this
    rw [Valuation.comap_apply, valuation_withAbs, ← this]
    rfl
  obtain ⟨g, hg⟩ := exists_eq_extValuation (K := UniformSpace.Completion (DiscField ν))
    (⟨W, hext⟩ : Extension (DiscField ν) F)
  replace hg : extValuation g = W := hg
  obtain ⟨P, hP⟩ := exists_lift_normPoly (a := (0 : C)) one_ne_zero e.2
  have hsum := sum_natDegree_eq_natTrailingDegree ν e.2 P hP
  rw [hcount P hP] at hsum
  set S := Finset.univ.filter (fun g : Factor (DiscField ν)
    (UniformSpace.Completion (DiscField ν)) F ↦ ‖toLocal g (e : F)‖ < 1)
  have hmemS : ∀ g' : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F,
      g' ∈ S ↔ extValuation g' (e : F) < 1 := fun g' ↦ by
    rw [Finset.mem_filter, extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
    exact and_iff_right (Finset.mem_univ _)
  have hgS : g ∈ S := (hmemS g).2 (hg ▸ he)
  have hpos : ∀ g' ∈ S, 1 ≤ g'.1.natDegree := fun g' _ ↦
    Nat.one_le_iff_ne_zero.2 (irreducible_of_mem_factors g'.2).natDegree_pos.ne'
  have hcard : S.card ≤ 1 := by
    have := Finset.card_nsmul_le_sum S (fun g ↦ g.1.natDegree) 1 hpos
    rw [smul_eq_mul, mul_one, hsum] at this
    exact this
  have huniq : ∀ g' ∈ S, g' = g := fun g' hg' ↦ Finset.card_le_one.1 hcard _ hg' _ hgS
  have hdeg : g.1.natDegree = 1 := by
    have h := Finset.single_le_sum (f := fun g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F ↦ g.1.natDegree) (fun _ _ ↦ Nat.zero_le _) hgS
    rw [hsum] at h
    exact le_antisymm h (hpos g hgS)
  refine ⟨g, hg, hdeg, ?_⟩
  unfold discDegree
  have hmemg : g ∈ Finset.univ.filter (fun g' : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F ↦ center (isDiscVal_comap_extValuation g') =
        center (isDiscVal_comap_extValuation g)) := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  convert (Finset.sum_eq_single_of_mem (f := fun g' : Factor (DiscField ν)
    (UniformSpace.Completion (DiscField ν)) F ↦ g'.1.natDegree) _ hmemg ?_).trans hdeg using 0
  · intro g' hg' hne
    refine absurd (huniq g' ((hmemS g').2 ?_)) hne
    have h1 : e ∈ center (isDiscVal_comap_extValuation g) := by
      rw [DiscCount.mem_center_iff]
      exact hg ▸ he
    rw [(Finset.mem_filter.1 hg').2.symm] at h1
    exact h1

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- **Density at a factor of degree one**: `C(x)` is dense in `F` for the extension attached to a
factor of degree one. -/
theorem exists_ratFunc_approx_of_natDegree {ν : DiscVal (0 : C) 1}
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F) (hdeg : g.1.natDegree = 1)
    (z : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : RatFunc C, (extValuation g (z - algebraMap (RatFunc C) F φ) : ℝ) < ε := by
  set K := UniformSpace.Completion (DiscField ν)
  set τ : K := Algebra.trace K (Local K g.1) (toLocal g z)
  have hτ : algebraMap K (Local K g.1) τ = toLocal g z :=
    algebraMap_trace_of_natDegree_eq_one hdeg _
  obtain ⟨φ', hφ'⟩ := exists_norm_sub_lt _ (denseRange_algebraMap_completion (DiscField ν)) τ hε
  refine ⟨WithAbs.ofAbs φ', ?_⟩
  change ‖toLocal g (z - algebraMap (RatFunc C) F (WithAbs.ofAbs φ'))‖ < ε
  rw [map_sub, toLocal_algebraMap_ratFunc, ← hτ, ← map_sub, norm_algebraMap_local, norm_sub_rev]
  exact hφ'

omit [IsAlgClosed C] in
/-- **Polynomial approximation at a point of disc degree one** (the germ, `DiscGerm.exists_germ`):
every `y ∈ R'` is approximated by polynomials in `x` with integral coefficients at the extension
centred at the point. -/
theorem exists_poly_approx_of_discDegree {ν : DiscVal (0 : C) 1}
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F)
    (h1 : discDegree ν (center (isDiscVal_comap_extValuation g)) = 1) (y : DRint (0 : C) 1 F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : C[X], (∀ i, ‖Q.coeff i‖₊ ≤ 1) ∧
      (extValuation g ((y : F) - algebraMap (RatFunc C) F (aeval RatFunc.X Q)) : ℝ) < ε := by
  haveI := center_isMaximal (a := (0 : C)) one_ne_zero (isDiscVal_comap_extValuation g)
  obtain ⟨G, Q, -, hQ1, -, hconv⟩ := exists_germ one_ne_zero ν _ h1 y
  have h := hconv ν g rfl
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := h2.exists
  refine ⟨Q n, hQ1 n, ?_⟩
  change ‖toLocal g ((y : F) - _)‖ < ε
  rw [map_sub, norm_sub_rev, ← SmoothVertex.gaussCoord_zero_one]
  exact hn

/-- **The restriction to `C(x)` of a degree-one extension with a residually transcendental element
is a Gauss point**: if some `y₀ ∈ F` satisfies the Gauss formula `W(Q(y₀)) = ‖Q‖` at the extension
`W` attached to a factor of degree one, then `W` restricted to `C(x)` is `w_{a',|c'|}`, i.e. the
coordinate `(x - a')/c'` satisfies the Gauss formula. -/
theorem exists_gaussCoord [Algebra C F] [IsScalarTower C (RatFunc C) F] {ν : DiscVal (0 : C) 1}
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F) (hdeg : g.1.natDegree = 1)
    {y₀ : F} (hy₀ : ∀ Q : C[X], extValuation g (aeval y₀ Q) =
      Gauss.sup (NormedField.valuation (K := C)) 1 Q) :
    ∃ a' c' : C, c' ≠ 0 ∧ ∀ Q : C[X],
      extValuation g (algebraMap (RatFunc C) F (aeval (gaussCoord a' c') Q)) =
        Gauss.sup (NormedField.valuation (K := C)) 1 Q := by
  set W := extValuation g
  set μ := W.comap (algebraMap (RatFunc C) F)
  have hμν : μ = ν.val := KummerSheet.comap_extValuation g
  have hw : ∀ c : C, μ (algebraMap C (RatFunc C) c) = NormedField.valuation (K := C) c := fun c ↦ by
    rw [hμν, ν.isDiscVal.map_C, NormedField.valuation_apply]
  have hC : μ.comap (algebraMap C (RatFunc C)) = NormedField.valuation (K := C) :=
    Valuation.ext fun c ↦ by rw [Valuation.comap_apply, hw]
  letI := DenseCompletion.hasExtension_of_comap_eq hC
  -- a residually transcendental element of `C(x)`
  obtain ⟨φ, hφ⟩ := exists_ratFunc_approx_of_natDegree g hdeg y₀ one_pos
  replace hφ : W (y₀ - algebraMap (RatFunc C) F φ) < 1 := by exact_mod_cast hφ
  have hy1 : W y₀ ≤ 1 := by
    have := hy₀ X
    rw [aeval_X] at this
    rw [this]
    exact Gauss.sup_le_iff.2 fun i ↦ by
      simp only [Gauss.term, coeff_X, Units.val_one, one_pow, mul_one]
      split_ifs <;> simp
  have hφ1 : μ φ ≤ 1 := by
    change W (algebraMap (RatFunc C) F φ) ≤ 1
    have := Valuation.map_sub W y₀ (y₀ - algebraMap (RatFunc C) F φ)
    rw [sub_sub_cancel] at this
    exact this.trans (max_le hy1 hφ.le)
  have htr : Algebra.Transcendental 𝓀 (ResidueField μ.valuationSubring) := by
    refine Algebra.transcendental_def.2 ⟨residue μ.valuationSubring ⟨φ, hφ1⟩, ?_⟩
    refine transcendental_of_notMem_range fun ⟨k₀, hk₀⟩ ↦ ?_
    obtain ⟨c₀, rfl⟩ := residue_surjective k₀
    rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap, ← sub_eq_zero,
      ← map_sub, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff] at hk₀
    have hlt : W (algebraMap (RatFunc C) F φ - algebraMap C F c₀) < 1 := by
      rw [Valuation.map_sub_swap]
      convert hk₀ using 2
      simp [μ, IsScalarTower.algebraMap_apply C (RatFunc C) F]
    have h1 : W (y₀ - algebraMap C F c₀) < 1 := by
      have : y₀ - algebraMap C F c₀ = (y₀ - algebraMap (RatFunc C) F φ) +
          (algebraMap (RatFunc C) F φ - algebraMap C F c₀) := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans_lt (max_lt hφ hlt)
    have h2 := hy₀ (X - Polynomial.C (c₀ : C))
    rw [map_sub, aeval_X, aeval_C] at h2
    rw [h2] at h1
    have h3 := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1)
      (X - Polynomial.C (c₀ : C)) 1
    simp [Gauss.term] at h3
    exact absurd (h3.trans_lt h1) (lt_irrefl 1)
  obtain ⟨a', r, hr⟩ := eq_gaussRat' (K := C) (v := NormedField.valuation (K := C)) (w := μ) hw htr
  obtain ⟨c', hc'⟩ := exists_eq_of_transcendental (v := NormedField.valuation (K := C)) (w := μ)
    trdeg_ratFunc.le htr (algebraMap C[X] (RatFunc C) (X - Polynomial.C a'))
  have hXa : μ (algebraMap C[X] (RatFunc C) (X - Polynomial.C a')) = r := by
    rw [hr, gaussRat_algebraMap, gauss_X_sub_C, sub_self, map_zero]
    exact max_eq_right zero_le
  have hr' : (r : ℝ≥0) = ‖c'‖₊ := by rw [← hXa, hc', hw, NormedField.valuation_apply]
  have hc0 : c' ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hr'
    exact r.ne_zero hr'
  have hrU : r = Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc0) := Units.ext hr'
  refine ⟨a', c', hc0, fun Q ↦ ?_⟩
  change μ (aeval (gaussCoord a' c') Q) = _
  rw [hr, hrU, gaussRat_aeval_eq hc0 hc0, div_self hc0, map_one, one_mul, comp_X]

end Factor

end SmoothDisc

end SemistableReduction
