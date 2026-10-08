/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourKummerStep
import TemperedFundamentalGroups.SemistableReduction.KummerUnram

/-!
# The Kummer step from the degree reduction

Blueprint §9.12, leaf T4:
`TypeFour.kummerStepFor_of : DegreeReductionFor C p → KummerStepFor C F p`.
In the coordinate `s` (dense in `K`) the point is of type 4 (`isTypeFour_coord`,
`exists_radius_bound_coord`) and `K` is a sheet; DiscGerm gives polynomial approximants `Qₙ(s)`
of `θ^p` (`exists_germ_approx`, after rescaling `θ`); `Qₙ` is not approximable by `p`-th powers
to the Kummer bound (`lt_valuation_pow_sub`), so the degree reduction gives a linear-dominant
disc, and the endgame (`mem_vClosure_endgame`) puts `s`, hence `K[θ]`, into the closure of
`C(w)`, `w = (θ/H(s) - 1)/λ`.
-/

open Polynomial Filter Topology
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open DiscCount LocalGlobal DenseCompletion ClassicalSmooth

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section Coord

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F]

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- The coordinate map of an intermediate field, followed by the inclusion. -/
lemma coe_coordAlgHom {K : IntermediateField (RatFunc C) F} {s : F} (hsK : s ∈ K)
    (hs : Transcendental C s) (hsK' : Transcendental C (⟨s, hsK⟩ : K)) (φ : RatFunc C) :
    ((coordAlgHom hsK' φ : K) : F) = coordAlgHom hs φ := by
  have : ((K.val.restrictScalars C).comp (coordAlgHom hsK')) = coordAlgHom hs := by
    refine ratFunc_algHom_ext ?_
    simp only [AlgHom.comp_apply]
    rw [← RatFunc.algebraMap_X, coordAlgHom_algebraMap, coordAlgHom_algebraMap, aeval_X, aeval_X]
    rfl
  exact congrArg (fun χ : RatFunc C →ₐ[C] F ↦ χ φ) this

end Coord

section Assembly

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] [CharZero C]

/-- **The Kummer step** from the degree reduction. -/
theorem kummerStepFor_of {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    (hDR : DegreeReductionFor C p) : KummerStepFor C F p := by
  intro ξ' hconst hT hr K θ σ ζ hζ hθ0 hθp hσθ hσK hσξ s hsK hdense
  classical
  -- `s` is transcendental
  obtain ⟨r', hr'0, hr'⟩ := exists_radius_bound_coord hr hdense
  have hs : Transcendental C s := by
    intro halg
    obtain ⟨b, hb⟩ := minpoly.mem_range_of_degree_eq_one C s
      (IsAlgClosed.degree_eq_one_of_irreducible C (minpoly.irreducible halg.isIntegral))
    have := hr' b
    rw [hb, sub_self, map_zero] at this
    exact absurd hr'0 (not_lt.2 this)
  -- the type-4 point in the coordinate `s`
  set η := ξ'.comap (coordAlgHom hs).toRingHom
  have hη4 : Splitting.IsTypeFour η := isTypeFour_coord hconst hT hs
  have hηX : ∀ b : C, η (RatFunc.X - algebraMap C (RatFunc C) b) = ξ' (s - algebraMap C F b) :=
    fun b ↦ by
      change ξ' (coordAlgHom hs _) = _
      have hX : coordAlgHom hs RatFunc.X = s := by
        rw [← RatFunc.algebraMap_X, coordAlgHom_algebraMap, aeval_X]
      rw [map_sub, AlgHom.commutes, hX]
  have hηrad : ∃ r : ℝ≥0, 0 < r ∧ ∀ b : C, r ≤ η (RatFunc.X - algebraMap C (RatFunc C) b) :=
    ⟨r', hr'0, fun b ↦ by rw [hηX]; exact hr' b⟩
  -- the field `K` in the coordinate `s`
  set sK : K := ⟨s, hsK⟩
  have hsK' : Transcendental C sK := by
    rintro ⟨P, hP0, hP⟩
    apply hs
    refine ⟨P, hP0, ?_⟩
    rw [show s = (K.val.restrictScalars C) sK from rfl, aeval_algHom_apply, hP, map_zero]
  haveI : IsCurveFunctionField C K := GaussFibre.isCurveFunctionField_F
  haveI : IsCurveFunctionField C (Coord hsK') := inferInstanceAs (IsCurveFunctionField C K)
  haveI : FiniteDimensional (RatFunc C) (Coord hsK') :=
    finiteDimensional_of_transcendental (by rw [xF_coord_eq]; exact hsK')
  haveI : Algebra.IsSeparable (RatFunc C) (Coord hsK') :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- the valuation on `K`
  set ιK : Coord hsK' →+* F := (K.val : K →+* F).comp (toCoord hsK').symm.toRingHom
  set ξL : Valuation (Coord hsK') ℝ≥0 := ξ'.comap ιK
  have hconstL : ∀ b : C, ξL (algebraMap C (Coord hsK') b) = ‖b‖₊ := fun b ↦ hconst b
  have hcoordF : ∀ φ : RatFunc C,
      ιK (algebraMap (RatFunc C) (Coord hsK') φ) = coordAlgHom hs φ := fun φ ↦ by
    rw [algebraMap_coord]; exact coe_coordAlgHom hsK hs hsK' φ
  have hηL : ξL.comap (algebraMap (RatFunc C) (Coord hsK')) = η := Valuation.ext fun φ ↦ by
    simp only [Valuation.comap_apply]
    change ξ' (ιK _) = ξ' (coordAlgHom hs φ)
    rw [hcoordF]
  have hιaeval : ∀ P : C[X],
      ιK (aeval (algebraMap (RatFunc C) (Coord hsK') RatFunc.X) P) = aeval s P := fun P ↦ by
    rw [aeval_X_eq, hcoordF, coordAlgHom_algebraMap]
  have hdL : CoordDense C ξL (algebraMap (RatFunc C) (Coord hsK') RatFunc.X) := by
    intro y ε hε
    obtain ⟨P, Q, hQ, hPQ⟩ := hdense (ιK y) ((toCoord hsK').symm y).2 ε hε
    refine ⟨P, Q, fun h0 ↦ hQ (by rw [← hιaeval, h0, map_zero]), ?_⟩
    change ξ' (ιK _) < ε
    rw [map_sub, map_div₀, hιaeval, hιaeval]
    exact hPQ
  -- polynomial approximants of `θ^p`
  set y : Coord hsK' := toCoord hsK' ⟨θ ^ p, hθp⟩
  have hy0 : y ≠ 0 := by
    intro h
    have : (θ ^ p : F) = 0 :=
      congrArg Subtype.val ((toCoord hsK').injective (h.trans (map_zero _).symm))
    exact hθ0 (pow_eq_zero_iff hp.ne_zero |>.1 this)
  obtain ⟨u, b₀, c₀, l, Qt, q, hu0, hc₀, hl0, hl1, hrad, hq0, hq1, hyu1, hQ1, hCauchy, hconv⟩ :=
    exists_germ_approx hp.pos hconstL (hηL ▸ hη4) hdL hy0
  -- the rescaled Kummer generator `θ' = θ u`
  set uF : F := ιK u
  have huK : uF ∈ K := ((toCoord hsK').symm u).2
  have huF0 : uF ≠ 0 := fun h ↦ hu0 (ιK.injective (h.trans (map_zero _).symm))
  set θ' := θ * uF
  have hθ'p : θ' ^ p = ιK (y * u ^ p) := by
    simp only [θ', mul_pow, map_mul, map_pow, uF]
    rfl
  have hσθ' : σ θ' = algebraMap C F ζ * θ' := by
    simp only [θ', map_mul, hσθ, hσK _ huK]; ring
  have hθ'0 : θ' ≠ 0 := mul_ne_zero hθ0 huF0
  have hθ'1 : ξ' (θ' ^ p) = 1 := by rw [hθ'p]; exact hyu1
  -- the approximants in the coordinate `s`
  set Qn : ℕ → C[X] := fun n ↦ (Qt n).comp (Polynomial.C c₀⁻¹ * (X - Polynomial.C b₀))
  have hQev : ∀ n, ιK (algebraMap (RatFunc C) (Coord hsK') (aeval (gaussCoord b₀ c₀) (Qt n))) =
      aeval s (Qn n) := by
    intro n
    rw [hcoordF, ← Polynomial.aeval_algHom_apply, AffineTwist.gaussCoord_eq, map_mul, map_sub,
      AlgHom.commutes, AlgHom.commutes]
    have hX : coordAlgHom hs RatFunc.X = s := by
      rw [← RatFunc.algebraMap_X, coordAlgHom_algebraMap, aeval_X]
    rw [hX]
    simp only [Qn, aeval_comp, map_mul, map_sub, aeval_C, aeval_X]
  have hconvF : Tendsto (fun n ↦ (ξ' (θ' ^ p - aeval s (Qn n)) : ℝ)) atTop (𝓝 0) := by
    refine hconv.congr fun n ↦ ?_
    rw [hθ'p, ← hQev, ← map_sub]
    rfl
  -- auxiliary facts
  have hcK : ∀ φ : RatFunc C, coordAlgHom hs φ ∈ K := fun φ ↦ by
    rw [← hcoordF]; exact ((toCoord hsK').symm _).2
  have hCK : ∀ b : C, algebraMap C F b ∈ K := fun b ↦ by
    rw [← AlgHom.commutes (coordAlgHom hs)]; exact hcK _
  have hζ1 : (‖1 - ζ‖₊ : ℝ) ^ p = kummerBound C p := by
    rw [coe_nnnorm]; exact kummerBound_eq hp (norm_one_sub_pow_pred hp hζ)
  have hA1 : kummerBound C p < 1 := kummerBound_lt_one hp hp1
  have hA0 : 0 < kummerBound C p := by
    rw [← hζ1]
    refine pow_pos (NNReal.coe_pos.2 (nnnorm_pos.2 (sub_ne_zero.2 fun h ↦ ?_))) _
    exact hp.one_lt.ne' (hζ.eq_orderOf.trans (by rw [← h, orderOf_one]))
  -- the index `N`
  obtain ⟨N, hN1, hN2⟩ := ((hconvF.eventually (gt_mem_nhds hA0)).and
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually (gt_mem_nhds hA0))).exists
  have hqN : q ^ (2 ^ N) < kummerBound C p :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hq0 hq1.le Nat.lt_two_pow_self.le) hN2
  -- `Q_N` has value one and is not approximable by `p`-th powers
  have hQN1 : ξ' (aeval s (Qn N)) = 1 := by
    rw [← hθ'1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [Valuation.map_sub_swap, hθ'1, ← NNReal.coe_lt_coe, NNReal.coe_one]
    exact hN1.trans hA1
  have hηQ : η (algebraMap C[X] (RatFunc C) (Qn N)) = 1 := by
    change ξ' (coordAlgHom hs _) = 1
    rw [coordAlgHom_algebraMap]; exact hQN1
  have hNS : ∀ H : RatFunc C, H ≠ 0 → kummerBound C p * (η H : ℝ) ^ p <
      η (algebraMap C[X] (RatFunc C) (Qn N) - H ^ p) := by
    intro H hH0
    change kummerBound C p * (ξ' (coordAlgHom hs H) : ℝ) ^ p <
      ξ' (coordAlgHom hs (algebraMap C[X] (RatFunc C) (Qn N) - H ^ p))
    rw [map_sub, map_pow, coordAlgHom_algebraMap]
    set h := coordAlgHom hs H
    have hh0 : h ≠ 0 := (map_ne_zero_iff _ (coordAlgHom hs).toRingHom.injective).2 hH0
    have key := lt_valuation_pow_sub hp hp1 hconst hT hζ hσξ hh0 hσθ' (hσK _ (hcK H))
    have key' : kummerBound C p * (ξ' h : ℝ) ^ p < ξ' (θ' ^ p - h ^ p) := by
      rw [← hζ1]; exact_mod_cast key
    have hlt : ξ' (θ' ^ p - aeval s (Qn N)) < ξ' (θ' ^ p - h ^ p) := by
      by_contra hle
      push Not at hle
      have hD : (ξ' (θ' ^ p - h ^ p) : ℝ) < 1 :=
        lt_of_le_of_lt (NNReal.coe_le_coe.2 hle) (hN1.trans hA1)
      have hh1 : ξ' (h ^ p) = 1 := by
        rw [← hθ'1]
        refine Valuation.map_eq_of_sub_lt _ ?_
        rw [Valuation.map_sub_swap, hθ'1, ← NNReal.coe_lt_coe, NNReal.coe_one]
        exact hD
      rw [map_pow] at hh1
      have hh1' : (ξ' h : ℝ) ^ p = 1 := by exact_mod_cast hh1
      rw [hh1', mul_one] at key'
      exact absurd (key'.trans (lt_of_le_of_lt (NNReal.coe_le_coe.2 hle) hN1)) (lt_irrefl _)
    have heq : ξ' (aeval s (Qn N) - h ^ p) = ξ' (θ' ^ p - h ^ p) := by
      refine Valuation.map_eq_of_sub_lt _ ?_
      rw [show aeval s (Qn N) - h ^ p - (θ' ^ p - h ^ p) = -(θ' ^ p - aeval s (Qn N)) by ring,
        Valuation.map_neg]
      exact hlt
    rw [heq]; exact key'
  -- the degree reduction
  have hρ : η (RatFunc.X - algebraMap C (RatFunc C) b₀) < ‖l * c₀‖₊ := by
    rw [← hηL]; exact hrad
  obtain ⟨H, a, c, hc0, hηa, hcρ, haρ, hHa, hH, hQa, M, hAM, hM1, hMmax⟩ :=
    hDR η hη4 hηrad (Qn N) hηQ hNS b₀ ‖l * c₀‖₊ hρ
  set G := ((Qn N - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff 1
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq G hp.pos
  have hlamM : ‖lam‖ ^ p = M := by rw [← norm_pow, hlam, hM1]
  have hAlam : kummerBound C p < ‖lam‖ ^ p := hlamM ▸ hAM
  -- uniform Cauchy on the disc `D(a, |c|)`
  have hcl : ‖c‖ ≤ ‖l‖ * ‖c₀‖ := by
    have := NNReal.coe_le_coe.2 hcρ
    simpa [norm_mul] using this
  have hal : ‖a - b₀‖ ≤ ‖l‖ * ‖c₀‖ := by
    have := NNReal.coe_le_coe.2 haρ
    simpa [norm_mul] using this
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  have hunif : ∀ n ≥ N, ∀ i,
      ‖((Qn n - Qn N).comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ < ‖lam‖ ^ p := by
    intro n hn i
    have hℓ : (Polynomial.C c₀⁻¹ * (X - Polynomial.C b₀)).comp (Polynomial.C c * X +
        Polynomial.C a) = Polynomial.C (c₀⁻¹ * c) * X + Polynomial.C (c₀⁻¹ * (a - b₀)) := by
      simp only [mul_comp, sub_comp, X_comp, C_comp, map_mul, map_sub]; ring
    rw [show Qn n - Qn N = (Qt n - Qt N).comp (Polynomial.C c₀⁻¹ * (X - Polynomial.C b₀)) by
      simp only [Qn, sub_comp], comp_assoc, hℓ]
    refine lt_of_le_of_lt (norm_coeff_comp_affine_le hl0 ?_ ?_ (pow_nonneg hq0 _) ?_ i)
      (hqN.trans hAlam)
    · rw [norm_mul, norm_inv, inv_mul_le_iff₀ hc₀n]; linarith [mul_comm ‖l‖ ‖c₀‖]
    · rw [norm_mul, norm_inv, inv_mul_le_iff₀ hc₀n]; linarith [mul_comm ‖l‖ ‖c₀‖]
    · intro j
      refine (hCauchy n N j).trans (max_le ?_ le_rfl)
      exact pow_le_pow_of_le_one hq0 hq1.le (Nat.pow_le_pow_right two_pos hn)
  have hN₀ : ξ' (θ' ^ p - aeval s (Qn N)) < ‖lam‖₊ ^ p := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_pow, coe_nnnorm]
    exact hN1.trans hAlam
  have hY : ξ' (s - algebraMap C F a) < ‖c‖₊ := by rw [← hηX]; exact hηa
  have hmem := mem_vClosure_endgame hconst hp Qn H hc0 hY hHa hH N hQa hlam.symm
    (fun i ↦ hlamM ▸ hMmax i) hp1 (norm_natCast_lt_of_kummerBound_lt hp hAlam) hunif hconvF hN₀
  -- the generator `w`
  set hS := aeval s H
  have hS0 : hS ≠ 0 := by
    intro h0
    have hH0 : H = 0 := by
      by_contra hne
      exact hs ⟨H, hne, h0⟩
    rw [hH0, eval_zero, norm_zero] at hHa
    exact zero_ne_one hHa
  have hSK : hS ∈ K := by
    have := hcK (algebraMap C[X] (RatFunc C) H)
    rwa [coordAlgHom_algebraMap] at this
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow hp.ne_zero] at hAlam
    linarith
  have hlamF : algebraMap C F lam ≠ 0 := (map_ne_zero_iff _ (algebraMap C F).injective).2 hlam0
  set w := (θ' / hS - 1) / algebraMap C F lam
  have hw : w = -(algebraMap C F lam)⁻¹ + uF / (hS * algebraMap C F lam) * θ := by
    simp only [w, θ']; field_simp; ring
  have hθeq : θ = hS * (1 + algebraMap C F lam * w) / uF := by
    simp only [w, θ']; field_simp; ring
  refine ⟨w, ?_, ?_⟩
  · refine ⟨fun j ↦ if j = 0 then -(algebraMap C F lam)⁻¹ else
      if j = 1 then uF / (hS * algebraMap C F lam) else 0, fun j ↦ ?_, ?_⟩
    · beta_reduce
      split_ifs
      · exact neg_mem (inv_mem (hCK lam))
      · exact div_mem huK (mul_mem hSK (hCK lam))
      · exact zero_mem _
    · rw [hw, show p = (p - 2) + 1 + 1 by have := hp.two_le; omega, Finset.sum_range_succ',
        Finset.sum_range_succ']
      simp [add_comm]
  · rw [denseOn_iff]
    set Nw := (IntermediateField.adjoin C {w}).toSubfield
    have hCN : ∀ b : C, algebraMap C F b ∈ vClosure ξ' Nw := fun b ↦
      le_vClosure ξ' _ (IntermediateField.algebraMap_mem _ b)
    have hwN : w ∈ vClosure ξ' Nw :=
      le_vClosure ξ' _ (IntermediateField.mem_adjoin_simple_self C w)
    have haev : ∀ P : C[X], aeval s P ∈ vClosure ξ' Nw := fun P ↦ by
      rw [aeval_eq_sum_range]
      refine sum_mem fun i _ ↦ ?_
      rw [Algebra.smul_def]
      exact mul_mem (hCN _) (pow_mem hmem i)
    have hsN : (IntermediateField.adjoin C {s}).toSubfield ≤ vClosure ξ' Nw := by
      intro z hz
      obtain ⟨P, Q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff C _).1 hz
      exact div_mem (haev P) (haev Q)
    have hKN : ∀ z ∈ K, z ∈ vClosure ξ' Nw := fun z hz ↦
      vClosure_le_of_le ξ' hsN ((denseOn_iff ξ').1 hdense hz)
    have hθN : θ ∈ vClosure ξ' Nw := by
      rw [hθeq]
      exact div_mem (mul_mem (hKN _ hSK) (add_mem (one_mem _) (mul_mem (hCN _) hwN)))
        (hKN _ huK)
    rintro z ⟨d, hd, rfl⟩
    exact sum_mem fun j _ ↦ mul_mem (hKN _ (hd j)) (pow_mem hθN j)

end Assembly

section Final

universe v

variable [CharZero C]

/-- **`TypeFourGoodFor` from the degree reduction**: local uniformization holds by the Kummer step
(`kummerStepFor_of`), so only the geometric comparison `CoreGFor` and A6 remain. -/
theorem typeFourGoodFor_of_degreeReduction {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    (hDR : DegreeReductionFor C p) {F : Type v} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
    (hG : ∀ (L : Type v) [Field L] [Algebra (RatFunc C) L] [Algebra C L]
      [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
      [IsGalois (RatFunc C) L], CoreGFor C L)
    (hA6 : ∀ (L : Type v) [Field L] [Algebra (RatFunc C) L] [Algebra F L]
      [IsScalarTower (RatFunc C) F L] [Algebra C L] [IsScalarTower C (RatFunc C) L]
      [FiniteDimensional (RatFunc C) L] [IsGalois F L], ClassicalSmooth.A6For C F L) :
    S8A.TypeFourGoodFor C F :=
  typeFourGoodFor_of (fun _ _ _ _ _ _ _ ↦ unifFor_of_kummerStep hp hp1
    (kummerStepFor_of hp hp1 hDR)) hG hA6

end Final

end TypeFour

end SemistableReduction
