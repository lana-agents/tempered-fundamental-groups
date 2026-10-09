/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothDiscLocal
import TemperedFundamentalGroups.SemistableReduction.ChartBasis

/-!
# Lemma (L): the residue class of a smooth point is an open disc

Blueprint §9.12, O11 (D⇒), lemma (L), valuative form.

* **`exists_disc_coord`**: if every point of `R' = DRint 0 1 G` over `|x| < 1` is smooth, every
  valuation `W` of `G` over a disc valuation with a residually transcendental element has a
  coordinate `Z` (Gauss formula) with `C(Z)` dense in `G` for `W` and `x` approximated by
  polynomials in `Z`: at the smooth point `P'` below `W` take `u = s + xᵐ` (`SmoothDiscLocal`),
  in which `P'` has disc degree one (`exists_count`); then `W` is attached to a factor of degree
  one, its restriction to `C(u)` is a Gauss point `w_{a',|c'|}` and `Z = (u - a')/c'`;
* **`tube_of_coord`**: in that situation the residue curve of `W` is the line `k(Z̄)` and `x̄` is
  a polynomial in `Z̄`, so it has exactly one pole (`card_zeros_inv_aeval`).
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace SmoothDisc

open FundamentalInequality GaussStability GaussFibre PlaceNorm GaussTube DiscCount SmoothVertex
  ClassicalSmooth TubeCount DiscGerm LocalGlobal DenseCompletion

universe u

section Coord

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- A polynomial in `x` is a polynomial in `(x - a')/c'`. -/
lemma algebraMap_eq_aeval_gaussCoord {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] {a' c' : C} (hc : c' ≠ 0) (P : C[X]) :
    algebraMap (RatFunc C) F (algebraMap C[X] (RatFunc C) P) =
      aeval (algebraMap (RatFunc C) F (gaussCoord a' c'))
        (P.comp (Polynomial.C c' * X + Polynomial.C a')) := by
  rw [aeval_comp]
  have h : aeval (algebraMap (RatFunc C) F (gaussCoord a' c'))
      (Polynomial.C c' * X + Polynomial.C a') = algebraMap (RatFunc C) F RatFunc.X := by
    rw [X_eq_gaussCoord (a := a') hc, map_add, map_mul, aeval_X, aeval_C, map_add, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, aeval_C]
  rw [h, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]

variable {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
include hp hp1

/-- **Lemma (L), local form.** Let every point of `R' = DRint 0 1 G` over the open disc `|x| < 1`
be smooth, and let `W` be a valuation of `G` over a disc valuation with a residually
transcendental element `y₀` (Gauss formula). Then there is `Z ∈ G` satisfying the Gauss formula
(a coordinate of the residue curve of `W`), such that `C(Z)` is dense in `G` for `W` and `x` is
approximated by polynomials in `Z`: the residue curve of `W` is the line `k(Z̄)` and `x̄` is a
polynomial in `Z̄`. -/
theorem exists_disc_coord
    (hsm : ∀ P' : Ideal (DRint (0 : C) 1 G), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) = discIdeal (0 : C) 1 →
        IsDiscSmooth P')
    (W : Valuation G ℝ≥0) (hW : IsDiscVal (0 : C) 1 (W.comap (algebraMap (RatFunc C) G)))
    {y₀ : G} (hy₀ : ∀ Q : C[X], W (aeval y₀ Q) = Gauss.sup (NormedField.valuation (K := C)) 1 Q) :
    ∃ Z : G, (∀ Q : C[X], W (aeval Z Q) = Gauss.sup (NormedField.valuation (K := C)) 1 Q) ∧
      (∀ f : G, ∃ A B : C[X], aeval Z B ≠ 0 ∧ W (f - aeval Z A / aeval Z B) < 1) ∧
      ∀ ε : ℝ, 0 < ε → ∃ H : C[X], (W (xF C G - aeval Z H) : ℝ) < ε := by
  classical
  set P' := center hW
  haveI hPmax : P'.IsMaximal := center_isMaximal one_ne_zero hW
  obtain ⟨v, Q, hQ, hPv, hb, s, hu, hx, hsQ⟩ := exists_coord P' (hsm P' hPmax (comap_center hW))
  haveI : FiniteDimensional (RatFunc C) (Coord hu) := finiteDimensional_coord hu
  haveI : Algebra.IsSeparable (RatFunc C) (Coord hu) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨e, heP, hcount⟩ := exists_count hu hx hp hp1 v hQ hb rfl hsQ
  have hexp : (exp (-1) : ℤᵐ⁰) < 1 := by rw [← exp_zero, exp_lt_exp]; norm_num
  have hsP : s ∈ P' := by
    rw [← hPv, mem_placeIdealD_iff]
    exact Q.res_eq_zero_of_lt_one (hsQ ▸ hexp)
  -- `W` in the coordinate `u = s`
  set W' : Valuation (Coord hu) ℝ≥0 := W
  have hW' : IsDiscVal (0 : C) 1 (W'.comap (algebraMap (RatFunc C) (Coord hu))) := by
    refine ⟨fun c ↦ ?_, ?_⟩
    · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]
      have := hW.map_C c
      rwa [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply] at this
    · rw [gaussCoord_zero_one, Valuation.comap_apply]
      change W (coordAlgHom hu RatFunc.X) < 1
      rw [← RatFunc.algebraMap_X, coordAlgHom_algebraMap, aeval_X]
      exact hsP
  obtain ⟨ν, hν⟩ : ∃ ν : DiscVal (0 : C) 1,
      W'.comap (algebraMap (RatFunc C) (Coord hu)) = ν.val := ⟨⟨_, hW'⟩, rfl⟩
  have he' : W' ((incl hu hx e : DRint (0 : C) 1 (Coord hu)) : Coord hu) < 1 := by
    have : e ∈ P' := hPv ▸ heP
    exact this
  obtain ⟨g, hg, hdeg, h1⟩ := exists_factor_of_count ν hν he' hcount
  have hy₀' : ∀ Q : C[X], extValuation g (aeval (toCoord hu y₀) Q) =
      Gauss.sup (NormedField.valuation (K := C)) 1 Q := fun Q ↦ by
    rw [hg]
    exact hy₀ Q
  obtain ⟨a', c', hc0, hgauss⟩ := exists_gaussCoord g hdeg hy₀'
  obtain ⟨Zc, hZc⟩ : ∃ Zc : Coord hu,
      Zc = algebraMap (RatFunc C) (Coord hu) (gaussCoord a' c') := ⟨_, rfl⟩
  have hpoly (P : C[X]) : algebraMap (RatFunc C) (Coord hu) (algebraMap C[X] (RatFunc C) P) =
      aeval Zc (P.comp (Polynomial.C c' * X + Polynomial.C a')) := by
    rw [hZc]
    exact algebraMap_eq_aeval_gaussCoord hc0 P
  refine ⟨(toCoord hu).symm Zc, fun Q ↦ ?_, fun f ↦ ?_, fun ε hε ↦ ?_⟩
  · have h := hgauss Q
    rw [hg, ← aeval_algebraMap_apply, ← hZc] at h
    exact h
  · obtain ⟨φ, hφ⟩ := exists_ratFunc_approx_of_natDegree g hdeg (toCoord hu f) one_pos
    rw [hg] at hφ
    refine ⟨φ.num.comp (Polynomial.C c' * X + Polynomial.C a'),
      φ.denom.comp (Polynomial.C c' * X + Polynomial.C a'), ?_, ?_⟩
    · intro h0
      have h2 : algebraMap (RatFunc C) (Coord hu) (algebraMap C[X] (RatFunc C) φ.denom) = 0 :=
        (hpoly φ.denom).trans h0
      rw [map_eq_zero_iff _ (algebraMap (RatFunc C) (Coord hu)).injective,
        map_eq_zero_iff _ (IsFractionRing.injective C[X] (RatFunc C))] at h2
      exact φ.denom_ne_zero h2
    · have hφ' : algebraMap (RatFunc C) (Coord hu) φ =
          aeval Zc (φ.num.comp (Polynomial.C c' * X + Polynomial.C a')) /
            aeval Zc (φ.denom.comp (Polynomial.C c' * X + Polynomial.C a')) := by
        rw [← hpoly, ← hpoly, ← map_div₀, RatFunc.num_div_denom]
      rw [hφ'] at hφ
      exact_mod_cast hφ
  · obtain ⟨H, -, hH⟩ := exists_poly_approx_of_discDegree g h1 ⟨toCoord hu (xF C G), hx⟩ hε
    refine ⟨H.comp (Polynomial.C c' * X + Polynomial.C a'), ?_⟩
    rw [hg, RatFunc.aeval_X_left_eq_algebraMap, hpoly] at hH
    exact hH

end Coord

section Residue

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "vC" => NormedField.valuation (K := C)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) K] in
lemma red_aeval_of_sup (w : Ext C K) {Z : K} (hZ : w.1 Z ≤ 1) {P : C[X]}
    (hP : Gauss.sup vC 1 P ≤ 1) : red C (aeval Z P) w = aeval (red C Z w) (redPoly P) := by
  obtain ⟨P', hP', hred⟩ := exists_lift_redPoly hP
  conv_lhs => rw [← hP']
  rw [red_aeval_of_le hZ, hred]

/-- **Poles of a polynomial in a coordinate**: if `κ = k(z)` and `t = P(z)` is not constant, then
`t` has exactly one pole. -/
lemma card_zeros_inv_aeval {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
    [IsCurveFunctionField k κ] {z : κ} (hz : k⟮z⟯ = ⊤) (hzr : z ∉ (algebraMap k κ).range)
    {P : k[X]} (ht : aeval z P ∉ (algebraMap k κ).range) :
    (zeros k (aeval z P)⁻¹).card = 1 := by
  have hz1 : (zeros k z⁻¹).card = 1 := by
    have hf : Module.finrank k⟮z⟯ κ ≤ 1 := by
      rw [hz, IntermediateField.finrank_top]
    exact (TubeSkeleton.tube_of_eq_smul_pow one_ne_zero le_rfl
      (by rw [map_one, one_mul, pow_one]) hzr hf).2.1
  have hz0 : z ≠ 0 := fun h ↦ hzr ⟨0, by rw [h, map_zero]⟩
  have ht0 : aeval z P ≠ 0 := fun h ↦ ht ⟨0, by rw [h, map_zero]⟩
  -- the poles of `P(z)` are poles of `z`
  have hsub : zeros k (aeval z P)⁻¹ ⊆ zeros k z⁻¹ := by
    intro R hR
    rw [SmoothDisc.mem_zeros_iff_lt_one R (inv_ne_zero ht0)] at hR
    rw [SmoothDisc.mem_zeros_iff_lt_one R (inv_ne_zero hz0)]
    by_contra hle
    rw [not_lt, map_inv₀, one_le_inv₀ ((Valuation.pos_iff _).2 hz0)] at hle
    have h1 : R.valuation (aeval z P) ≤ 1 :=
      valuation_aeval_le_one R.valuation_algebraMap_le_one hle P
    rw [map_inv₀, inv_lt_one₀ ((Valuation.pos_iff _).2 ht0)] at hR
    exact absurd (hR.trans_le h1) (lt_irrefl 1)
  -- `P(z)` has a pole
  have hne : (zeros k (aeval z P)⁻¹).Nonempty := by
    have hti : (aeval z P)⁻¹ ∉ (algebraMap k κ).range := by
      rintro ⟨c, hc⟩
      exact ht ⟨c⁻¹, by rw [map_inv₀, hc, inv_inv]⟩
    have hs := sum_ord hti
    haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hti)
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hs
    exact Module.finrank_pos.ne hs
  have := Finset.card_le_card hsub
  have := hne.card_pos
  omega

omit [FiniteDimensional (RatFunc C) K] [IsAlgClosed C] in
/-- `Z` with the Gauss formula has value `≤ 1` and non-constant reduction. -/
lemma red_notMem_range_of_gauss (w : Ext C K) {Z : K}
    (ha : ∀ Q : C[X], w.1 (aeval Z Q) = Gauss.sup vC 1 Q) :
    w.1 Z ≤ 1 ∧ red C Z w ∉ (algebraMap 𝓀 (ResidueField w.1.valuationSubring)).range := by
  have hZ1 : w.1 Z ≤ 1 := by
    have := ha X
    rw [aeval_X, sup_X] at this
    exact this.le
  refine ⟨hZ1, fun ⟨k₀, hk₀⟩ ↦ ?_⟩
  obtain ⟨c₀, rfl⟩ := residue_surjective k₀
  have hc₀ : ‖(c₀ : C)‖₊ ≤ 1 := by exact_mod_cast (HenselComplete.mem_integers_iff _).1 c₀.2
  have hc : w.1 (algebraMap C K c₀) ≤ 1 := by rw [valuation_algebraMap_C']; exact hc₀
  have h0 : red C (Z - algebraMap C K c₀) w = 0 := by
    rw [red_sub hZ1 hc, red_algebraMap_C _ hc₀, ← hk₀, sub_self]
  rw [red_eq_zero_iff ((Valuation.map_sub _ _ _).trans (max_le hZ1 hc))] at h0
  have h2 := ha (X - Polynomial.C (c₀ : C))
  rw [map_sub, aeval_X, aeval_C, sup_X_sub_C (by exact_mod_cast hc₀)] at h2
  rw [h2] at h0
  exact lt_irrefl 1 h0

/-- **The residue curve in a coordinate.** Let `w` extend `w_{0,1}` to `K` and `Z ∈ K` satisfy the
Gauss formula, with `C(Z)` dense in `K` for `w` and `x` approximated by a polynomial in `Z`.
Then the residue curve of `w` is rational, and `x̄` has exactly one pole. -/
theorem tube_of_coord (w : Ext C K) {Z : K}
    (ha : ∀ Q : C[X], w.1 (aeval Z Q) = Gauss.sup vC 1 Q)
    (hb : ∀ f : K, ∃ A B : C[X], aeval Z B ≠ 0 ∧ w.1 (f - aeval Z A / aeval Z B) < 1)
    (hc : ∃ H : C[X], w.1 (xF C K - aeval Z H) < 1) :
    genus 𝓀 (ResidueField w.1.valuationSubring) = 0 ∧
      (zeros 𝓀 (red C (xF C K) w)⁻¹).card = 1 := by
  obtain ⟨hZ1, hzr⟩ := red_notMem_range_of_gauss w ha
  set z := red C Z w
  -- `κ(w) = k(z)`
  have htop : 𝓀⟮z⟯ = ⊤ := by
    refine eq_top_iff.2 fun r _ ↦ ?_
    obtain ⟨⟨f, hf⟩, rfl⟩ := residue_surjective r
    obtain ⟨A, B, hB0, hAB⟩ := hb f
    have hBne : B ≠ 0 := by rintro rfl; exact hB0 (by simp)
    obtain ⟨i, hi⟩ := Gauss.exists_term_eq_sup (v := vC) (r := 1) B
    have hBi : B.coeff i ≠ 0 := by
      intro h0
      have hpos := sup_pos_of_ne_zero hBne
      rw [← hi] at hpos
      simp [Gauss.term, h0] at hpos
    set l := B.coeff i
    set A' := Polynomial.C l⁻¹ * A
    set B' := Polynomial.C l⁻¹ * B
    have hsupB : Gauss.sup vC 1 B' = 1 := by
      rw [Gauss.sup_mul, Gauss.sup_C, ← hi]
      simp [Gauss.term, l, hBi]
    have hwB : w.1 (aeval Z B') = 1 := by rw [ha, hsupB]
    have hq : aeval Z A / aeval Z B = aeval Z A' / aeval Z B' := by
      have hl : algebraMap C K l⁻¹ ≠ 0 := by simpa using hBi
      simp only [A', B', map_mul, aeval_C]
      rw [mul_div_mul_left _ _ hl]
    rw [hq] at hAB
    have hq1 : w.1 (aeval Z A' / aeval Z B') ≤ 1 := by
      have := Valuation.map_sub w.1 f (f - aeval Z A' / aeval Z B')
      rw [sub_sub_cancel] at this
      exact this.trans (max_le hf hAB.le)
    have hwA : w.1 (aeval Z A') ≤ 1 := by
      rw [map_div₀, hwB, div_one] at hq1
      exact hq1
    have hsupA : Gauss.sup vC 1 A' ≤ 1 := by rw [← ha]; exact hwA
    -- `f B'(Z) ≡ A'(Z)`
    have hB0' : aeval Z B' ≠ 0 := fun h ↦ by rw [h, map_zero] at hwB; exact zero_ne_one hwB
    have hdiff : w.1 (f * aeval Z B' - aeval Z A') < 1 := by
      have : f * aeval Z B' - aeval Z A' = (f - aeval Z A' / aeval Z B') * aeval Z B' := by
        field_simp
      rw [this, map_mul, hwB, mul_one]
      exact hAB
    have hfB : w.1 (f * aeval Z B') ≤ 1 := by rw [map_mul, hwB, mul_one]; exact hf
    have hred : red C f w * aeval z (redPoly B') = aeval z (redPoly A') := by
      rw [← red_aeval_of_sup w hZ1 hsupB.le, ← red_aeval_of_sup w hZ1 hsupA,
        ← red_mul hf (by rw [hwB]), ← sub_eq_zero, ← red_sub hfB hwA,
        red_eq_zero_iff ((Valuation.map_sub _ _ _).trans (max_le hfB hwA))]
      exact hdiff
    have hz0 : aeval z (redPoly B') ≠ 0 := by
      rw [← red_aeval_of_sup w hZ1 hsupB.le, Ne, red_eq_zero_iff hwB.le, hwB]
      exact lt_irrefl 1
    have : residue w.1.valuationSubring ⟨f, hf⟩ = red C f w := (red_of_le hf).symm
    rw [this, eq_div_of_mul_eq hz0 hred]
    exact div_mem
      (IntermediateField.algebra_adjoin_le_adjoin 𝓀 {z} (aeval_mem_adjoin_singleton 𝓀 z))
      (IntermediateField.algebra_adjoin_le_adjoin 𝓀 {z} (aeval_mem_adjoin_singleton 𝓀 z))
  refine ⟨genus_eq_zero_of_adjoin_eq_top htop, ?_⟩
  -- `x̄` is a polynomial in `z`
  obtain ⟨H, hH⟩ := hc
  have hxH : w.1 (aeval Z H) ≤ 1 := by
    have := Valuation.map_sub w.1 (xF C K) (xF C K - aeval Z H)
    rw [sub_sub_cancel] at this
    exact this.trans (max_le (valuation_xF w).le hH.le)
  have hsupH : Gauss.sup vC 1 H ≤ 1 := by rw [← ha]; exact hxH
  have hxred : red C (xF C K) w = aeval z (redPoly H) := by
    rw [← red_aeval_of_sup w hZ1 hsupH, ← sub_eq_zero, ← red_sub (valuation_xF w).le hxH,
      red_eq_zero_iff ((Valuation.map_sub _ _ _).trans (max_le (valuation_xF w).le hxH))]
    exact hH
  have hxr : red C (xF C K) w ∉ (algebraMap 𝓀 (ResidueField w.1.valuationSubring)).range :=
    fun ⟨b, hb⟩ ↦ transcendental_red_x (F := K) w (hb ▸ isAlgebraic_algebraMap b)
  rw [hxred] at hxr ⊢
  exact card_zeros_inv_aeval htop hzr hxr

end Residue

end SmoothDisc

end SemistableReduction
