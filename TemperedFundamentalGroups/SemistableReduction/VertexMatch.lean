/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TubePoints
import TemperedFundamentalGroups.SemistableReduction.ResidueNorm
import TemperedFundamentalGroups.SemistableReduction.PlaceNorm

/-!
# Tube degrees at the outer vertex

Blueprint §9.9, W7 layer S6 (glue). Let `nodeRing c = O_C[x, c/x]` (`0 < |c| < 1`), `F' / C(x)`
finite separable and `R'` the integral closure of the node chart in `F'`. The outer vertex of the
annulus is the Gauss point `w_{0,1}`; its extensions `w` have residue curves `κ(w)` containing
`x̄`, and the branches of the special fibre through the node are the zeros `Q` of `x̄` on the
`κ(w)`. Every element of the node chart is a constant `κ` plus an element which is small on the
open segment and whose reductions vanish at all these branches (`exists_const_red`).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [Fintype (Ext C F')] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

omit [Fintype (Ext C F')] in
/-- Every element of the node chart is a constant plus an element which is small on the open
segment, has value `≤ 1` at every extension of the outer Gauss point, and whose reductions vanish
at all zeros of `x̄`. -/
theorem exists_const_red {c : C} (hc : ‖c‖ < 1) {a : RatFunc C} (ha : a ∈ nodeRing c) :
    ∃ κ : C, ‖κ‖ ≤ 1 ∧ (∀ s ∈ segment c, w s (a - algebraMap C (RatFunc C) κ) < 1) ∧
      ∀ v : Ext C F', v.1 (algebraMap (RatFunc C) F' (a - algebraMap C (RatFunc C) κ)) ≤ 1 ∧
        ∀ Q ∈ zeros 𝓀 (red C (xF C F') v),
          Q.valuation (red C (algebraMap (RatFunc C) F' (a - algebraMap C (RatFunc C) κ)) v) <
            1 := by
  induction ha using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, hb, rfl⟩ | rfl | rfl
    · refine ⟨b, ?_, fun s _ ↦ by simp, fun v ↦ ⟨by simp, fun Q _ ↦ by simp⟩⟩
      have : NormedField.valuation b ≤ 1 := hb
      rw [NormedField.valuation_apply] at this
      exact_mod_cast this
    · refine ⟨0, by simp, fun s hs ↦ by simp [hs.2], fun v ↦ ⟨?_, fun Q hQ ↦ ?_⟩⟩
      · simpa using (valuation_xF v).le
      · simpa using valuation_x_lt_one hQ
    · refine ⟨0, by simp, fun s hs ↦ ?_, fun v ↦ ?_⟩
      · rw [map_zero, sub_zero, map_div₀, gaussRat_C, gaussRat_X]
        exact (div_lt_one (by simp)).2 hs.1
      · have hlt : v.1 (algebraMap (RatFunc C) F'
            (algebraMap C (RatFunc C) c / RatFunc.X - algebraMap C (RatFunc C) 0)) < 1 := by
          rw [map_zero, sub_zero, valuation_algebraMap, map_div₀, gauss1_algebraMap_C, gauss1_X,
            div_one]
          exact_mod_cast hc
        refine ⟨hlt.le, fun Q _ ↦ ?_⟩
        rw [(red_eq_zero_iff hlt.le).2 hlt, map_zero]
        exact zero_lt_one
  | zero => exact ⟨0, by simp, fun s _ ↦ by simp, fun v ↦ ⟨by simp, fun Q _ ↦ by simp⟩⟩
  | one => exact ⟨1, by simp, fun s _ ↦ by simp, fun v ↦ ⟨by simp, fun Q _ ↦ by simp⟩⟩
  | add a b _ _ ha hb =>
    obtain ⟨κ, hκ, h1, h2⟩ := ha
    obtain ⟨κ', hκ', h1', h2'⟩ := hb
    have heq : a + b - algebraMap C (RatFunc C) (κ + κ') =
        (a - algebraMap C (RatFunc C) κ) + (b - algebraMap C (RatFunc C) κ') := by
      rw [map_add]; ring
    refine ⟨κ + κ', (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hκ hκ'),
      fun s hs ↦ ?_, fun v ↦ ?_⟩
    · rw [heq]
      exact (Valuation.map_add _ _ _).trans_lt (max_lt (h1 s hs) (h1' s hs))
    · obtain ⟨hv, hQ⟩ := h2 v
      obtain ⟨hv', hQ'⟩ := h2' v
      rw [heq, map_add]
      refine ⟨(Valuation.map_add _ _ _).trans (max_le hv hv'), fun Q hQz ↦ ?_⟩
      rw [red_add hv hv']
      exact (Valuation.map_add _ _ _).trans_lt (max_lt (hQ Q hQz) (hQ' Q hQz))
  | neg a _ ha =>
    obtain ⟨κ, hκ, h1, h2⟩ := ha
    have heq : -a - algebraMap C (RatFunc C) (-κ) = -(a - algebraMap C (RatFunc C) κ) := by
      rw [_root_.map_neg]; ring
    refine ⟨-κ, by simpa using hκ, fun s hs ↦ ?_, fun v ↦ ?_⟩
    · rw [heq, Valuation.map_neg]
      exact h1 s hs
    · obtain ⟨hv, hQ⟩ := h2 v
      rw [heq, _root_.map_neg, Valuation.map_neg]
      refine ⟨hv, fun Q hQz ↦ ?_⟩
      rw [red_neg hv, Valuation.map_neg]
      exact hQ Q hQz
  | mul a b _ _ ha hb =>
    obtain ⟨κ, hκ, h1, h2⟩ := ha
    obtain ⟨κ', hκ', h1', h2'⟩ := hb
    set u := a - algebraMap C (RatFunc C) κ
    set u' := b - algebraMap C (RatFunc C) κ'
    have heq : a * b - algebraMap C (RatFunc C) (κ * κ') =
        u * u' + algebraMap C (RatFunc C) κ * u' + algebraMap C (RatFunc C) κ' * u := by
      simp only [u, u', map_mul]; ring
    refine ⟨κ * κ', by rw [norm_mul]; exact mul_le_one₀ hκ (norm_nonneg _) hκ',
      fun s hs ↦ ?_, fun v ↦ ?_⟩
    · have hk : w s (algebraMap C (RatFunc C) κ) ≤ 1 := by
        rw [gaussRat_C]; exact_mod_cast hκ
      have hk' : w s (algebraMap C (RatFunc C) κ') ≤ 1 := by
        rw [gaussRat_C]; exact_mod_cast hκ'
      rw [heq]
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_add _ _ _).trans_lt
        (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (h1 s hs) (h1' s hs).le
      · exact mul_lt_one_of_nonneg_of_lt_one_right hk zero_le (h1' s hs)
      · exact mul_lt_one_of_nonneg_of_lt_one_right hk' zero_le (h1 s hs)
    · obtain ⟨hv, hQ⟩ := h2 v
      obtain ⟨hv', hQ'⟩ := h2' v
      have hk : v.1 (algebraMap C F' κ) ≤ 1 := by
        rw [valuation_algebraMap_C']; exact_mod_cast hκ
      have hk' : v.1 (algebraMap C F' κ') ≤ 1 := by
        rw [valuation_algebraMap_C']; exact_mod_cast hκ'
      have heq' : algebraMap (RatFunc C) F' (a * b - algebraMap C (RatFunc C) (κ * κ')) =
          algebraMap (RatFunc C) F' u * algebraMap (RatFunc C) F' u' +
            algebraMap C F' κ * algebraMap (RatFunc C) F' u' +
              algebraMap C F' κ' * algebraMap (RatFunc C) F' u := by
        rw [heq, map_add, map_add, map_mul, map_mul, map_mul,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      have hm1 := mul_le_one' hv hv'
      have hm2 := mul_le_one' hk hv'
      have hm3 := mul_le_one' hk' hv
      rw [heq']
      refine ⟨(Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
        (max_le (by rw [map_mul]; exact hm1) (by rw [map_mul]; exact hm2)))
          (by rw [map_mul]; exact hm3)), fun Q hQz ↦ ?_⟩
      rw [← map_mul] at hm1 hm2 hm3
      rw [red_add ((Valuation.map_add _ _ _).trans (max_le hm1 hm2)) hm3, red_add hm1 hm2,
        red_mul hv hv', red_mul hk hv', red_mul hk' hv]
      have hkQ : Q.valuation (red C (algebraMap C F' κ) v) ≤ 1 := by
        rw [red_algebraMap_C κ (by exact_mod_cast hκ)]
        exact Q.valuation_algebraMap_le_one _
      have hkQ' : Q.valuation (red C (algebraMap C F' κ') v) ≤ 1 := by
        rw [red_algebraMap_C κ' (by exact_mod_cast hκ')]
        exact Q.valuation_algebraMap_le_one _
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_add _ _ _).trans_lt
        (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hQ Q hQz) (hQ' Q hQz).le
      · exact mul_lt_one_of_nonneg_of_lt_one_right hkQ zero_le (hQ' Q hQz)
      · exact mul_lt_one_of_nonneg_of_lt_one_right hkQ' zero_le (hQ Q hQz)

/-- A root of a monic polynomial with coefficients of value `≤ 1` has value `≤ 1`. -/
lemma valuation_le_one_of_root {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation K Γ) {p : K[X]} (hm : p.Monic) (hc : ∀ i, u (p.coeff i) ≤ 1) {r : K}
    (hr : p.eval r = 0) : u r ≤ 1 := by
  have hO : (p.coeffs : Set K) ⊆ u.integer := fun a ha ↦ by
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 ha
    exact hc n
  refine (Valuation.integer.integers u).mem_of_integral
    ⟨p.toSubring _ hO, (monic_toSubring _ _ _).2 hm, ?_⟩
  rw [eval₂_eq_eval_map]
  change eval r ((p.toSubring _ hO).map (Subring.subtype _)) = 0
  rw [map_toSubring]
  exact hr

variable {c : C}

omit [Fintype (Ext C F')] in
lemma valuation_algebraMap_nodeRing_le (hc : ‖c‖ < 1) (v : Ext C F') {a : RatFunc C}
    (ha : a ∈ nodeRing c) : v.1 (algebraMap (RatFunc C) F' a) ≤ 1 := by
  obtain ⟨κ, hκ, -, h⟩ := exists_const_red (F' := F') hc ha
  have : algebraMap (RatFunc C) F' a = algebraMap (RatFunc C) F' (a - algebraMap C (RatFunc C) κ)
      + algebraMap C F' κ := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', ← map_add, sub_add_cancel]
  rw [this]
  refine (Valuation.map_add _ _ _).trans (max_le (h v).1 ?_)
  rw [valuation_algebraMap_C']
  exact_mod_cast hκ

omit [Fintype (Ext C F')] in
lemma red_algebraMap_nodeRing_mem (hc : ‖c‖ < 1) (v : Ext C F') {a : RatFunc C}
    (ha : a ∈ nodeRing c) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) :
    ∃ κ : HenselComplete.integers C,
      (∀ s ∈ segment c, w s (a - algebraMap C (RatFunc C) κ) < 1) ∧
      red C (algebraMap (RatFunc C) F' a) v ∈ Q.V ∧
      Q.res (red C (algebraMap (RatFunc C) F' a) v) = residue (HenselComplete.integers C) κ := by
  obtain ⟨κ, hκ, hs, h⟩ := exists_const_red (F' := F') hc ha
  obtain ⟨hv, hQv⟩ := h v
  have hk : v.1 (algebraMap C F' κ) ≤ 1 := by
    rw [valuation_algebraMap_C']; exact_mod_cast hκ
  have heq : red C (algebraMap (RatFunc C) F' a) v =
      red C (algebraMap (RatFunc C) F' (a - algebraMap C (RatFunc C) κ)) v +
        algebraMap 𝓀 _ (residue (HenselComplete.integers C)
          ⟨κ, (HenselComplete.mem_integers_iff κ).2 hκ⟩) := by
    rw [← red_algebraMap_C κ (by exact_mod_cast hκ), ← red_add hv hk, _root_.map_sub,
      ← IsScalarTower.algebraMap_apply, sub_add_cancel]
  refine ⟨⟨κ, (HenselComplete.mem_integers_iff κ).2 hκ⟩, hs, ?_, ?_⟩
  · rw [heq]
    exact add_mem (Q.valuation_le_one_iff.1 (hQv Q hQ).le) (Q.algebraMap_mem _)
  · rw [heq, Q.res_add (Q.valuation_le_one_iff.1 (hQv Q hQ).le) (Q.algebraMap_mem _),
      Q.res_eq_zero_of_lt_one (hQv Q hQ), zero_add, Q.res_algebraMap]

omit [Fintype (Ext C F')] in
lemma valuation_le_one_R (hc : ‖c‖ < 1) (v : Ext C F') (y : Rint c F') : v.1 (y : F') ≤ 1 := by
  let φ : nodeRing c →+* v.1.integer :=
    { toFun := fun a ↦ ⟨algebraMap (RatFunc C) F' a, valuation_algebraMap_nodeRing_le hc v a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hint : IsIntegral v.1.integer (y : F') :=
    IsIntegral.map_of_comp_eq φ (RingHom.id F') (by ext; rfl) y.2
  exact (Valuation.integer.integers v.1).mem_of_integral hint

omit [Fintype (Ext C F')] in
/-- Reductions of elements of `R'` are regular at the zeros of `x̄`. -/
lemma red_mem_V (hc : ‖c‖ < 1) (v : Ext C F') (y : Rint c F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : red C (y : F') v ∈ Q.V := by
  obtain ⟨p, hm, hp⟩ := y.2
  have hle (a : nodeRing c) : v.1 (algebraMap (RatFunc C) F' a) ≤ 1 :=
    valuation_algebraMap_nodeRing_le hc v a.2
  let ρ : nodeRing c →+* ResidueField v.1.valuationSubring :=
    { toFun := fun a ↦ red C (algebraMap (RatFunc C) F' a) v
      map_one' := by simp [red_one]
      map_mul' := fun a b ↦ by
        simp only [Subring.coe_mul, map_mul]
        exact red_mul (hle a) (hle b)
      map_zero' := by simp [red_zero]
      map_add' := fun a b ↦ by
        simp only [Subring.coe_add, map_add]
        exact red_add (hle a) (hle b) }
  have hy1 := valuation_le_one_R hc v y
  refine Q.valuation_le_one_iff.1 (valuation_le_one_of_root Q.valuation (hm.map ρ)
    (fun i ↦ ?_) ?_)
  · rw [coeff_map]
    obtain ⟨-, -, hmem, -⟩ := red_algebraMap_nodeRing_mem hc v (p.coeff i).2 hQ
    exact Q.valuation_le_one_iff.2 hmem
  · have hsum : eval₂ (algebraMap (nodeRing c) F') (y : F') p = ∑ i ∈ Finset.range
        (p.natDegree + 1), algebraMap (RatFunc C) F' (p.coeff i) * (y : F') ^ i := by
      rw [eval₂_eq_sum_range]
      rfl
    rw [eval_eq_sum_range, hm.natDegree_map]
    have h0 := congrArg (fun f ↦ red C f v) hp
    simp only [hsum, red_zero] at h0
    rw [red_sum _ _ fun i _ ↦ by rw [map_mul, map_pow]; exact mul_le_one' (hle _) (pow_le_one' hy1 _)] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_map, red_mul (hle _) (by rw [map_pow]; exact pow_le_one' hy1 _), red_pow hy1]
    rfl

end GaussTube

end SemistableReduction
