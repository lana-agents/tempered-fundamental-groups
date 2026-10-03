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
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

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

section Place


/-- The reduction of `R'` at a branch `Q` of the outer vertex through the node:
`y ↦ ȳ_v(Q)`. -/
noncomputable def placeHom (hc : ‖c‖ < 1) (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : Rint c F' →+* 𝓀 where
  toFun y := Q.res (red C (y : F') v)
  map_one' := by simp [Q.res_one]
  map_mul' y z := by
    simp only [Subalgebra.coe_mul]
    rw [red_mul (valuation_le_one_R hc v y) (valuation_le_one_R hc v z),
      Q.res_mul (red_mem_V hc v y hQ) (red_mem_V hc v z hQ)]
  map_zero' := by simp [Q.res_zero]
  map_add' y z := by
    simp only [Subalgebra.coe_add]
    rw [red_add (valuation_le_one_R hc v y) (valuation_le_one_R hc v z),
      Q.res_add (red_mem_V hc v y hQ) (red_mem_V hc v z hQ)]

lemma placeHom_apply (hc : ‖c‖ < 1) (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (y : Rint c F') : placeHom hc v hQ y = Q.res (red C (y : F') v) := rfl

lemma placeHom_algebraMap (hc : ‖c‖ < 1) (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (a : nodeRing c) :
    ∃ κ : HenselComplete.integers C,
      (∀ s ∈ segment c, w s ((a : RatFunc C) - algebraMap C (RatFunc C) κ) < 1) ∧
      placeHom hc v hQ (algebraMap (nodeRing c) (Rint c F') a) =
        residue (HenselComplete.integers C) κ := by
  obtain ⟨κ, hs, -, hres⟩ := red_algebraMap_nodeRing_mem hc v a.2 hQ
  exact ⟨κ, hs, hres⟩

lemma placeHom_surjective (hc : ‖c‖ < 1) (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : Function.Surjective (placeHom hc v hQ) := by
  intro t
  obtain ⟨κ, rfl⟩ := residue_surjective t
  have hmem : algebraMap C (RatFunc C) κ ∈ nodeRing c :=
    algebraMap_mem_nodeRing ((HenselComplete.mem_integers_iff _).1 κ.2)
  refine ⟨algebraMap (nodeRing c) (Rint c F') ⟨_, hmem⟩, ?_⟩
  rw [placeHom_apply]
  change Q.res (red C (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) κ)) v) = _
  rw [← IsScalarTower.algebraMap_apply,
    red_algebraMap_C (κ : C) (by exact_mod_cast (HenselComplete.mem_integers_iff _).1 κ.2),
    Q.res_algebraMap]

/-- The ideal of `R'` of the branch `Q`: a maximal ideal over the node. -/
noncomputable def placeIdeal (hc : ‖c‖ < 1) (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : Ideal (Rint c F') := RingHom.ker (placeHom hc v hQ)

lemma placeIdeal_isMaximal (hc : ‖c‖ < 1) (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) : (placeIdeal hc v hQ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (placeHom_surjective hc v hQ)

lemma mem_placeIdeal_iff (hc : ‖c‖ < 1) (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (y : Rint c F') :
    y ∈ placeIdeal hc v hQ ↔ Q.res (red C (y : F') v) = 0 := RingHom.mem_ker

end Place

section Curve

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ) {u : κ}

/-- The value at `0` of `r / X^{ord₀ r}`. -/
noncomputable def lead0 (r : k[X]) : k := (r /ₘ (X - Polynomial.C 0) ^ r.rootMultiplicity 0).eval 0

omit [IsAlgClosed k] in
lemma lead0_ne_zero {r : k[X]} (hr : r ≠ 0) : lead0 r ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hr

lemma res_aeval (hu : Q.valuation u < 1) (p : k[X]) : Q.res (aeval u p) = p.eval 0 := by
  refine Q.res_eq_of_valuation_sub_lt_one ?_
  have : aeval u p - algebraMap k κ (p.eval 0) = aeval u p.divX * u := by
    conv_lhs => rw [← divX_mul_X_add p]
    simp [coeff_zero_eq_eval_zero]
  rw [this, map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_right (valuation_aeval_le_one
    Q.valuation_algebraMap_le_one (hu.le) _) zero_le hu

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma aeval_eq_pow_mul (r : k[X]) :
    aeval u r = u ^ r.rootMultiplicity 0 * aeval u (r /ₘ (X - Polynomial.C 0) ^ r.rootMultiplicity 0) := by
  conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq r 0]
  simp

lemma valuation_aeval_div (hu : Q.valuation u < 1) (r : k[X]) :
    Q.valuation (aeval u (r /ₘ (X - Polynomial.C 0) ^ r.rootMultiplicity 0)) = 1 ∨ r = 0 := by
  by_cases hr : r = 0
  · exact Or.inr hr
  left
  have h := lead0_ne_zero hr
  have hres := res_aeval Q hu (r /ₘ (X - Polynomial.C 0) ^ r.rootMultiplicity 0)
  by_contra hne
  have hlt : Q.valuation (aeval u (r /ₘ (X - Polynomial.C 0) ^ r.rootMultiplicity 0)) < 1 :=
    lt_of_le_of_ne (valuation_aeval_le_one Q.valuation_algebraMap_le_one hu.le _) hne
  rw [Q.res_eq_zero_of_lt_one hlt] at hres
  exact h hres.symm

/-- Membership and value of `r(u) / s(u)` at a zero `Q` of `u`, in terms of the orders and
leading values of `r` and `s` at `0`. -/
theorem res_div_aeval (hu : Q.valuation u < 1) (hu0 : u ≠ 0) {r s : k[X]} (hr : r ≠ 0)
    (hs : s ≠ 0) :
    (aeval u r / aeval u s ∈ Q.V ↔ s.rootMultiplicity 0 ≤ r.rootMultiplicity 0) ∧
    (r.rootMultiplicity 0 = s.rootMultiplicity 0 →
      Q.res (aeval u r / aeval u s) = lead0 r / lead0 s) ∧
    (s.rootMultiplicity 0 < r.rootMultiplicity 0 → Q.res (aeval u r / aeval u s) = 0) := by
  set m := r.rootMultiplicity 0
  set n := s.rootMultiplicity 0
  set r1 := r /ₘ (X - Polynomial.C 0) ^ m
  set s1 := s /ₘ (X - Polynomial.C 0) ^ n
  have hm' : (m : ℤ) = (r.rootMultiplicity 0 : ℤ) := rfl
  have hn' : (n : ℤ) = (s.rootMultiplicity 0 : ℤ) := rfl
  have hr1 : Q.valuation (aeval u r1) = 1 := (valuation_aeval_div Q hu r).resolve_right hr
  have hs1 : Q.valuation (aeval u s1) = 1 := (valuation_aeval_div Q hu s).resolve_right hs
  have hs10 : aeval u s1 ≠ 0 := fun h ↦ by rw [h, map_zero] at hs1; exact zero_ne_one hs1
  have hv0 : Q.valuation u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hval : Q.valuation (aeval u r / aeval u s) = Q.valuation u ^ ((m : ℤ) - n) := by
    rw [aeval_eq_pow_mul r, aeval_eq_pow_mul s, map_div₀, map_mul, map_mul, hr1, hs1, mul_one,
      mul_one, map_pow, map_pow, zpow_sub₀ hv0, zpow_natCast, zpow_natCast]
  obtain ⟨e, he⟩ : ∃ e : ℤ, Q.valuation u = exp e := ⟨log (Q.valuation u), (exp_log hv0).symm⟩
  have he0 : e < 0 := by
    rw [he, ← exp_zero, exp_lt_exp] at hu
    exact hu
  refine ⟨?_, fun hmn ↦ ?_, fun hmn ↦ ?_⟩
  · rw [← Q.valuation_le_one_iff, hval, he, ← exp_zsmul, ← exp_zero, exp_le_exp, smul_eq_mul]
    constructor
    · intro h
      by_contra! H
      have : (m : ℤ) - n < 0 := by omega
      nlinarith
    · intro h
      have : (0 : ℤ) ≤ (m : ℤ) - n := by omega
      nlinarith
  · have heq : aeval u r / aeval u s = aeval u r1 / aeval u s1 := by
      rw [aeval_eq_pow_mul r, aeval_eq_pow_mul s]
      change u ^ m * aeval u r1 / (u ^ n * aeval u s1) = _
      rw [hmn, mul_div_mul_left _ _ (pow_ne_zero _ hu0)]
    have hmem1 : aeval u r1 ∈ Q.V := Q.valuation_le_one_iff.1 hr1.le
    have hmem2 : aeval u s1 ∈ Q.V := Q.valuation_le_one_iff.1 hs1.le
    have hq : aeval u r1 / aeval u s1 ∈ Q.V := by
      rw [← Q.valuation_le_one_iff, map_div₀, hr1, hs1, div_one]
    have := Q.res_mul hq hmem2
    rw [div_mul_cancel₀ _ hs10, res_aeval Q hu, res_aeval Q hu] at this
    rw [heq, lead0, lead0]
    change Q.res _ = r1.eval 0 / s1.eval 0
    rw [this]
    exact (mul_div_cancel_right₀ _ (lead0_ne_zero hs)).symm
  · refine Q.res_eq_zero_of_lt_one ?_
    rw [hval, he, ← exp_zsmul, ← exp_zero, exp_lt_exp, smul_eq_mul]
    have : (0 : ℤ) < (m : ℤ) - n := by omega
    nlinarith

end Curve

local notation "κ₁" => ResidueField (Valuation.valuationSubring (gauss1 C))

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
lemma red_xF_ne_zero' (v : Ext C F') : red C (xF C F') v ≠ 0 := by
  intro h
  have := transcendental_red_x (F := F') v
  rw [h] at this
  exact this (isAlgebraic_zero)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
lemma algebraMap_aeval_residue_X (v : Ext C F') (r : 𝓀[X]) :
    algebraMap κ₁ (ResidueField v.1.valuationSubring)
        (aeval (residue (gauss1 C).valuationSubring ⟨RatFunc.X, gauss1_mem_X⟩) r) =
      aeval (red C (xF C F') v) r := by
  rw [← algebraMap_residue_X v, ← IsScalarTower.coe_toAlgHom' 𝓀 κ₁,
    ← Polynomial.aeval_algHom_apply]

/-- **Values at `x̄ = 0` do not depend on the residue curve.** An element `a` of the residue
field `κ(w_{0,1}) = k(x̄)`, regular at a zero `Q` of `x̄` on one residue curve `κ(v)`, is regular
at every zero `Q'` of `x̄` on every residue curve `κ(v')`, with the same value. -/
theorem res_algebraMap_eq (a : κ₁) (v v' : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)} (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v))
    {Q' : CurvePlace 𝓀 (ResidueField v'.1.valuationSubring)}
    (hQ' : Q' ∈ zeros 𝓀 (red C (xF C F') v'))
    (ha : algebraMap κ₁ (ResidueField v.1.valuationSubring) a ∈ Q.V) :
    algebraMap κ₁ (ResidueField v'.1.valuationSubring) a ∈ Q'.V ∧
      Q'.res (algebraMap κ₁ (ResidueField v'.1.valuationSubring) a) =
        Q.res (algebraMap κ₁ (ResidueField v.1.valuationSubring) a) := by
  have hmem : a ∈ IntermediateField.adjoin 𝓀
      {residue (gauss1 C).valuationSubring ⟨RatFunc.X, gauss1_mem_X⟩} := by
    rw [adjoin_residue_X_eq_top]; trivial
  obtain ⟨r, s', rfl⟩ := (IntermediateField.mem_adjoin_simple_iff 𝓀 a).1 hmem
  simp only [map_div₀, algebraMap_aeval_residue_X] at ha ⊢
  by_cases hr : r = 0
  · simp [hr, Q'.res_zero, Q.res_zero]
  by_cases hs : s' = 0
  · simp [hs, Q'.res_zero, Q.res_zero]
  have h := res_div_aeval Q (valuation_x_lt_one hQ) (red_xF_ne_zero' v) hr hs
  have h' := res_div_aeval Q' (valuation_x_lt_one hQ') (red_xF_ne_zero' v') hr hs
  have hle := h.1.1 ha
  refine ⟨h'.1.2 hle, ?_⟩
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [h'.2.1 heq.symm, h.2.1 heq.symm]
  · rw [h'.2.2 hlt, h.2.2 hlt]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma red_algebraMap_rat (v : Ext C F') {φ : RatFunc C} (h : gauss1 C φ ≤ 1) :
    red C (algebraMap (RatFunc C) F' φ) v =
      algebraMap κ₁ (ResidueField v.1.valuationSubring) (residue _ ⟨φ, h⟩) := by
  have := red_algebraMap_mul φ h (by simp : v.1 (1 : F') ≤ 1)
  rwa [mul_one, red_one, mul_one] at this

lemma placeHom_const (hc : ‖c‖ < 1) (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (κ : HenselComplete.integers C) :
    placeHom hc v hQ (algebraMap (nodeRing c) (Rint c F')
      ⟨algebraMap C (RatFunc C) κ, algebraMap_mem_nodeRing
        ((HenselComplete.mem_integers_iff _).1 κ.2)⟩) =
      residue (HenselComplete.integers C) κ := by
  rw [placeHom_apply]
  change Q.res (red C (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) κ)) v) = _
  rw [← IsScalarTower.algebraMap_apply,
    red_algebraMap_C (κ : C) (by exact_mod_cast (HenselComplete.mem_integers_iff _).1 κ.2),
    Q.res_algebraMap]

/-- The norm from a residue curve to `κ(w_{0,1})`, evaluated at a zero `Q` of `x̄`: the
norm specialization (`PlaceNorm.res_norm_eq_prod`) transported along `κ(w_{0,1}) ≅ k(x̄)`. -/
theorem res_norm_residue (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) {z : ResidueField v.1.valuationSubring}
    (hz : ∀ Q' ∈ zeros 𝓀 (red C (xF C F') v), z ∈ Q'.V) :
    algebraMap κ₁ (ResidueField v.1.valuationSubring) (Algebra.norm κ₁ z) ∈ Q.V ∧
      Q.res (algebraMap κ₁ (ResidueField v.1.valuationSubring) (Algebra.norm κ₁ z)) =
        ∏ Q' ∈ zeros 𝓀 (red C (xF C F') v), Q'.res z ^ ord (red C (xF C F') v) Q' := by
  set E := 𝓀⟮red C (xF C F') v⟯
  have hinj : Function.Injective (algebraMap κ₁ (ResidueField v.1.valuationSubring)) :=
    RingHom.injective _
  let i : κ₁ ≃+* E :=
    RingEquiv.ofBijective ((algebraMap _ _ : _ →+* _).codRestrict E.toSubfield
      fun y ↦ (mem_adjoin_red_x_iff v _).2 ⟨y, rfl⟩)
      ⟨fun a b h ↦ hinj (congrArg Subtype.val h), fun z ↦ by
        obtain ⟨y, hy⟩ := (mem_adjoin_red_x_iff v z).1 z.2
        exact ⟨y, Subtype.ext hy⟩⟩
  have hnorm : (i (Algebra.norm κ₁ z) : ResidueField v.1.valuationSubring) =
      ((Algebra.norm E z : E) : ResidueField v.1.valuationSubring) := by
    rw [Algebra.norm_eq_of_ringEquiv i (by ext; rfl) z]
  have hx : red C (xF C F') v ∉ (algebraMap 𝓀 (ResidueField v.1.valuationSubring)).range :=
    fun ⟨a, ha⟩ ↦ transcendental_red_x (F := F') v (ha ▸ isAlgebraic_algebraMap a)
  have := PlaceNorm.res_norm_eq_prod hx hz hQ
  change ((i (Algebra.norm κ₁ z) : E) : ResidueField v.1.valuationSubring) ∈ Q.V ∧
    Q.res ((i (Algebra.norm κ₁ z) : E) : ResidueField v.1.valuationSubring) = _
  rw [hnorm]
  exact this

end GaussTube

end SemistableReduction
