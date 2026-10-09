/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourBranch

/-!
# Smoothness from a sheet in another coordinate

Blueprint §9.12, leaf T4, part (G). Let `e : G₂ ≃+* G₁` be one field with two coordinates: `x`
(on `G₁`, chart `R'₁ = DRint 0 1 G₁`) and `σ = e x₂` (chart `R'₂ = DRint 0 1 G₂`), with `σ` integral
over `C[x]` and `x` integral over `C[σ]`. Let `ξ` be a valuation with centres `P₁` on `R'₁` and
`P₂` on `R'₂`, where `P₂` has disc degree one (a sheet). Assume every component through `P₁` has
`|σ| ≤ 1` and one of them has `|σ| = 1`. Then `P₁` is smooth (`isDiscSmooth_of_sheet`):

1. (`res_iff`) for `y ∈ R'₂` and a branch `(v, Q)` through `P₁`: `ȳ ∈ O_Q`, and `y ∈ P₂` iff
   `ȳ(Q) = 0` (clear the components not through `P₁` and compare centres of `ξ`);
2. (`exists_branch₂`) a branch `(v, Q)` through `P₁` with `|σ|_v = 1` is a branch of the
   `σ`-chart through `P₂`: `v` is the Gauss valuation in `σ` (`v(σ - β) = max(1, |β|)`, as
   `σ - β ∈ P₂` forces `|β| < 1`), and the point of `Q` in `R'₂` is `P₂`;
3. a component `v` through `P₁` with `|σ|_v < 1` is impossible: its centre on `R'₂` is `P₂`, and
   `x`, cleared of the other components of `R'₂` (there is only one through `P₂`, of the sheet),
   lies in `P₂` but is a unit at `v`;
4. hence the branch correspondence of `ChartTransfer` holds, and `SheetSmooth` gives smoothness
   of `P₂`.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open FundamentalInequality GaussStability GaussFibre GaussTube DiscCount SmoothVertex PlaceNorm
  CurvePlace

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {G₁ G₂ : Type*} [Field G₁] [Algebra (RatFunc C) G₁] [Algebra C G₁]
  [IsScalarTower C (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₁]
  [Algebra.IsSeparable (RatFunc C) G₁]
  [Field G₂] [Algebra (RatFunc C) G₂] [Algebra C G₂]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₂]
  [Algebra.IsSeparable (RatFunc C) G₂]
  (e : G₂ ≃+* G₁) (he : ∀ c : C, e.symm (algebraMap C G₁ c) = algebraMap C G₂ c)

omit [Algebra.IsSeparable (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂]
  [Algebra.IsSeparable (RatFunc C) G₂] in
include hp hp1 he in
/-- **Step 1.** For `y ∈ R'₂` and a branch `(v, Q)` through `P₁`: `ē y ∈ O_Q`, and `y ∈ P₂` iff
`(e y)‾(Q) = 0`. -/
theorem res_iff (hσ : IsIntegral (Algebra.adjoin C {xF C G₁}) (e (xF C G₂)))
    {ξ : Valuation G₁ ℝ≥0} {P₁ : Ideal (DRint (0 : C) 1 G₁)}
    (hξ₁ : ∀ y : DRint (0 : C) 1 G₁, y ∈ P₁ ↔ ξ (y : G₁) < 1)
    (hξ₁le : ∀ y : DRint (0 : C) 1 G₁, ξ (y : G₁) ≤ 1)
    {P₂ : Ideal (DRint (0 : C) 1 G₂)}
    (hξ₂ : ∀ y : DRint (0 : C) 1 G₂, y ∈ P₂ ↔ ξ (e y) < 1)
    {z : DRint (0 : C) 1 G₁} (hzP : z ∉ P₁) (hz : ∀ v : Ext C G₁, ¬ Through P₁ v → v.1 (z : G₁) < 1)
    (hle : ∀ v : Ext C G₁, Through P₁ v → ∀ y : DRint (0 : C) 1 G₂, v.1 (e y) ≤ 1)
    (y : DRint (0 : C) 1 G₂) (v : Ext C G₁) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₁) v)) (hP : placeIdealD v hQ = P₁) :
    red C (e y) v ∈ Q.V ∧ (y ∈ P₂ ↔ Q.res (red C (e y) v) = 0) := by
  obtain ⟨N, hN⟩ := exists_lift' hp hp1 hz (isIntegral_e e he hσ y) fun v hv ↦ hle v hv y
  set Y : DRint (0 : C) 1 G₁ := ⟨_, hN N le_rfl⟩
  obtain ⟨hvz, -⟩ := valuation_eq_one_of_notMem hzP hP
  have hQz : Q.valuation (red C (z : G₁) v) = 1 := (notMem_placeIdealD_iff v hQ z).1 (hP ▸ hzP)
  have hredY : red C (Y : G₁) v = red C (z : G₁) v ^ N * red C (e y) v := by
    change red C ((z : G₁) ^ N * e y) v = _
    rw [red_mul (by rw [map_pow, hvz, one_pow]) (hle v ⟨Q, hQ, hP⟩ y), red_pow (le_of_eq hvz)]
  have hYV : red C (Y : G₁) v ∈ Q.V := redD_mem_V v Y (xbar_mem_V v hQ)
  rw [hredY] at hYV
  obtain ⟨hV, hiff⟩ := mem_and_res_iff Q hQz N hYV
  refine ⟨hV, ?_⟩
  have hξz : ξ (z : G₁) = 1 := le_antisymm (hξ₁le z) (not_lt.1 fun h ↦ hzP ((hξ₁ z).2 h))
  rw [hξ₂, ← hiff, ← hredY, ← redD_apply, ← mem_placeIdealD_iff v hQ, hP, hξ₁]
  change _ ↔ ξ ((z : G₁) ^ N * e y) < 1
  rw [map_mul, map_pow, hξz, one_pow, one_mul]

omit [Algebra.IsSeparable (RatFunc C) G₁] [Algebra.IsSeparable (RatFunc C) G₂] in
include hp hp1 he in
/-- **Step 2.** A branch through `P₁` with `|σ| = 1` is a branch of the `σ`-chart through `P₂`. -/
theorem exists_branch₂ (hσ : IsIntegral (Algebra.adjoin C {xF C G₁}) (e (xF C G₂)))
    {ξ : Valuation G₁ ℝ≥0} {P₁ : Ideal (DRint (0 : C) 1 G₁)}
    (hξ₁ : ∀ y : DRint (0 : C) 1 G₁, y ∈ P₁ ↔ ξ (y : G₁) < 1)
    (hξ₁le : ∀ y : DRint (0 : C) 1 G₁, ξ (y : G₁) ≤ 1)
    {P₂ : Ideal (DRint (0 : C) 1 G₂)} [hP₂ : P₂.IsMaximal]
    (hc₂ : P₂.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) =
      discIdeal (0 : C) 1)
    (hξ₂ : ∀ y : DRint (0 : C) 1 G₂, y ∈ P₂ ↔ ξ (e y) < 1)
    {z : DRint (0 : C) 1 G₁} (hzP : z ∉ P₁) (hz : ∀ v : Ext C G₁, ¬ Through P₁ v → v.1 (z : G₁) < 1)
    (hle : ∀ v : Ext C G₁, Through P₁ v → ∀ y : DRint (0 : C) 1 G₂, v.1 (e y) ≤ 1)
    (v : Ext C G₁) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₁) v)) (hP : placeIdealD v hQ = P₁)
    (hv1 : v.1 (e (xF C G₂)) = 1) :
    ∃ (v₂ : Ext C G₂) (h : ∀ y : G₁, v₂.1 (e.symm y) = v.1 y)
      (hQ₂ : Q.map (resAlgEquiv e.symm he h) ∈ zeros 𝓀 (red C (xF C G₂) v₂)),
      placeIdealD v₂ hQ₂ = P₂ := by
  have step := res_iff hp hp1 e he hσ hξ₁ hξ₁le hξ₂ hzP hz hle
  have hx₂P : (xD : DRint (0 : C) 1 G₂) ∈ P₂ := xD_mem hc₂
  have hvC : ∀ c : C, v.1 (e (algebraMap C G₂ c)) = ‖c‖₊ := fun c ↦ by
    rw [e_algebraMap e he, valuation_algebraMap_C']
  -- `v` is the Gauss valuation in `σ`
  have hlin : ∀ β : C, v.1 (e (xF C G₂) - algebraMap C G₁ β) = max ‖β‖₊ 1 := by
    intro β
    by_cases hβ : ‖β‖ ≤ 1
    · have hβ' : ‖β‖₊ ≤ 1 := by exact_mod_cast hβ
      rw [max_eq_right hβ']
      refine le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hv1.le
        (by rw [valuation_algebraMap_C']; exact hβ'))) (not_lt.1 fun hlt ↦ ?_)
      set βO : HenselComplete.integers C := ⟨β, (HenselComplete.mem_integers_iff _).2 hβ⟩
      have hred : red C (e ((xD - constD βO : DRint (0 : C) 1 G₂) : G₂)) v = 0 := by
        rw [red_eq_zero_iff]
        · change v.1 (e (xF C G₂ - algebraMap (RatFunc C) G₂ (algebraMap C (RatFunc C) β))) < 1
          rwa [← IsScalarTower.algebraMap_apply, _root_.map_sub, e_algebraMap e he]
        · change v.1 (e (xF C G₂ - algebraMap (RatFunc C) G₂ (algebraMap C (RatFunc C) β))) ≤ 1
          rw [← IsScalarTower.algebraMap_apply, _root_.map_sub, e_algebraMap e he]
          exact hlt.le
      have hmem := (step (xD - constD βO) v Q hQ hP).2.2 (by rw [hred, Q.res_zero])
      have hcP : constD βO ∈ P₂ := by
        have := P₂.sub_mem hx₂P hmem
        rwa [sub_sub_cancel] at this
      have hdisc : (⟨algebraMap C (RatFunc C) β, algebraMap_mem_discRing' βO⟩ :
          discRing (0 : C) 1) ∈ discIdeal (0 : C) 1 := by
        rw [← hc₂, Ideal.mem_comap]; exact hcP
      rw [mem_discIdeal_iff discValHalf.isDiscVal] at hdisc
      change discValHalf.val (algebraMap C (RatFunc C) β) < 1 at hdisc
      rw [discValHalf.isDiscVal.map_C] at hdisc
      have hlt' : v.1 (e (xF C G₂)) < 1 := by
        rw [show e (xF C G₂) = (e (xF C G₂) - algebraMap C G₁ β) + algebraMap C G₁ β by ring]
        exact (Valuation.map_add _ _ _).trans_lt (max_lt hlt
          (by rw [valuation_algebraMap_C']; exact hdisc))
      exact absurd hv1 hlt'.ne
    · have hβ' : 1 < ‖β‖₊ := by exact_mod_cast not_le.1 hβ
      rw [max_eq_left hβ'.le, Valuation.map_sub_eq_of_lt_right _
        (by rw [hv1, valuation_algebraMap_C']; exact hβ'), valuation_algebraMap_C']
  set w := v.1.comap e.toRingHom
  have hw : w.comap (algebraMap (RatFunc C) G₂) =
      gaussRat (NormedField.valuation (K := C)) 0 1 := by
    refine valuation_ratFunc_ext_of_linear (fun c ↦ ?_) fun β ↦ ?_
    · simp only [Valuation.comap_apply, w]
      rw [← IsScalarTower.algebraMap_apply]
      change v.1 (e (algebraMap C G₂ c)) = _
      rw [hvC, gaussRat_algebraMap_C, NormedField.valuation_apply]
    · rw [gaussRat_algebraMap, gauss_X_sub_C, zero_sub, Valuation.map_neg,
        NormedField.valuation_apply, max_comm]
      simp only [Valuation.comap_apply, w]
      rw [_root_.map_sub, _root_.map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C,
        _root_.map_sub, ← IsScalarTower.algebraMap_apply]
      change v.1 (e (xF C G₂) - e (algebraMap C G₂ β)) = _
      rw [e_algebraMap e he, hlin, max_comm, Units.val_one]
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : Ext C G₂, v₂.1 = w := ⟨⟨w, hw⟩, rfl⟩
  have h : ∀ y : G₁, v₂.1 (e.symm y) = v.1 y := fun y ↦ by
    rw [hv₂]
    change v.1 (e (e.symm y)) = _
    rw [RingEquiv.apply_symm_apply]
  set ε := resAlgEquiv e.symm he h
  have hεred : ∀ y : G₂, ε (red C (e y) v) = red C y v₂ := fun y ↦ by
    rw [resAlgEquiv_red, RingEquiv.symm_apply_apply]
  -- the transported place is a zero of `σ̄`
  obtain ⟨hxV, hxres⟩ := step xD v Q hQ hP
  have hx0 : Q.res (red C (e (xF C G₂)) v) = 0 := hxres.1 hx₂P
  have hxV' : red C (e (xF C G₂)) v ∈ Q.V := hxV
  have hxlt : Q.valuation (red C (e (xF C G₂)) v) < 1 := by
    have := Q.valuation_sub_res_lt_one hxV'
    rwa [hx0, map_zero, sub_zero] at this
  have hQ₂ : Q.map ε ∈ zeros 𝓀 (red C (xF C G₂) v₂) := by
    rw [mem_zeros]
    intro hinv
    have h1 := (Q.map ε).valuation_le_one_iff.2 hinv
    rw [map_inv₀, valuation_map, ← hεred, AlgEquiv.symm_apply_apply] at h1
    have h2 := inv_le_one₀ ((Valuation.pos_iff _).2 fun h0 ↦ red_xF_ne_zero' v₂ (by
      rw [← hεred, h0, map_zero])) |>.1 h1
    exact absurd hxlt (not_lt.2 h2)
  refine ⟨v₂, h, hQ₂, (hP₂.eq_of_le (placeIdealD_isMaximal v₂ hQ₂).ne_top fun y hy ↦ ?_).symm⟩
  obtain ⟨hyV, hyres⟩ := step y v Q hQ hP
  rw [mem_placeIdealD_iff, redD_apply, ← hεred, res_map ε Q (by
    rw [mem_map_V, AlgEquiv.symm_apply_apply]; exact hyV), AlgEquiv.symm_apply_apply]
  exact hyres.1 hy

include hp hp1 he in
/-- **Smoothness from a sheet in another coordinate.** -/
theorem isDiscSmooth_of_sheet (hσ : IsIntegral (Algebra.adjoin C {xF C G₁}) (e (xF C G₂)))
    (hτ : IsIntegral (Algebra.adjoin C {xF C G₂}) (e.symm (xF C G₁)))
    {ξ : Valuation G₁ ℝ≥0} {P₁ : Ideal (DRint (0 : C) 1 G₁)} [hP₁ : P₁.IsMaximal]
    (hc₁ : P₁.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₁)) =
      discIdeal (0 : C) 1)
    (hξ₁ : ∀ y : DRint (0 : C) 1 G₁, y ∈ P₁ ↔ ξ (y : G₁) < 1)
    (hξ₁le : ∀ y : DRint (0 : C) 1 G₁, ξ (y : G₁) ≤ 1)
    {P₂ : Ideal (DRint (0 : C) 1 G₂)} [hP₂ : P₂.IsMaximal]
    (hc₂ : P₂.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) =
      discIdeal (0 : C) 1)
    (hξ₂ : ∀ y : DRint (0 : C) 1 G₂, y ∈ P₂ ↔ ξ (e y) < 1)
    (hξ₂le : ∀ y : DRint (0 : C) 1 G₂, ξ (e y) ≤ 1)
    (hdeg : ∃ ν : DiscVal (0 : C) 1, discDegree ν P₂ = 1)
    (hH : ∀ v : Ext C G₁, Through P₁ v → v.1 (e (xF C G₂)) ≤ 1)
    (hH' : ∃ v : Ext C G₁, Through P₁ v ∧ v.1 (e (xF C G₂)) = 1) :
    IsDiscSmooth P₁ := by
  classical
  haveI : Finite (Ext C G₁) := finite_ext (F := G₁) hp hp1
  haveI : Finite (Ext C G₂) := finite_ext (F := G₂) hp hp1
  obtain ⟨z, hzP, hz⟩ := exists_away' P₁ hc₁
  have hle : ∀ v : Ext C G₁, Through P₁ v → ∀ y : DRint (0 : C) 1 G₂, v.1 (e y) ≤ 1 :=
    fun v hv y ↦ val_le_one_of_xF (w := v.1.comap e.toRingHom) (fun c hc ↦ by
      rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]
      change v.1 (e (algebraMap C G₂ c)) ≤ 1
      rw [e_algebraMap e he, valuation_algebraMap_C']
      exact_mod_cast hc) (hH v hv) y
  have step := res_iff hp hp1 e he hσ hξ₁ hξ₁le hξ₂ hzP hz hle
  have step2 := exists_branch₂ hp hp1 e he hσ hξ₁ hξ₁le hc₂ hξ₂ hzP hz hle
  -- the unique branch of the sheet
  obtain ⟨ν, hν⟩ := hdeg
  obtain ⟨b₂, hS₂, -⟩ := exists_branch_of_discDegree_eq_one hp hp1 ν P₂ hν
  obtain ⟨v₀, ⟨Q₀, hQ₀, hP₀⟩, hv₀⟩ := hH'
  obtain ⟨v₂₀, hv₂₀, hQ₂₀, hP₂₀⟩ := step2 v₀ Q₀ hQ₀ hP₀ hv₀
  have hthrough : ∀ w : Ext C G₂, Through P₂ w → w = v₂₀ := by
    rintro w ⟨Q, hQ, hQP⟩
    have h1 : (⟨w, Q, hQ⟩ : OuterBranch C G₂) ∈ discBranches P₂ := hQP
    have h2 : (⟨v₂₀, _, hQ₂₀⟩ : OuterBranch C G₂) ∈ discBranches P₂ := hP₂₀
    rw [hS₂, Set.mem_singleton_iff] at h1 h2
    exact congrArg Sigma.fst (h1.trans h2.symm)
  -- `x` cleared of the components of the `σ`-chart not through `P₂`
  obtain ⟨z₂, hz₂P, hz₂⟩ := exists_away' P₂ hc₂
  obtain ⟨N₂, hN₂⟩ := exists_lift' hp hp1 hz₂ hτ fun w hw ↦ by
    rw [hthrough w hw, hv₂₀, valuation_xF]
  set Y₂ : DRint (0 : C) 1 G₂ := ⟨_, hN₂ N₂ le_rfl⟩
  have hY₂ : Y₂ ∈ P₂ := by
    rw [hξ₂]
    change ξ (e ((z₂ : G₂) ^ N₂ * e.symm (xF C G₁))) < 1
    rw [map_mul, RingEquiv.apply_symm_apply, map_mul, map_pow, map_pow]
    refine mul_lt_one_of_nonneg_of_lt_one_right (pow_le_one' (hξ₂le z₂) _) zero_le ?_
    exact (hξ₁ xD).1 (xD_mem hc₁)
  -- every component through `P₁` has `|σ| = 1`
  have step3 : ∀ v : Ext C G₁, Through P₁ v → v.1 (e (xF C G₂)) = 1 := by
    rintro v ⟨Q, hQ, hP⟩
    by_contra hne
    have hlt : v.1 (e (xF C G₂)) < 1 := lt_of_le_of_ne (hH v ⟨Q, hQ, hP⟩) hne
    set w := v.1.comap e.toRingHom
    have hdisc : IsDiscVal (0 : C) 1 (w.comap (algebraMap (RatFunc C) G₂)) := by
      refine ⟨fun c ↦ ?_, ?_⟩
      · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]
        change v.1 (e (algebraMap C G₂ c)) = _
        rw [e_algebraMap e he, valuation_algebraMap_C']
      · rw [Valuation.comap_apply, SmoothVertex.gaussCoord_zero_one]
        exact hlt
    have hcen : center hdisc = P₂ := by
      refine (center_isMaximal one_ne_zero hdisc).eq_of_le hP₂.ne_top fun y hy ↦ ?_
      rw [DiscCount.mem_center_iff] at hy
      have hy' : v.1 (e y) < 1 := hy
      refine ((step y v Q hQ hP).2).2 ?_
      rw [(red_eq_zero_iff (hle v ⟨Q, hQ, hP⟩ y)).2 hy', Q.res_zero]
    have hYc : Y₂ ∈ center hdisc := hcen ▸ hY₂
    rw [DiscCount.mem_center_iff] at hYc
    have hz₂v : v.1 (e z₂) = 1 := by
      refine le_antisymm (hle v ⟨Q, hQ, hP⟩ z₂) (not_lt.1 fun h ↦ hz₂P ?_)
      rw [← hcen, DiscCount.mem_center_iff]
      exact h
    change v.1 (e ((z₂ : G₂) ^ N₂ * e.symm (xF C G₁))) < 1 at hYc
    rw [map_mul, RingEquiv.apply_symm_apply, map_mul, map_pow, map_pow, hz₂v, one_pow, one_mul,
      valuation_xF] at hYc
    exact lt_irrefl 1 hYc
  exact chartTransfer hp hp1 e he hσ P₁ P₂ hP₁ hP₂ hc₁ hc₂
    (fun v₁ Q₁ hQ₁ hP ↦ step2 v₁ Q₁ hQ₁ hP (step3 v₁ ⟨Q₁, hQ₁, hP⟩))
    (sheetSmooth hp hp1 G₂ ν P₂ hc₂ hν)

end TypeFour

end SemistableReduction
