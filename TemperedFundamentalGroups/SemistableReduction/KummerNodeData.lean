/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerAnnulus
import TemperedFundamentalGroups.SemistableReduction.NearBoundary
import TemperedFundamentalGroups.SemistableReduction.DVRDescentKernel

/-!
# Node parameters over a Kummer sheet

Blueprint §9.10, L4 (K6, exhaustion, purely inseparable case). Over the annulus
`|l c₀ c| ≤ |x - a| ≤ |l c|` of the sheet `P'` (node chart `Rint c₀ (Aff a (l c) F')`), with Kummer
data `θ^p = f` whose index `m` strictly dominates `f̃ - h̃^p` at both radii, the element
`w = (θ - h̃(t))/λ` satisfies `w^p ≡ ḡ x^m` at the outer vertex, so `x̄` has order `p` and `w̄`
order `m` at the unique outer branch.

* `toAff_gaussCoord`: `t = l x` in the twist;
* `outer_dominant`: `v w = 1`, `v(w^p - c_m x^m) < 1` with `‖c_m‖ = 1`;
* `outer_orders`: `ord_Q x̄ = p`, `ord_Q w̄ = m` at the unique outer branch;
* `kumW_value`, `inner_val_W`: `μ(w)^p = ‖e‖^m` at the inner vertices over the inner sheet;
* `exists_sep`, `exists_S`: an element of `R' ∖ P'` small at the vertices off the sheets;
* **`exists_nodeData`**: exact node data (`GaussTube.NodeData`) with coordinate
  `u = w^α / x^β`, `α m = β p + 1`;
* **`isNodeODP_kummer`**: every point of the node chart over the node and over the sheet is an
  ordinary double point (via `isNodeODP_of_le`).
-/

open Polynomial NNReal WithZero

namespace SemistableReduction

namespace KummerAnnulus

open DiscCount GaussTube GaussFibre AffineTwist KummerSheet PlaceNorm

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {L : Type*} [Field L] [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra L F'] [IsScalarTower (RatFunc C) L F']
  [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {a c : C} (hc : c ≠ 0) (ν₀ : DiscVal a c) (P' : Ideal (DRint a c L)) [P'.IsMaximal]
  (h1 : discDegree ν₀ P' = 1) {l : C} (hl0 : l ≠ 0) (hl1 : ‖l‖ < 1)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L F'] [IsScalarTower (RatFunc C) L F'] [FiniteDimensional (RatFunc C) F']
  [Algebra (RatFunc C) L] in
/-- In the twist `Aff a (l c)`, the disc coordinate `t = (x - a)/c` is `l x`. -/
lemma toAff_gaussCoord :
    toAff (mul_ne_zero hl0 hc) (algebraMap (RatFunc C) F' (gaussCoord a c)) =
      algebraMap C (Aff a (l * c) (mul_ne_zero hl0 hc) F') l *
        xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') := by
  rw [xF_aff, KummerSheet.gaussCoord_mul (c := c) hl0, map_mul, map_mul, mul_comm c l,
    ← IsScalarTower.algebraMap_apply]
  rfl

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L F'] [IsScalarTower (RatFunc C) L F'] [FiniteDimensional (RatFunc C) F']
  [Algebra (RatFunc C) L] in
/-- The disc chart `O_C[t]` lands in `C[x]` of the twist. -/
lemma toAff_mem_adjoin {φ : RatFunc C} (hφ : φ ∈ discRing a c) :
    toAff (mul_ne_zero hl0 hc) (algebraMap (RatFunc C) F' φ) ∈
      Algebra.adjoin C {xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')} := by
  obtain ⟨Q, -, rfl⟩ := mem_polyChart_iff.1 hφ
  have h : toAff (a := a) (mul_ne_zero hl0 hc)
      (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) Q)) =
      aeval (toAff (a := a) (mul_ne_zero hl0 hc)
        (algebraMap (RatFunc C) F' (gaussCoord a c))) Q := by
    rw [aeval_eq_sum_range, aeval_eq_sum_range, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_pow, map_pow,
      ← IsScalarTower.algebraMap_apply]
    rfl
  have hX : algebraMap C (Aff a (l * c) (mul_ne_zero hl0 hc) F') l *
      xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') =
      aeval (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) (Polynomial.C l * X) := by
    simp
  rw [h, toAff_gaussCoord hc hl0, hX, ← aeval_comp]
  exact aeval_mem_adjoin_singleton C _

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L F'] [IsScalarTower (RatFunc C) L F'] [FiniteDimensional (RatFunc C) F']
  [Algebra (RatFunc C) L] in
/-- Elements integral over the disc chart are integral over `C[x]` in the twist. -/
lemma isIntegral_adjoin_of_discRing {y : F'} (hy : IsIntegral (discRing a c) y) :
    IsIntegral (Algebra.adjoin C {xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')})
      (toAff (a := a) (mul_ne_zero hl0 hc) y) := by
  set ψ : discRing a c →+* Algebra.adjoin C {xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')} :=
    { toFun := fun φ ↦ ⟨_, toAff_mem_adjoin hc hl0 φ.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp }
  exact IsIntegral.map_of_comp_eq ψ (toAff (a := a) (mul_ne_zero hl0 hc)).toRingHom
    (RingHom.ext fun φ ↦ rfl) hy

variable (p : ℕ) [Fact p.Prime] (γ : C) (θ : F') (f : L)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- **The residue relation at the outer vertex**: with strict dominance of `m`,
`v w = 1` and `v(w^p - c_m x^m) < 1` for `c_m = G_m l^m / λ^p`, `‖c_m‖ = 1`. -/
theorem outer_dominant (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f)
    (hstrict : ∀ i, i ≠ D.m → ‖(D.f' - D.h' ^ p).coeff i‖ * ‖l‖ ^ i < ‖D.lam‖ ^ p)
    (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (hvS : v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1) :
    v.1 (toAff (mul_ne_zero hl0 hc) (kumW L a c θ D.h' D.lam)) = 1 ∧
      v.1 (toAff (mul_ne_zero hl0 hc) (kumW L a c θ D.h' D.lam) ^ p -
        algebraMap C _ ((D.f' - D.h' ^ p).coeff D.m / D.lam ^ p * l ^ D.m) *
          xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') ^ D.m) < 1 ∧
      ‖(D.f' - D.h' ^ p).coeff D.m / D.lam ^ p * l ^ D.m‖ = 1 := by
  set e := (toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom
  set v' := v.1.comap e
  have hv' : v'.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0 hl1).1 := by
    rw [← Valuation.comap_comp]; exact hvS
  obtain ⟨hw1, hred, -⟩ := insep_value hc ν₀ P' h1 hl0 hl1 p hγ v' hv' hθ D.hh' D.hγl D.hl1'
    D.hGle D.hGm D.hf
  have hlam0 : D.lam ≠ 0 := nnnorm_ne_zero_iff.1 (lt_of_le_of_lt zero_le D.hγl).ne'
  have hdom := kumX_dominant hc ν₀ P' h1 hl0 hl1 p hlam0 hstrict
  rw [← hv', Valuation.comap_apply] at hdom
  set b := (D.f' - D.h' ^ p).coeff D.m / D.lam ^ p
  -- the monomial in the twist
  have hmon : e (algebraMap L F' (algebraMap (RatFunc C) L
      (algebraMap C (RatFunc C) b * gaussCoord a c ^ D.m))) =
      algebraMap C _ (b * l ^ D.m) * xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') ^ D.m := by
    rw [← IsScalarTower.algebraMap_apply, map_mul, map_mul, map_pow, map_pow]
    change toAff (mul_ne_zero hl0 hc) (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) b)) *
      toAff (mul_ne_zero hl0 hc) (algebraMap (RatFunc C) F' (gaussCoord a c)) ^ D.m = _
    rw [toAff_gaussCoord hc hl0, mul_pow, ← mul_assoc, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply]
    rfl
  refine ⟨hw1, ?_, ?_⟩
  · rw [← hmon]
    have h2 : v' (kumW L a c θ D.h' D.lam ^ p - algebraMap L F' (algebraMap (RatFunc C) L
        (algebraMap C (RatFunc C) b * gaussCoord a c ^ D.m))) < 1 := by
      have := Valuation.map_add v' (kumW L a c θ D.h' D.lam ^ p -
        algebraMap L F' (kumX p a c D.f' D.h' D.lam)) (algebraMap L F' (kumX p a c D.f' D.h' D.lam -
          algebraMap (RatFunc C) L (algebraMap C (RatFunc C) b * gaussCoord a c ^ D.m)))
      rw [map_sub (algebraMap L F'), sub_add_sub_cancel] at this
      exact this.trans_lt (max_lt hred (by rwa [← map_sub]))
    change v' _ < 1 at h2
    simpa [v', e, map_sub, map_pow] using h2
  · have hGm := D.hGm
    have hl : 0 < ‖D.lam‖ ^ p := pow_pos (norm_pos_iff.2 hlam0) _
    simp only [b, norm_mul, norm_div, norm_pow]
    rw [div_mul_eq_mul_div, div_eq_one_iff_eq hl.ne']
    exact hGm

section Orders

open IntermediateField IsLocalRing

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- **Orders at the outer branch**: at the zero `Q` of `x̄` over the sheet, `ord_Q x̄ = p` and
`ord_Q w̄ = m`. -/
theorem outer_orders [FiniteDimensional L F'] (hp1 : ‖(p : C)‖ < 1)
    (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f)
    (hstrict : ∀ i, i ≠ D.m → ‖(D.f' - D.h' ^ p).coeff i‖ * ‖l‖ ^ i < ‖D.lam‖ ^ p)
    (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (hvS : v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v)) :
    ord (red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v) Q = p ∧
      Q.valuation (red C (toAff (mul_ne_zero hl0 hc) (kumW L a c θ D.h' D.lam)) v) =
        exp (-(D.m : ℤ)) := by
  set F₁ := Aff a (l * c) (mul_ne_zero hl0 hc) F'
  set X := xF C F₁
  set W := toAff (mul_ne_zero hl0 hc) (kumW L a c θ D.h' D.lam)
  set cm := (D.f' - D.h' ^ p).coeff D.m / D.lam ^ p * l ^ D.m
  obtain ⟨hW1, hWred, hcm⟩ := outer_dominant hc ν₀ P' h1 hl0 hl1 p γ θ f hγ hθ D hstrict v hvS
  have hpp := (Fact.out : p.Prime)
  have hX1 : v.1 X = 1 := valuation_xF v
  have hx0 : red C X v ≠ 0 := fun h0 ↦ transcendental_red_x v (by
    rw [h0]; exact isAlgebraic_zero)
  -- `ord_Q x̄ ∣ p`
  have hdvd : ord (red C X v) Q ∣ p := by
    obtain ⟨π, hπ⟩ := Q.exists_valuation_eq_exp_neg_one
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact exp_ne_zero hπ.symm
    have ha : (⟨π ^ p, outer_pow_mem_adjoin hc ν₀ P' h1 hl0 hl1 p γ θ f hp1 hγ hθ hspan D v
      hvS π⟩ : 𝓀⟮red C X v⟯) ≠ 0 := fun h ↦ hπ0 (pow_eq_zero_iff hpp.ne_zero |>.1 congr($h.1))
    have h := valuation_eq_expo hx0 ha hQ
    simp only [map_pow, hπ, ← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one, exp_inj] at h
    have : ((ord (red C X v) Q : ℕ) : ℤ) ∣ (p : ℤ) := ⟨expo (red C X v) _, by linarith⟩
    exact Int.natCast_dvd_natCast.1 this
  -- the residue relation `ȳ^p = c̄ x̄^m`
  have hcm' : ‖cm‖ = 1 := hcm
  have hcm1 : ‖cm‖₊ ≤ 1 := by rw [← NNReal.coe_le_coe]; simp [hcm']
  have hC1 : v.1 (algebraMap C F₁ cm) = 1 := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F₁, valuation_algebraMap, gauss1_algebraMap_C]
    rw [← NNReal.coe_inj]; simpa using hcm'
  have hrel : red C W v ^ p = algebraMap 𝓀 _ (residue (HenselComplete.integers C)
      ⟨cm, by simpa using hcm1⟩) * red C X v ^ D.m := by
    have hle : v.1 (algebraMap C F₁ cm * X ^ D.m) ≤ 1 := by
      rw [map_mul, map_pow, hC1, hX1, one_pow, one_mul]
    have hWp : v.1 (W ^ p) ≤ 1 := by rw [map_pow, hW1, one_pow]
    have h0 := (red_eq_zero_iff (w := v) ((Valuation.map_sub _ _ _).trans (max_le hWp hle))).2
      hWred
    rw [red_sub hWp hle, sub_eq_zero, red_pow hW1.le, red_mul hC1.le (by rw [map_pow, hX1,
      one_pow]), red_pow hX1.le, red_algebraMap_C _ hcm1] at h0
    exact h0
  have hres0 : residue (HenselComplete.integers C) ⟨cm, by simpa using hcm1⟩ ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
    simp [hcm']
  have hvc : Q.valuation (algebraMap 𝓀 _ (residue (HenselComplete.integers C)
      ⟨cm, by simpa using hcm1⟩)) = 1 :=
    valuation_algebraMap_eq_one (fun b ↦ Q.valuation_algebraMap_le_one b) hres0
  have hY0 : red C W v ≠ 0 := by
    rw [Ne, red_eq_zero_iff hW1.le, hW1]; exact lt_irrefl 1
  have hYv0 : Q.valuation (red C W v) ≠ 0 := by simpa using hY0
  set n := log (Q.valuation (red C W v))
  have hn : Q.valuation (red C W v) = exp n := (exp_log hYv0).symm
  have hval := congrArg Q.valuation hrel
  rw [map_pow, map_mul, map_pow, hvc, one_mul, hn, valuation_x hQ, ← exp_nsmul, ← exp_nsmul,
    exp_inj, nsmul_eq_mul, nsmul_eq_mul] at hval
  -- `p ∣ ord_Q x̄`
  have hpdvd : p ∣ ord (red C X v) Q := by
    have h : (p : ℤ) ∣ (ord (red C X v) Q : ℤ) * D.m := ⟨-n, by linarith⟩
    rcases Int.Prime.dvd_mul' hpp h with h | h
    · exact Int.natCast_dvd_natCast.1 h
    · exact absurd (Int.natCast_dvd_natCast.1 h) D.hpm
  have hord : ord (red C X v) Q = p := Nat.dvd_antisymm hdvd hpdvd
  refine ⟨hord, ?_⟩
  rw [hn]
  congr 1
  rw [hord] at hval
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have : (p : ℤ) * n = (p : ℤ) * (-(D.m : ℤ)) := by linarith
  exact mul_left_cancel₀ hp0 this

end Orders

/-! ### Values at the vertices -/

section Values

/-- The constant `b ∈ C` in `F'` through `L`. -/
local notation "cst" b => algebraMap L F' (algebraMap (RatFunc C) L (algebraMap C (RatFunc C) b))

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [IsScalarTower (RatFunc C) L F'] [Algebra (RatFunc C) F'] [Fact p.Prime]
  [IsUltrametricDist C] in
/-- Changing the normalization `λ` of `w`. -/
lemma kumW_eq_mul {h' : C[X]} {lam lam' : C} (hlam : lam ≠ 0) (hlam' : lam' ≠ 0) :
    kumW L a c θ h' lam = kumW L a c θ h' lam' * cst (lam' / lam) := by
  have h0 : (cst lam) ≠ 0 := by simpa using hlam
  have h0' : (cst lam') ≠ 0 := by simpa using hlam'
  simp only [kumW, map_div₀]
  field_simp

omit [IsAlgClosed C] [Algebra (RatFunc C) F'] [IsScalarTower (RatFunc C) L F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
/-- Constants have their norm at an extension of a sheet. -/
lemma sheet_cst {l' : C} (hl0' : l' ≠ 0) (hl1' : ‖l'‖ < 1) {μ : Valuation F' ℝ≥0}
    (hμ : μ.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0' hl1').1) (b : C) :
    μ (cst b) = ‖b‖₊ := by
  rw [← Valuation.comap_apply, hμ, sheet_algebraMap, gaussRat_algebraMap_C,
    NormedField.valuation_apply]

omit [FiniteDimensional (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [IsAlgClosed C] [Algebra (RatFunc C) F'] [IsScalarTower (RatFunc C) L F'] in
/-- **The value of `w` at another sheet radius**: if `D'` is Kummer data at the radius `‖l'‖`
with the same `h̃`, then `μ w = ‖λ'‖/‖λ‖` at every extension `μ` of that sheet. -/
theorem kumW_value (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f) {l' : C} (hl0' : l' ≠ 0) (hl1' : ‖l'‖ < 1)
    (D' : InsepData hc ν₀ P' h1 hl0' hl1' p γ f) (hh : D'.h' = D.h') {μ : Valuation F' ℝ≥0}
    (hμ : μ.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0' hl1').1) :
    μ (kumW L a c θ D.h' D.lam) = ‖D'.lam‖₊ / ‖D.lam‖₊ := by
  have hlam0 : D.lam ≠ 0 := nnnorm_ne_zero_iff.1 (lt_of_le_of_lt zero_le D.hγl).ne'
  have hlam0' : D'.lam ≠ 0 := nnnorm_ne_zero_iff.1 (lt_of_le_of_lt zero_le D'.hγl).ne'
  obtain ⟨hw1, -, -⟩ := insep_value hc ν₀ P' h1 hl0' hl1' p hγ μ hμ hθ D'.hh' D'.hγl D'.hl1'
    D'.hGle D'.hGm D'.hf
  rw [hh] at hw1
  rw [kumW_eq_mul θ hlam0 hlam0', map_mul, hw1, one_mul, sheet_cst hc ν₀ P' h1 hl0' hl1' hμ,
    nnnorm_div]

omit [IsAlgClosed C] [Fact p.Prime] in
/-- `‖λ'‖^p = ‖λ‖^p ‖e‖^m` for Kummer data with the same `f̃, h̃, m` at the radii `‖l‖` and
`‖l e‖`. -/
lemma lam_pow_eq (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f) {e : C} (hle0 : l * e ≠ 0)
    (hle1 : ‖l * e‖ < 1) (D' : InsepData hc ν₀ P' h1 hle0 hle1 p γ f) (hf' : D'.f' = D.f')
    (hh : D'.h' = D.h') (hm : D'.m = D.m) :
    ‖D'.lam‖₊ ^ p = ‖D.lam‖₊ ^ p * ‖e‖₊ ^ D.m := by
  have h1' := D'.hGm
  have h2 := D.hGm
  rw [hf', hh, hm, norm_mul, mul_pow, ← mul_assoc, h2] at h1'
  rw [← NNReal.coe_inj]; push_cast; exact h1'.symm

end Values

/-! ### Separating the other vertices -/

section Separate

omit [FiniteDimensional (RatFunc C) F'] [IsAlgClosed C] in
/-- **Other extensions are small somewhere off `P'`**: an extension of `w_{a,|l c|}` to `L`
other than the sheet extension is `< 1` at some `y ∉ P'` of `R' = DRint a c L`. -/
lemma exists_small_of_ne {l' : C} (hl0' : l' ≠ 0) (hl1' : ‖l'‖ < 1) (u : Valuation L ℝ≥0)
    (hu : u.comap (algebraMap (RatFunc C) L) = (DiscGerm.gaussDiscVal (a := a) hc hl0' hl1').val)
    (hne : u ≠ (sheetExt hc ν₀ P' h1 hl0' hl1').1) :
    ∃ y : DRint a c L, y ∉ P' ∧ u (y : L) < 1 := by
  by_contra h
  push Not at h
  exact hne (eq_sheetExt hc ν₀ P' h1 hl0' hl1' u hu fun y hy ↦ by
    by_contra hy'
    exact absurd hy (not_lt.2 (h y hy')))

omit [IsAlgClosed C] [IsUltrametricDist C] in
/-- A uniform exponent: if `a i ≤ 1` and, for each `i`, `a i < 1` or `b i ≤ 1`, then
`a i ^ N b i ≤ 1` for some `N` and all `i`. -/
lemma exists_pow_mul_le_one {ι : Type*} [Finite ι] (a b : ι → ℝ≥0) (ha : ∀ i, a i ≤ 1)
    (h : ∀ i, a i < 1 ∨ b i ≤ 1) : ∃ N : ℕ, ∀ i, a i ^ N * b i ≤ 1 := by
  classical
  have := Fintype.ofFinite ι
  have hN : ∀ i, ∃ N : ℕ, a i ^ N * b i ≤ 1 := by
    intro i
    rcases h i with hi | hi
    · rcases eq_or_ne (b i) 0 with hb | hb
      · exact ⟨0, by simp [hb]⟩
      obtain ⟨N, hN⟩ := _root_.exists_pow_lt_of_lt_one (inv_pos.2 (pos_iff_ne_zero.2 hb)) hi
      refine ⟨N, ?_⟩
      calc a i ^ N * b i ≤ (b i)⁻¹ * b i := mul_le_mul_of_nonneg_right hN.le zero_le
        _ = 1 := inv_mul_cancel₀ hb
    · exact ⟨0, by simpa using hi⟩
  choose N hN using hN
  refine ⟨∑ i, N i, fun i ↦ ?_⟩
  calc a i ^ (∑ j, N j) * b i ≤ a i ^ N i * b i := by
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        exact pow_le_pow_of_le_one zero_le (ha i)
          (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (N j)) (Finset.mem_univ i))
    _ ≤ 1 := hN i

omit [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- An outer vertex restricts on `C(x)` (through `L`) to `w_{a,|l c|}`. -/
lemma outer_comap_eq (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) :
    (v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F'))).comap (algebraMap (RatFunc C) L) =
      (DiscGerm.gaussDiscVal (a := a) hc hl0 hl1).val := by
  have h2 := ((extAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).symm v).2
  refine Valuation.ext fun φ ↦ ?_
  have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u φ) h2
  simp only [Valuation.comap_apply] at this ⊢
  change v.1 (toAff (mul_ne_zero hl0 hc) (algebraMap L F' (algebraMap (RatFunc C) L φ))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact this

omit [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- An inner vertex of the chart `Rint e` restricts on `C(x)` (through `L`) to `w_{a,|l e c|}`. -/
lemma inner_comap_eq {e : C} (he0 : e ≠ 0) (hle1 : ‖l * e‖ < 1)
    (μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
      (Aff a (l * c) (mul_ne_zero hl0 hc) F')) :
    (μ.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F'))).comap (algebraMap (RatFunc C) L) =
      (DiscGerm.gaussDiscVal (a := a) hc (mul_ne_zero hl0 he0) hle1).val := by
  refine Valuation.ext fun φ ↦ ?_
  simp only [Valuation.comap_apply]
  change μ.1 (toAff (mul_ne_zero hl0 hc) (algebraMap L F' (algebraMap (RatFunc C) L φ))) = _
  rw [← IsScalarTower.algebraMap_apply]
  have h : toAff (a := a) (mul_ne_zero hl0 hc) (algebraMap (RatFunc C) F' φ) =
      algebraMap (RatFunc C) (Aff a (l * c) (mul_ne_zero hl0 hc) F')
        ((aff a (l * c) (mul_ne_zero hl0 hc)).symm φ) := by
    rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply]
  rw [h, ← Valuation.comap_apply, μ.2, gaussRat_aff_symm]
  change _ = gaussRat _ a _ φ
  congr 2
  ext
  simp only [Units.val_mul, coe_invRad, Units.val_one, div_one, Units.val_mk0, nnnorm_mul]
  ring

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional (RatFunc C) F'] [Algebra (RatFunc C) L] [Algebra L F']
  [IsScalarTower (RatFunc C) L F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- `x` has value `‖e‖` at the inner vertex. -/
lemma inner_val_X {e : C} (he0 : e ≠ 0)
    (μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
      (Aff a (l * c) (mul_ne_zero hl0 hc) F')) :
    μ.1 (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) = ‖e‖₊ := by
  change μ.1 (algebraMap (RatFunc C) _ RatFunc.X) = _
  rw [← Valuation.comap_apply, μ.2, AnnulusUnit.gaussRat_X, coe_invRad, Units.val_one, div_one]

omit [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra (RatFunc C) L] [Algebra L F'] [IsScalarTower (RatFunc C) L F'] in
/-- Elements of the node chart have value `≤ 1` at the inner vertex. -/
lemma inner_val_le_one {e : C} (he0 : e ≠ 0) (he1 : ‖e‖ < 1)
    (μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
      (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (r : Rint e (Aff a (l * c) (mul_ne_zero hl0 hc) F')) : μ.1 (r : _) ≤ 1 := by
  rw [← toInvExt_apply he0 μ]
  exact valuation_le_one_R he1 (toInvExt he0 μ) (rintEquiv he0 r)

/-- **A separating element**: some `s₀ ∈ R' ∖ P'` is small at every outer vertex of the chart
`Rint e (Aff a (l c) F')` not over the sheet and at every inner vertex not over the inner sheet
`|l e|`. -/
lemma exists_sep [CharZero C] (hp1 : ‖(p : C)‖ < 1) {e : C} (he0 : e ≠ 0)
    (he1 : ‖e‖ < 1) (hle1 : ‖l * e‖ < 1) :
    ∃ s₀ : DRint a c L, s₀ ∉ P' ∧
      (∀ v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
        v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
          (algebraMap L F')) ≠ (sheetExt hc ν₀ P' h1 hl0 hl1).1 →
        v.1 (nodeMap (F' := F') hc hl0 hl1 e s₀ : _) < 1) ∧
      (∀ μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
          (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
        μ.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
          (algebraMap L F')) ≠ (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1 →
        μ.1 (nodeMap (F' := F') hc hl0 hl1 e s₀ : _) < 1) := by
  classical
  set F₁ := Aff a (l * c) (mul_ne_zero hl0 hc) F'
  set e₁ : L →+* F₁ := (toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
    (algebraMap L F')
  haveI : Finite (Ext C F₁) := finite_ext (F := F₁) (Fact.out : p.Prime) hp1
  letI : Fintype (Ext C F₁) := Fintype.ofFinite _
  haveI : Finite (GaussStability.GaussExtension (0 : C) (invRad he0 1) F₁) :=
    finite_gaussExtension 0 _
  letI : Fintype (GaussStability.GaussExtension (0 : C) (invRad he0 1) F₁) := Fintype.ofFinite _
  have hy₁ : ∀ v : Ext C F₁, ∃ y : DRint a c L, y ∉ P' ∧
      (v.1.comap e₁ ≠ (sheetExt hc ν₀ P' h1 hl0 hl1).1 → v.1.comap e₁ (y : L) < 1) := by
    intro v
    by_cases hv : v.1.comap e₁ = (sheetExt hc ν₀ P' h1 hl0 hl1).1
    · exact ⟨1, fun h ↦ (Ideal.IsMaximal.ne_top inferInstance)
        ((Ideal.eq_top_iff_one _).2 h), fun h ↦ absurd hv h⟩
    · obtain ⟨y, hy, hlt⟩ := exists_small_of_ne hc ν₀ P' h1 hl0 hl1 (v.1.comap e₁)
        (outer_comap_eq hc hl0 hl1 v) hv
      exact ⟨y, hy, fun _ ↦ hlt⟩
  have hy₂ : ∀ μ : GaussStability.GaussExtension (0 : C) (invRad he0 1) F₁,
      ∃ y : DRint a c L, y ∉ P' ∧ (μ.1.comap e₁ ≠
        (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1 → μ.1.comap e₁ (y : L) < 1) := by
    intro μ
    by_cases hμ : μ.1.comap e₁ = (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1
    · exact ⟨1, fun h ↦ (Ideal.IsMaximal.ne_top inferInstance)
        ((Ideal.eq_top_iff_one _).2 h), fun h ↦ absurd hμ h⟩
    · obtain ⟨y, hy, hlt⟩ := exists_small_of_ne hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1
        (μ.1.comap e₁) (inner_comap_eq hc hl0 he0 hle1 μ) hμ
      exact ⟨y, hy, fun _ ↦ hlt⟩
  choose y₁ hy₁P hy₁lt using hy₁
  choose y₂ hy₂P hy₂lt using hy₂
  set s₀ : DRint a c L := (∏ v, y₁ v) * ∏ μ, y₂ μ
  have hnode (y : DRint a c L) : (nodeMap (F' := F') hc hl0 hl1 e y : F₁) = e₁ (y : L) := rfl
  refine ⟨s₀, ?_, fun v hv ↦ ?_, fun μ hμ ↦ ?_⟩
  · intro hs
    rcases (inferInstance : P'.IsPrime).mem_or_mem hs with h | h
    · obtain ⟨v, -, hv⟩ := (Ideal.IsPrime.prod_mem_iff (p := P')).1 h
      exact hy₁P v hv
    · obtain ⟨μ, -, hμ⟩ := (Ideal.IsPrime.prod_mem_iff (p := P')).1 h
      exact hy₂P μ hμ
  · have hs : s₀ = y₁ v * ((∏ v' ∈ Finset.univ.erase v, y₁ v') * ∏ μ, y₂ μ) := by
      rw [← mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    rw [hs, map_mul, MulMemClass.coe_mul, map_mul]
    have h1 := hy₁lt v hv
    rw [Valuation.comap_apply] at h1
    have h2 := valuation_le_one_R he1 v (nodeMap (F' := F') hc hl0 hl1 e
      ((∏ v' ∈ Finset.univ.erase v, y₁ v') * ∏ μ, y₂ μ))
    rw [hnode] at h2 ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2
  · have hs : s₀ = y₂ μ * ((∏ v, y₁ v) * ∏ μ' ∈ Finset.univ.erase μ, y₂ μ') := by
      rw [mul_left_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ μ)]
    rw [hs, map_mul, MulMemClass.coe_mul, map_mul]
    have h1 := hy₂lt μ hμ
    rw [Valuation.comap_apply] at h1
    have h2 := inner_val_le_one hc hl0 he0 he1 μ (nodeMap (F' := F') hc hl0 hl1 e
      ((∏ v, y₁ v) * ∏ μ' ∈ Finset.univ.erase μ, y₂ μ'))
    rw [hnode] at h2 ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2

end Separate

/-! ### Values of `w` and integrality -/

section WValues

omit [FiniteDimensional (RatFunc C) F'] [IsAlgClosed C] [IsScalarTower (RatFunc C) L F']
  [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- `w` has value `1` at every outer vertex over the sheet. -/
lemma outer_val_W (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f)
    (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (hvS : v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1) :
    v.1 (toAff (mul_ne_zero hl0 hc) (kumW L a c θ D.h' D.lam)) = 1 := by
  have hv' : (v.1.comap (toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom).comap
      (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0 hl1).1 := by
    rw [← Valuation.comap_comp]; exact hvS
  exact (insep_value hc ν₀ P' h1 hl0 hl1 p hγ _ hv' hθ D.hh' D.hγl D.hl1' D.hGle D.hGm D.hf).1

omit [FiniteDimensional (RatFunc C) F'] [IsAlgClosed C] [IsScalarTower (RatFunc C) L F']
  [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- `w^p` has value `‖e‖^m` at every inner vertex over the inner sheet. -/
lemma inner_val_W (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f) {e : C} (he0 : e ≠ 0) (hle1 : ‖l * e‖ < 1)
    (D' : InsepData hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1 p γ f) (hf' : D'.f' = D.f')
    (hh : D'.h' = D.h') (hm : D'.m = D.m)
    (μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
      (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (hμS : μ.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F')) = (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1) :
    μ.1 (toAff (mul_ne_zero hl0 hc) (kumW L a c θ D.h' D.lam)) ^ p = ‖e‖₊ ^ D.m := by
  have hμ' : (μ.1.comap (toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom).comap
      (algebraMap L F') = (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1 := by
    rw [← Valuation.comap_comp]; exact hμS
  have h := kumW_value hc ν₀ P' h1 hl0 hl1 p γ θ f hγ hθ D (mul_ne_zero hl0 he0) hle1 D' hh hμ'
  have hlam0 : D.lam ≠ 0 := nnnorm_ne_zero_iff.1 (lt_of_le_of_lt zero_le D.hγl).ne'
  change (μ.1.comap (toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom)
    (kumW L a c θ D.h' D.lam) ^ p = _
  rw [h, div_pow, lam_pow_eq hc ν₀ P' h1 hl0 hl1 p γ f D (mul_ne_zero hl0 he0) hle1 D' hf' hh hm,
    mul_div_cancel_left₀ _ (pow_ne_zero _ (nnnorm_ne_zero_iff.2 hlam0))]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional (RatFunc C) F'] [Fact p.Prime] in
/-- `w` is integral over `C[x]` in the twist if `θ` is integral over the disc chart. -/
lemma isIntegral_W (hθint : IsIntegral (discRing a c) θ) (h' : C[X])
    (hh' : ∀ i, ‖h'.coeff i‖₊ ≤ 1) (lam : C) :
    IsIntegral (Algebra.adjoin C {xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')})
      (toAff (a := a) (mul_ne_zero hl0 hc) (kumW L a c θ h' lam)) := by
  have hH : aeval (gaussCoord a c) h' ∈ discRing a c :=
    mem_polyChart_iff.2 ⟨h', Gauss.sup_le_iff.2 fun i ↦ by simpa [Gauss.term] using hh' i, rfl⟩
  have hHint : IsIntegral (discRing a c)
      (algebraMap L F' (algebraMap (RatFunc C) L (aeval (gaussCoord a c) h'))) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap (x := (⟨_, hH⟩ : discRing a c))
  have h1 := isIntegral_adjoin_of_discRing hc hl0 (hθint.sub hHint)
  have hk : toAff (a := a) (mul_ne_zero hl0 hc) (kumW L a c θ h' lam) =
      toAff (a := a) (mul_ne_zero hl0 hc) (θ - algebraMap L F' (algebraMap (RatFunc C) L
        (aeval (gaussCoord a c) h'))) *
        algebraMap C (Aff a (l * c) (mul_ne_zero hl0 hc) F') lam⁻¹ := by
    rw [kumW, div_eq_mul_inv, map_mul, map_inv₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, map_inv₀, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (RatFunc C) L F']
    congr 2
  rw [hk]
  exact h1.mul (isIntegral_algebraMap (x := (⟨_, Subalgebra.algebraMap_mem _ lam⁻¹⟩ :
    Algebra.adjoin C {xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')})))

end WValues

/-! ### Exact node data -/

section NodeData

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- A residue of value `1` at the branch is not in the point. -/
lemma notMem_of_Qval {e : C} (he1 : ‖e‖ < 1) {E : Type*} [Field E] [Algebra (RatFunc C) E]
    [Algebra C E] [IsScalarTower C (RatFunc C) E] [FiniteDimensional (RatFunc C) E]
    (b : OuterBranch C E) (y : Rint e E)
    (hy : b.2.1.valuation (red C (y : E) b.1) = 1) : y ∉ placeIdeal he1 b.1 b.2.2 := by
  intro hmem
  rw [mem_placeIdeal_iff] at hmem
  have h := b.2.1.valuation_sub_res_lt_one (red_mem_V he1 b.1 y b.2.2)
  rw [hmem, map_zero, sub_zero, hy] at h
  exact lt_irrefl 1 h

omit [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra (RatFunc C) L] [Algebra L F'] [IsScalarTower (RatFunc C) L F'] [Fact p.Prime] in
/-- The order of a monomial quotient `W^i / X^j` at a branch. -/
lemma Qval_quot (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (Q : CurvePlace 𝓀 (IsLocalRing.ResidueField v.1.valuationSubring))
    {W X : Aff a (l * c) (mul_ne_zero hl0 hc) F'} (hW1 : v.1 W = 1) (hX1 : v.1 X = 1)
    (hX0 : X ≠ 0) (i j : ℕ) {a' b' : ℤ}
    (hQW : Q.valuation (red C W v) = exp a') (hQX : Q.valuation (red C X v) = exp b') :
    v.1 (W ^ i / X ^ j) = 1 ∧ Q.valuation (red C (W ^ i / X ^ j) v) = exp (i * a' - j * b') := by
  have hy : v.1 (W ^ i / X ^ j) = 1 := by
    rw [map_div₀, map_pow, map_pow, hW1, hX1]; simp
  refine ⟨hy, ?_⟩
  have hrel : W ^ i / X ^ j * X ^ j = W ^ i := div_mul_cancel₀ _ (pow_ne_zero _ hX0)
  have hXj : v.1 (X ^ j) ≤ 1 := by rw [map_pow, hX1, one_pow]
  have h : Q.valuation (red C (W ^ i / X ^ j) v) * Q.valuation (red C X v) ^ j =
      Q.valuation (red C W v) ^ i := by
    rw [← map_pow, ← map_mul, ← red_pow hX1.le, ← red_mul hy.le hXj, hrel, red_pow hW1.le,
      map_pow]
  rw [hQX, hQW, ← exp_nsmul, ← exp_nsmul] at h
  have hy0 : Q.valuation (red C (W ^ i / X ^ j) v) ≠ 0 := by
    have : red C (W ^ i / X ^ j) v ≠ 0 := by
      rw [Ne, red_eq_zero_iff hy.le, hy]; exact lt_irrefl 1
    simpa using this
  rw [← exp_log hy0, ← exp_add, exp_inj, nsmul_eq_mul, nsmul_eq_mul] at h
  rw [← exp_log hy0, exp_inj]
  linarith

/-- **A small element off the sheet**: `S ∈ R'' ∖ P''` such that `S u` and `S z` have value `≤ 1`
at every outer and inner vertex of the chart, given the bounds at the vertices over the sheets. -/
lemma exists_S [CharZero C] (hp1 : ‖(p : C)‖ < 1) {e : C} (he0 : e ≠ 0) (he1 : ‖e‖ < 1)
    (hle1 : ‖l * e‖ < 1) (P'' : Ideal (Rint e (Aff a (l * c) (mul_ne_zero hl0 hc) F')))
    [P''.IsPrime] (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 e) = P')
    (u z : Aff a (l * c) (mul_ne_zero hl0 hc) F')
    (hgoodO : ∀ v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
      v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
        (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1 → v.1 u ≤ 1 ∧ v.1 z ≤ 1)
    (hgoodI : ∀ μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
        (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
      μ.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
        (algebraMap L F')) = (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1 →
        μ.1 u ≤ 1 ∧ μ.1 z ≤ 1) :
    ∃ S : Rint e (Aff a (l * c) (mul_ne_zero hl0 hc) F'), S ∉ P'' ∧
      (∀ v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
        v.1 ((S : _) * u) ≤ 1 ∧ v.1 ((S : _) * z) ≤ 1) ∧
      (∀ μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
          (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
        μ.1 ((S : _) * u) ≤ 1 ∧ μ.1 ((S : _) * z) ≤ 1) := by
  classical
  obtain ⟨s₀, hs₀P, hs₀o, hs₀i⟩ := exists_sep (F' := F') hc ν₀ P' h1 hl0 hl1 p hp1 he0 he1 hle1
  obtain ⟨S0, hS0⟩ : ∃ S0 : Rint e (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
    S0 = nodeMap (F' := F') hc hl0 hl1 e s₀ := ⟨_, rfl⟩
  haveI : Finite (Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) :=
    finite_ext (F := (Aff a (l * c) (mul_ne_zero hl0 hc) F')) (Fact.out : p.Prime) hp1
  letI : Fintype (Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) := Fintype.ofFinite _
  haveI : Finite (GaussStability.GaussExtension (0 : C) (invRad he0 1)
      (Aff a (l * c) (mul_ne_zero hl0 hc) F')) :=
    finite_gaussExtension 0 _
  obtain ⟨N, hN⟩ := exists_pow_mul_le_one
    (ι := Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F') ⊕
      GaussStability.GaussExtension (0 : C) (invRad he0 1) (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (Sum.elim (fun v ↦ v.1 (S0 : (Aff a (l * c) (mul_ne_zero hl0 hc) F')))
      (fun μ ↦ μ.1 (S0 : (Aff a (l * c) (mul_ne_zero hl0 hc) F'))))
    (Sum.elim (fun v ↦ max (v.1 u) (v.1 z)) (fun μ ↦ max (μ.1 u) (μ.1 z))) (fun i ↦ by
    rcases i with v | μ
    · exact valuation_le_one_R he1 v S0
    · exact inner_val_le_one hc hl0 he0 he1 μ S0) (fun i ↦ by
    rcases i with v | μ
    · by_cases hv : v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
          (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1
      · obtain ⟨h1', h2'⟩ := hgoodO v hv
        exact Or.inr (max_le h1' h2')
      · left; rw [hS0]; exact hs₀o v hv
    · by_cases hμ : μ.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
          (algebraMap L F')) = (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1
      · obtain ⟨h1', h2'⟩ := hgoodI μ hμ
        exact Or.inr (max_le h1' h2')
      · left; rw [hS0]; exact hs₀i μ hμ)
  refine ⟨S0 ^ N, fun hmem ↦ ?_, fun v ↦ ?_, fun μ ↦ ?_⟩
  · have h0 := (inferInstance : P''.IsPrime).mem_of_pow_mem N hmem
    rw [hS0] at h0
    exact hs₀P (by rw [← hP'']; exact h0)
  · have := hN (Sum.inl v)
    simp only [Sum.elim_inl] at this
    rw [SubmonoidClass.coe_pow, map_mul, map_mul, map_pow]
    exact ⟨(mul_le_mul_of_nonneg_left (le_max_left _ _) zero_le).trans this,
      (mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le).trans this⟩
  · have := hN (Sum.inr μ)
    simp only [Sum.elim_inr] at this
    rw [SubmonoidClass.coe_pow, map_mul, map_mul, map_pow]
    exact ⟨(mul_le_mul_of_nonneg_left (le_max_left _ _) zero_le).trans this,
      (mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le).trans this⟩

/-- **Exact node data over a Kummer sheet** (purely inseparable case). Let `θ^p = f`, `θ` integral
over the disc chart, with Kummer data `D` at the radius `‖l‖` whose index `m` strictly dominates,
and data `D'` with the same `f̃, h̃, m` at the radius `‖l e‖`. Then every point `P''` of the node
chart `Rint e (Aff a (l c) F')` over the node and over the sheet `P'` has a unique outer branch,
with exact node data: `u = w^α / x^β` (`α m = β p + 1`), `σ = (S z)^α`, `z = w^p / x^m`, and
`S` small at the vertices off the sheet. -/
theorem exists_nodeData [CharZero C] [FiniteDimensional L F'] (hp1 : ‖(p : C)‖ < 1)
    (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    (hθint : IsIntegral (discRing a c) θ) (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f)
    (hstrict : ∀ i, i ≠ D.m → ‖(D.f' - D.h' ^ p).coeff i‖ * ‖l‖ ^ i < ‖D.lam‖ ^ p)
    {e : C} (he0 : e ≠ 0) (he1 : ‖e‖ < 1) (hle1 : ‖l * e‖ < 1)
    (D' : InsepData hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1 p γ f) (hf' : D'.f' = D.f')
    (hh : D'.h' = D.h') (hm : D'.m = D.m)
    (P'' : Ideal (Rint e (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) [P''.IsMaximal]
    (hnode : P''.comap (algebraMap (nodeRing e) _) = tubeIdeal e)
    (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 e) = P') :
    ∃ b₁, outerBranches he1 P'' = {b₁} ∧ Nonempty (NodeData he1 P'' b₁) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨b₁, hb₁⟩ := outerBranches_eq_singleton hc ν₀ P' h1 hl0 hl1 p γ θ f hp1 hγ hθ hspan D
    he1 he0 P'' hnode hP''
  refine ⟨b₁, hb₁, ?_⟩
  have hP₁ : placeIdeal he1 b₁.1 b₁.2.2 = P'' := by
    have : b₁ ∈ outerBranches he1 P'' := by rw [hb₁]; exact Set.mem_singleton b₁
    exact this
  obtain ⟨v, Q, hQ⟩ := b₁
  have hvS := outer_restrict hc ν₀ P' h1 hl0 hl1 he1 v hQ hP₁ hP''
  obtain ⟨hord, hWQ⟩ := outer_orders hc ν₀ P' h1 hl0 hl1 p γ θ f hp1 hγ hθ hspan D hstrict v
    hvS hQ
  -- the exponents `α m = β p + 1`
  have hcop : Nat.Coprime D.m p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 D.hpm)
  obtain ⟨α, -, hα⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpp.one_lt
  obtain ⟨β, hαβ⟩ : ∃ β : ℕ, D.m * α = p * β + 1 := ⟨D.m * α / p, by
    have := Nat.div_add_mod (D.m * α) p
    rw [hα] at this
    omega⟩
  -- the elements
  obtain ⟨W, hW⟩ : ∃ W : Aff a (l * c) (mul_ne_zero hl0 hc) F',
    W = toAff (a := a) (mul_ne_zero hl0 hc) (kumW L a c θ D.h' D.lam) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Aff a (l * c) (mul_ne_zero hl0 hc) F',
    X = xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') := ⟨_, rfl⟩
  have hW1 : v.1 W = 1 := by
    rw [hW]; exact outer_val_W hc ν₀ P' h1 hl0 hl1 p γ θ f hγ hθ D v hvS
  have hX1 : v.1 X = 1 := by rw [hX]; exact valuation_xF v
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hX1
    exact zero_ne_one hX1
  have hQX : Q.valuation (red C X v) = exp (-(p : ℤ)) := by
    rw [hX, valuation_x hQ, hord]
  have hQW : Q.valuation (red C W v) = exp (-(D.m : ℤ)) := by rw [hW]; exact hWQ
  obtain ⟨hu1, hQu⟩ := Qval_quot hc hl0 v Q hW1 hX1 hX0 α β hQW hQX
  obtain ⟨hz1, hQz⟩ := Qval_quot hc hl0 v Q hW1 hX1 hX0 p D.m hQW hQX
  have hQu' : Q.valuation (red C (W ^ α / X ^ β) v) = exp (-1) := by
    rw [hQu]; congr 1
    have := congrArg (fun n : ℕ ↦ (n : ℤ)) hαβ
    push_cast at this
    linarith
  have hQz' : Q.valuation (red C (W ^ p / X ^ D.m) v) = 1 := by
    rw [hQz, ← exp_zero]; congr 1; ring
  -- bounds at the vertices over the sheets
  have hgoodO : ∀ v' : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
      v'.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
        (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1 →
      v'.1 (W ^ α / X ^ β) ≤ 1 ∧ v'.1 (W ^ p / X ^ D.m) ≤ 1 := by
    intro v' hv'
    have hW1' : v'.1 W = 1 := by
      rw [hW]; exact outer_val_W hc ν₀ P' h1 hl0 hl1 p γ θ f hγ hθ D v' hv'
    have hX1' : v'.1 X = 1 := by rw [hX]; exact valuation_xF v'
    simp [map_div₀, hW1', hX1']
  have hgoodI : ∀ μ : GaussStability.GaussExtension (0 : C) (invRad he0 1)
        (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
      μ.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
        (algebraMap L F')) = (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 he0) hle1).1 →
      μ.1 (W ^ α / X ^ β) ≤ 1 ∧ μ.1 (W ^ p / X ^ D.m) ≤ 1 := by
    intro μ hμ
    have hWp : μ.1 W ^ p = ‖e‖₊ ^ D.m := by
      rw [hW]; exact inner_val_W hc ν₀ P' h1 hl0 hl1 p γ θ f hγ hθ D he0 hle1 D' hf' hh hm μ hμ
    have hXe : μ.1 X = ‖e‖₊ := by rw [hX]; exact inner_val_X hc hl0 he0 μ
    have he0' : ‖e‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 he0
    refine ⟨?_, ?_⟩
    · have hup : μ.1 (W ^ α / X ^ β) ^ p = ‖e‖₊ := by
        rw [map_div₀, map_pow, map_pow, div_pow, ← pow_mul, mul_comm α p, pow_mul, hWp,
          hXe, ← pow_mul, ← pow_mul, hαβ, pow_succ, mul_comm β p, mul_div_cancel_left₀ _
            (pow_ne_zero _ he0')]
      have h1 : μ.1 (W ^ α / X ^ β) ^ p ≤ 1 := by
        rw [hup]; exact_mod_cast he1.le
      exact (pow_le_one_iff_of_nonneg zero_le hpp.ne_zero).1 h1
    · rw [map_div₀, map_pow, map_pow, hWp, hXe, div_self (pow_ne_zero _ he0')]
  -- the small element and integrality
  obtain ⟨S, hSnot, hSo, hSi⟩ := exists_S hc ν₀ P' h1 hl0 hl1 p hp1 he0 he1 hle1 P'' hP''
    (W ^ α / X ^ β) (W ^ p / X ^ D.m) hgoodO hgoodI
  obtain ⟨K, hK⟩ := exists_xF_pow_mul_isIntegral
    (F' := Aff a (l * c) (mul_ne_zero hl0 hc) F') S.2
  have hWint : IsIntegral (Algebra.adjoin C {xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')}) W := by
    rw [hW]; exact isIntegral_W hc hl0 θ hθint D.h' D.hh' D.lam
  have hmono : ∀ i j : ℕ,
      IsIntegral (Algebra.adjoin C {xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')})
        (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') ^ (K + j) * ((S : _) * (W ^ i / X ^ j))) := by
    intro i j
    have heq : xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') ^ (K + j) *
        ((S : _) * (W ^ i / X ^ j)) =
        (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') ^ K * (S : _)) * W ^ i := by
      rw [← hX, pow_add, div_eq_mul_inv,
        show X ^ K * X ^ j * ((S : Aff a (l * c) (mul_ne_zero hl0 hc) F') * (W ^ i * (X ^ j)⁻¹)) =
          X ^ K * (S : _) * W ^ i * (X ^ j * (X ^ j)⁻¹) by ring,
        mul_inv_cancel₀ (pow_ne_zero _ hX0), mul_one]
    rw [heq]
    exact hK.mul (hWint.pow i)
  have huint : IsIntegral (nodeRing e) ((S : _) * (W ^ α / X ^ β)) :=
    isIntegral_of_le hpp hp1 he0 (hmono α β) (fun v' ↦ (hSo v').1) (fun μ ↦ (hSi μ).1)
  have hzint : IsIntegral (nodeRing e) ((S : _) * (W ^ p / X ^ D.m)) :=
    isIntegral_of_le hpp hp1 he0 (hmono p D.m) (fun v' ↦ (hSo v').2) (fun μ ↦ (hSi μ).2)
  obtain ⟨uR, huR⟩ : ∃ uR : Rint e (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
    (uR : _) = (S : _) * (W ^ α / X ^ β) := ⟨⟨_, huint⟩, rfl⟩
  obtain ⟨zR, hzR⟩ : ∃ zR : Rint e (Aff a (l * c) (mul_ne_zero hl0 hc) F'),
    (zR : _) = (S : _) * (W ^ p / X ^ D.m) := ⟨⟨_, hzint⟩, rfl⟩
  -- residues at the branch
  have hS1 : v.1 (S : _) ≤ 1 := valuation_le_one_R he1 v S
  have hQS : Q.valuation (red C (S : Aff a (l * c) (mul_ne_zero hl0 hc) F') v) = 1 :=
    Qval_one_of_notMem he1 hP₁ hSnot
  have hzRnot : zR ∉ P'' := by
    have hQzR : Q.valuation (red C (zR : Aff a (l * c) (mul_ne_zero hl0 hc) F') v) = 1 := by
      rw [hzR, red_mul hS1 hz1.le, map_mul, hQS, hQz', one_mul]
    have := notMem_of_Qval he1 ⟨v, Q, hQ⟩ zR hQzR
    rwa [hP₁] at this
  have hσ : zR ^ α ∉ P'' := fun h ↦ hzRnot ((inferInstance : P''.IsPrime).mem_of_pow_mem α h)
  have he' : S ^ α ∉ P'' := fun h ↦ hSnot ((inferInstance : P''.IsPrime).mem_of_pow_mem α h)
  have hx : ((zR ^ α : Rint e _) : Aff a (l * c) (mul_ne_zero hl0 hc) F') *
      xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F') =
      ((S ^ α : Rint e _) : _) * (W ^ α / X ^ β) ^ p := by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, hzR, ← hX, mul_pow, mul_assoc]
    congr 1
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, hαβ,
      div_mul_eq_mul_div, mul_comm p α, mul_comm β p, pow_succ, mul_div_mul_right _ _ hX0]
  have hval : Q.valuation (redHom he1 v uR) = exp (-1) := by
    rw [redHom_apply, huR, red_mul hS1 hu1.le, map_mul, hQS, hQu', one_mul]
  exact nonempty_nodeData_of_coord he1 he0 hpp.one_lt.le (W ^ α / X ^ β) (zR ^ α) (S ^ α) hσ he'
    hx uR S hSnot huR hval

/-- **K6, exhaustion over the sheet (purely inseparable case)**: under the hypotheses of
`exists_nodeData` with the inner Kummer data at the radius `‖l c''²‖`, every point `P''` of the
node chart `Rint c'' (Aff a (l c) F')` over the node and over the sheet `P'` is an ordinary double
point. -/
theorem isNodeODP_kummer [CharZero C] [FiniteDimensional L F'] (hp1 : ‖(p : C)‖ < 1)
    (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    (hθint : IsIntegral (discRing a c) θ) (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f)
    (hstrict : ∀ i, i ≠ D.m → ‖(D.f' - D.h' ^ p).coeff i‖ * ‖l‖ ^ i < ‖D.lam‖ ^ p)
    {c'' : C} (hc0'' : c'' ≠ 0) (hc'' : ‖c''‖ < 1) (hle1 : ‖l * c'' ^ 2‖ < 1)
    (D' : InsepData hc ν₀ P' h1 (mul_ne_zero hl0 (pow_ne_zero 2 hc0'')) hle1 p γ f)
    (hf' : D'.f' = D.f') (hh : D'.h' = D.h') (hm : D'.m = D.m)
    (P'' : Ideal (Rint c'' (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) [P''.IsMaximal]
    (hnode : P''.comap (algebraMap (nodeRing c'') _) = tubeIdeal c'')
    (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 c'') = P') :
    IsNodeODP hc'' hc0'' P'' := by
  have hpp : p.Prime := Fact.out
  set c' := c'' ^ 2
  have hc0' : c' ≠ 0 := pow_ne_zero _ hc0''
  have hn : 0 < ‖c''‖ := norm_pos_iff.2 hc0''
  have hlt : ‖c'‖ < ‖c''‖ := by
    rw [norm_pow]
    nlinarith
  have hc' : ‖c'‖ < 1 := hlt.trans hc''
  set Q' := P''.comap (rintMap (F' := Aff a (l * c) (mul_ne_zero hl0 hc) F')
    (nodeRing_le hlt.le hc0''))
  have hcomap := comap_rintMap_comap hc'' hc0'' hlt P'' hnode
  haveI : Q'.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := nodeRing c') _
      (by rw [hcomap]; exact tubeIdeal_isMaximal hc' hc0')
  have hQ' : Q'.comap (nodeMap (F' := F') hc hl0 hl1 c') = P' := by
    rw [← hP'', Ideal.comap_comap]
    rfl
  obtain ⟨b₁, h₁, ⟨N⟩⟩ := exists_nodeData hc ν₀ P' h1 hl0 hl1 p γ θ f hp1 hγ hθ hspan hθint D
    hstrict hc0' hc' hle1 D' hf' hh hm Q' hcomap hQ'
  exact isNodeODP_of_le hpp hp1 hc' hc'' hc0' hc0'' hlt P'' hnode rfl h₁ N

end NodeData

end KummerAnnulus

end SemistableReduction
