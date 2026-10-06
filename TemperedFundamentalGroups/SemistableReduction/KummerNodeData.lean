/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerAnnulus
import TemperedFundamentalGroups.SemistableReduction.NearBoundary

/-!
# Node parameters over a Kummer sheet

Blueprint §9.10, L4 (K6, exhaustion, purely inseparable case). Over the annulus
`|l c₀ c| ≤ |x - a| ≤ |l c|` of the sheet `P'` (node chart `Rint c₀ (Aff a (l c) F')`), with Kummer
data `θ^p = f` whose index `m` strictly dominates `f̃ - h̃^p` at both radii, the element
`w = (θ - h̃(t))/λ` satisfies `w^p ≡ ḡ x^m` at the outer vertex, so `x̄` has order `p` and `w̄`
order `m` at the unique outer branch.

* `toAff_gaussCoord`: `t = l x` in the twist;
* `outer_dominant`: `v w = 1`, `v(w^p - c_m x^m) < 1` with `‖c_m‖ = 1`.
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
  rw [xF_aff, gaussCoord_mul (c := c) hl0, map_mul, map_mul, mul_comm c l,
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

end KummerAnnulus

end SemistableReduction
