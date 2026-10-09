/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourTower
import TemperedFundamentalGroups.SemistableReduction.FundamentalInequality

/-!
# The Kummer step at a type-4 point: no small approximation

Blueprint §9.12, leaf T4, interface `TypeFour.KummerStepFor`. Let `θ^p = f ∈ K`, `σ` an
automorphism fixing `K` with `σ θ = ζ θ` and preserving the valuation `ξ'`.

* `le_valuation_pow_sub`: `f` is not approximated by `p`-th powers of elements of `K` better than
  `‖1 - ζ‖^p` (relative): if `ξ'(θ^p/h^p - 1) < ‖1 - ζ‖^p`, then `θ/h` is close to a unique `ζ^j`,
  which `σ` moves to `ζ^(j - 1)`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section NoSmall

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F]

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- **No small approximation by `p`-th powers.** If `σ θ = ζ θ` for a primitive `p`-th root of
unity `ζ ∈ C`, `σ` fixes `h ≠ 0` and preserves `ξ'`, then
`‖1 - ζ‖^p ξ'(h)^p ≤ ξ'(θ^p - h^p)`. -/
theorem le_valuation_pow_sub {p : ℕ} (hp0 : p ≠ 0) {ξ' : Valuation F ℝ≥0}
    (hconst : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊) {ζ : C} (hζ : IsPrimitiveRoot ζ p)
    {σ : F ≃ₐ[RatFunc C] F} (hσξ : ∀ y, ξ' (σ y) = ξ' y) {θ h : F} (hh0 : h ≠ 0)
    (hσθ : σ θ = algebraMap C F ζ * θ) (hσh : σ h = h) :
    ‖1 - ζ‖₊ ^ p * ξ' h ^ p ≤ ξ' (θ ^ p - h ^ p) := by
  by_contra hlt
  push Not at hlt
  set t := θ / h
  set z := algebraMap C F ζ
  have hz : IsPrimitiveRoot z p := hζ.map_of_injective (algebraMap C F).injective
  have hξh : ξ' h ≠ 0 := (map_ne_zero ξ').2 hh0
  -- `ξ'(t^p - 1) < ‖1 - ζ‖^p`
  have ht : ξ' (t ^ p - 1) < ‖1 - ζ‖₊ ^ p := by
    have e : t ^ p - 1 = (θ ^ p - h ^ p) / h ^ p := by
      simp only [t, div_pow]; field_simp
    rw [e, map_div₀, map_pow, div_lt_iff₀ (pow_pos ((zero_le).lt_of_ne (Ne.symm hξh)) p)]
    exact hlt
  -- `t^p - 1 = ∏ (t - ζ')` over the `p`-th roots of unity
  have hprod : t ^ p - 1 = ∏ ζ' ∈ nthRootsFinset p (1 : F), (t - ζ') := by
    have := congrArg (Polynomial.eval t) (X_pow_sub_one_eq_prod (Nat.pos_of_ne_zero hp0) hz)
    simpa [Polynomial.eval_prod] using this
  have hcard : (nthRootsFinset p (1 : F)).card = p := hz.card_nthRootsFinset
  -- some root of unity is close to `t`
  obtain ⟨ζ', hζ', hclose⟩ : ∃ ζ' ∈ nthRootsFinset p (1 : F), ξ' (t - ζ') < ‖1 - ζ‖₊ := by
    by_contra! h
    have hle : ‖1 - ζ‖₊ ^ p ≤ ξ' (t ^ p - 1) := by
      have := Finset.pow_card_le_prod _ (fun x ↦ ξ' (t - x)) _ h
      rw [hcard] at this
      rw [hprod, map_prod]
      exact this
    exact absurd ht (not_lt.2 hle)
  have hζ'1 : ζ' ^ p = 1 := (mem_nthRootsFinset (Nat.pos_of_ne_zero hp0) 1).1 hζ'
  have hξζ' : ξ' ζ' = 1 := by
    have : ξ' ζ' ^ p = 1 := by rw [← map_pow, hζ'1, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hp0).1 this
  have hξz : ξ' z = 1 := by
    rw [hconst]
    have : ‖ζ‖₊ ^ p = 1 := by rw [← nnnorm_pow, hζ.pow_eq_one, nnnorm_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hp0).1 this
  have hz0 : z ≠ 0 := hz.ne_zero hp0
  -- apply `σ`
  have hσt : σ t = z * t := by
    simp only [t, map_div₀, hσθ, hσh]; ring
  have h2 : ξ' (t - z⁻¹ * ζ') < ‖1 - ζ‖₊ := by
    have := hσξ (t - ζ')
    rw [map_sub, hσt] at this
    have hσζ' : σ ζ' = ζ' := by
      haveI : NeZero p := ⟨hp0⟩
      obtain ⟨j, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ'1
      rw [map_pow, algEquiv_algebraMap_C]
    rw [hσζ'] at this
    rw [show t - z⁻¹ * ζ' = z⁻¹ * (z * t - ζ') by field_simp, map_mul, map_inv₀, hξz, inv_one,
      one_mul, this]
    exact hclose
  -- contradiction
  have h3 : ξ' (ζ' - z⁻¹ * ζ') < ‖1 - ζ‖₊ := by
    rw [show ζ' - z⁻¹ * ζ' = (t - z⁻¹ * ζ') - (t - ζ') by ring]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt h2 hclose)
  have h4 : ξ' (ζ' - z⁻¹ * ζ') = ‖1 - ζ‖₊ := by
    rw [show ζ' - z⁻¹ * ζ' = ζ' * z⁻¹ * (z - 1) by field_simp, map_mul, map_mul, map_inv₀, hξz,
      hξζ', inv_one, one_mul, one_mul, ← Valuation.map_neg, neg_sub, ← map_one (algebraMap C F),
      ← map_sub, hconst]
  exact absurd h3 (by rw [h4]; exact lt_irrefl _)

end NoSmall

/-! ### Residue fields and values of finite extensions of a type-4 point -/

section Residue

attribute [local instance] DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- A real valuation extending the norm of `C` in which every integral element is close to a
constant has algebraically closed residue field (it is the residue field of `C`). -/
theorem isAlgClosed_residueField_of_close {E : Type*} [Field E] [Algebra C E]
    {u : Valuation E ℝ≥0} (hconst : ∀ b : C, u (algebraMap C E b) = ‖b‖₊)
    (hres : ∀ y, u y ≤ 1 → ∃ b : C, ‖b‖ ≤ 1 ∧ u (y - algebraMap C E b) < 1) :
    IsAlgClosed (IsLocalRing.ResidueField u.valuationSubring) := by
  set V := u.valuationSubring
  have hequiv : u.IsEquiv V.valuation := Valuation.isEquiv_valuation_valuationSubring u
  have hmax : ∀ a : V, a ∈ IsLocalRing.maximalIdeal V ↔ u (a : E) < 1 := fun a ↦ by
    rw [ValuationSubring.valuation_lt_one_iff, ← hequiv.lt_one_iff_lt_one]
  have hunit : ∀ a : V, IsUnit a ↔ u (a : E) = 1 := fun a ↦ by
    rw [ValuationSubring.valuation_eq_one_iff, ← map_one V.valuation, ← hequiv.eq_iff, map_one]
  let φ₀ : HenselComplete.integers C →+* V :=
    { toFun := fun b ↦ ⟨algebraMap C E b, by
        rw [Valuation.mem_valuationSubring_iff, hconst]
        exact_mod_cast (HenselComplete.norm_le_one b)⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hφ₀ : ∀ b, ((φ₀ b : V) : E) = algebraMap C E b := fun b ↦ rfl
  haveI : IsLocalHom φ₀ := ⟨fun b hb ↦ by
    rw [hunit, hφ₀, hconst] at hb
    rw [HenselComplete.isUnit_iff_norm_eq_one, ← coe_nnnorm, hb, NNReal.coe_one]⟩
  let φ : 𝓀 →+* IsLocalRing.ResidueField V := IsLocalRing.ResidueField.map φ₀
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨b, hb1, hb⟩ := hres y ((Valuation.mem_valuationSubring_iff _ _).1 y.2)
    refine ⟨IsLocalRing.residue _ ⟨b, (HenselComplete.mem_integers_iff b).2 hb1⟩, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    refine (Ideal.Quotient.eq).2 ((hmax _).2 ?_)
    change u (((φ₀ _ : V) : E) - (y : E)) < 1
    rw [hφ₀, ← Valuation.map_neg, neg_sub]
    exact hb
  exact isAlgClosed_of_ringEquiv' (RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩)

end Residue

section Finite

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

open FundamentalInequality in
/-- **Values and residues of a finite extension of a type-4 point are those of `C`**: every
`y ≠ 0` is close to a constant, `ξ'(y - b) < ξ'(y)`. -/
theorem exists_const_sub_lt_finite {ξ' : Valuation F ℝ≥0}
    (hconst : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊)
    (hξ : Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) {y : F} (hy : y ≠ 0) :
    ∃ b : C, ξ' (y - algebraMap C F b) < ξ' y := by
  classical
  set v := ξ'.comap (algebraMap (RatFunc C) F)
  have hvc : ∀ b : C, v (algebraMap C (RatFunc C) b) = ‖b‖₊ := fun b ↦ by
    simp only [v, Valuation.comap_apply]
    rw [← IsScalarTower.algebraMap_apply]
    exact hconst b
  -- the value of `y` is a norm
  obtain ⟨n, hn, c, hc0, hcn⟩ := exists_pow_valuation_eq (K := RatFunc C) (w := ξ')
    (Algebra.IsIntegral.isIntegral y) hy
  obtain ⟨b₀, hb₀⟩ := exists_const_sub_lt hξ hc0
  have hvb₀ : v c = ‖b₀‖₊ := by
    rw [← hvc b₀]
    exact (Valuation.map_eq_of_sub_lt v (by rwa [← Valuation.map_neg, neg_sub])).symm
  obtain ⟨b₁, hb₁⟩ := IsAlgClosed.exists_pow_nat_eq b₀ hn
  have hyb : ξ' y = ‖b₁‖₊ := by
    refine (pow_left_inj₀ zero_le zero_le hn.ne').1 ?_
    rw [hcn, ← nnnorm_pow, hb₁]
    exact hvb₀
  have hy0 : ξ' y ≠ 0 := (map_ne_zero ξ').2 hy
  have hb₁0 : b₁ ≠ 0 := by
    rintro rfl; rw [nnnorm_zero] at hyb; exact hy0 hyb
  have hb₁F : algebraMap C F b₁ ≠ 0 := by simpa using hb₁0
  set y' := y / algebraMap C F b₁
  have hy'1 : ξ' y' = 1 := by
    rw [map_div₀, hconst, hyb, div_self (nnnorm_ne_zero_iff.2 hb₁0)]
  -- the residue field of `v` is algebraically closed
  haveI : IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring) := by
    refine isAlgClosed_residueField_of_close hvc fun z hz ↦ ?_
    by_cases hz0 : z = 0
    · exact ⟨0, by simp, by rw [hz0, map_zero, sub_zero, map_zero]; exact zero_lt_one⟩
    obtain ⟨b, hb⟩ := exists_const_sub_lt hξ hz0
    refine ⟨b, ?_, hb.trans_le hz⟩
    have := (Valuation.map_eq_of_sub_lt v (by rwa [← Valuation.map_neg, neg_sub])).trans_le hz
    rw [hvc] at this
    exact_mod_cast this
  -- the residue of `y'` comes from the residue field of `v`
  set W := ξ'.valuationSubring
  have hequiv : ξ'.IsEquiv W.valuation := Valuation.isEquiv_valuation_valuationSubring ξ'
  set x : W := ⟨y', (Valuation.mem_valuationSubring_iff _ _).2 hy'1.le⟩
  haveI := finite_residueField (v := v) (w := ξ')
  have hint : IsIntegral (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.residue W x) := Algebra.IsIntegral.isIntegral _
  obtain ⟨r, hr⟩ := minpoly.mem_range_of_degree_eq_one _ _
    (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hint))
  obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective r
  rw [IsLocalRing.ResidueField.algebraMap_residue] at hr
  have hclose : ξ' (y' - algebraMap (RatFunc C) F c') < 1 := by
    have h := (Ideal.Quotient.eq).1 hr.symm
    rw [ValuationSubring.valuation_lt_one_iff, ← hequiv.lt_one_iff_lt_one] at h
    exact h
  have hc'1 : ξ' (algebraMap (RatFunc C) F c') = 1 :=
    (Valuation.map_eq_of_sub_lt ξ' (by rwa [← Valuation.map_neg, neg_sub, hy'1])).trans hy'1
  have hc'0 : (c' : RatFunc C) ≠ 0 := by
    rintro h; rw [h, map_zero, map_zero] at hc'1; exact zero_ne_one hc'1
  obtain ⟨b, hb⟩ := exists_const_sub_lt hξ hc'0
  have hb' : ξ' (algebraMap (RatFunc C) F c' - algebraMap C F b) < 1 := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, ← map_sub]
    change v _ < 1
    calc v _ < v c' := hb
      _ = 1 := hc'1
  refine ⟨b₁ * b, ?_⟩
  have e : y - algebraMap C F (b₁ * b) =
      algebraMap C F b₁ * ((y' - algebraMap (RatFunc C) F c') +
        (algebraMap (RatFunc C) F c' - algebraMap C F b)) := by
    simp only [y', map_mul]; field_simp; ring
  rw [e, map_mul, hconst, hyb]
  refine mul_lt_of_lt_one_right (nnnorm_pos.2 hb₁0) ?_
  exact (Valuation.map_add _ _ _).trans_lt (max_lt hclose hb')

end Finite

/-! ### `‖1 - ζ‖ = ‖γ‖` and no approximation to the bound -/

section Strict

omit [IsAlgClosed C] in
lemma norm_one_sub_pow_le {x : C} (hx : ‖x‖ ≤ 1) (k : ℕ) : ‖1 - x ^ k‖ ≤ ‖1 - x‖ := by
  have h : 1 - x ^ k = (1 - x) * ∑ i ∈ Finset.range k, x ^ i := by
    rw [mul_comm, ← neg_sub, ← neg_sub x, mul_neg, geom_sum_mul]
  rw [h, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx

omit [IsAlgClosed C] in
/-- `‖1 - ζ‖ ^ (p - 1) = ‖p‖` for a primitive `p`-th root of unity. -/
lemma norm_one_sub_pow_pred {p : ℕ} (hp : p.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    ‖1 - ζ‖ ^ (p - 1) = ‖(p : C)‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have hζ1 : ‖ζ‖ = 1 := by
    have : ‖ζ‖ ^ (n + 1) = 1 := by rw [← norm_pow, hζ.pow_eq_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero n)).1 this
  have hk : ∀ k ∈ Finset.range n, ‖1 - ζ ^ (k + 1)‖ = ‖1 - ζ‖ := by
    intro k hk
    refine le_antisymm (norm_one_sub_pow_le hζ1.le _) ?_
    -- `ζ` is a power of `ζ^(k+1)`
    have hcop : (k + 1).Coprime (n + 1) := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
      (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) (by simpa using Finset.mem_range.1 hk))))
    have hζk : IsPrimitiveRoot (ζ ^ (k + 1)) (n + 1) := hζ.pow_of_coprime _ hcop
    haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    obtain ⟨j, -, hj⟩ := hζk.eq_pow_of_pow_eq_one hζ.pow_eq_one
    have : ‖ζ ^ (k + 1)‖ ≤ 1 := by rw [norm_pow, hζ1, one_pow]
    calc ‖1 - ζ‖ = ‖1 - (ζ ^ (k + 1)) ^ j‖ := by rw [hj]
      _ ≤ _ := norm_one_sub_pow_le this j
  have h := congrArg norm (hζ.prod_one_sub_pow_eq_order)
  rw [norm_prod, Finset.prod_congr rfl hk, Finset.prod_const, Finset.card_range] at h
  rw [Nat.add_sub_cancel, h]
  push_cast
  rfl

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

/-- **No approximation to the bound** (the Artin–Schreier improvement): in the situation of
`le_valuation_pow_sub`, at a type-4 point the inequality is strict. If equality held,
`θ^p/h^p - 1 = γ^p u` with `ξ'(u) = 1`, `u ≡ b` a constant; an Artin–Schreier root `c^p - c = b`
gives `h' = h (1 + γ c)` with `ξ'(θ^p/h'^p - 1) < ‖γ‖^p`. -/
theorem lt_valuation_pow_sub [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    {ξ' : Valuation F ℝ≥0} (hconst : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊)
    (hξ : Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) {ζ : C}
    (hζ : IsPrimitiveRoot ζ p) {σ : F ≃ₐ[RatFunc C] F} (hσξ : ∀ y, ξ' (σ y) = ξ' y) {θ h : F}
    (hh0 : h ≠ 0) (hσθ : σ θ = algebraMap C F ζ * θ) (hσh : σ h = h) :
    ‖1 - ζ‖₊ ^ p * ξ' h ^ p < ξ' (θ ^ p - h ^ p) := by
  have hp0 := hp.ne_zero
  have hle := le_valuation_pow_sub hp0 hconst hζ hσξ hh0 hσθ hσh
  refine lt_of_le_of_ne hle fun heq ↦ ?_
  -- `γ` with `γ^(p-1) = -p`
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (-(p : C)) (Nat.sub_pos_of_lt hp.one_lt)
  have hγζ : ‖γ‖₊ = ‖1 - ζ‖₊ := by
    have h1 : ‖γ‖ ^ (p - 1) = ‖1 - ζ‖ ^ (p - 1) := by
      rw [← norm_pow, hγ, norm_neg, norm_one_sub_pow_pred hp hζ]
    exact NNReal.coe_injective ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
      (Nat.sub_pos_of_lt hp.one_lt).ne').1 h1)
  have hγ1 : ‖γ‖ < 1 := by
    have : ‖γ‖ ^ (p - 1) < 1 := by rw [← norm_pow, hγ, norm_neg]; exact hp1
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (Nat.sub_pos_of_lt hp.one_lt).ne').1 this
  have hγ0 : γ ≠ 0 := by
    rintro rfl; rw [zero_pow (Nat.sub_pos_of_lt hp.one_lt).ne', zero_eq_neg] at hγ
    exact hp0 (by exact_mod_cast hγ)
  have hγp : γ ^ p = -(p : C) * γ := by
    rw [← hγ, ← pow_succ, Nat.sub_add_cancel hp.pos]
  have hδ : ‖1 - ζ‖₊ ^ p = ‖γ‖₊ ^ p := by rw [hγζ]
  have hξh : 0 < ξ' h := zero_le.lt_of_ne (Ne.symm ((map_ne_zero ξ').2 hh0))
  set t := θ / h
  have hg : ξ' (t ^ p - 1) = ‖γ‖₊ ^ p := by
    have e : t ^ p - 1 = (θ ^ p - h ^ p) / h ^ p := by
      simp only [t, div_pow]; field_simp
    rw [e, map_div₀, ← heq, map_pow, hδ, mul_div_cancel_right₀ _ (pow_pos hξh p).ne']
  have hγF : algebraMap C F (γ ^ p) ≠ 0 := by simpa using pow_ne_zero p hγ0
  set u := (t ^ p - 1) / algebraMap C F (γ ^ p)
  have hu1 : ξ' u = 1 := by
    rw [map_div₀, hg, hconst, nnnorm_pow, div_self (pow_ne_zero p (nnnorm_ne_zero_iff.2 hγ0))]
  have hu0 : u ≠ 0 := by rintro h0; rw [h0, map_zero] at hu1; exact zero_ne_one hu1
  obtain ⟨b, hb⟩ := exists_const_sub_lt_finite hconst hξ hu0
  rw [hu1] at hb
  have hb1 : ‖b‖₊ = 1 := by
    rw [← hconst, ← hu1]
    exact Valuation.map_eq_of_sub_lt ξ' (by rwa [← Valuation.map_neg, neg_sub, hu1])
  -- an Artin–Schreier root
  obtain ⟨c, hc⟩ : ∃ c : C, c ^ p - c = b := by
    have hdeg : (X ^ p - X - Polynomial.C b : C[X]).degree ≠ 0 := by
      have hnd : (X ^ p - X - Polynomial.C b : C[X]).natDegree = p := by
        rw [natDegree_sub_C, natDegree_sub_eq_left_of_natDegree_lt (by simpa using hp.one_lt),
          natDegree_X_pow]
      intro h0
      have := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
      rw [hnd] at this
      exact hp0 this
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨c, by simpa [sub_eq_zero, IsRoot] using hc⟩
  have hc1 : ‖c‖ ≤ 1 := by
    by_contra! hc1
    have hlt : ‖c‖ < ‖c ^ p‖ := by
      rw [norm_pow]; exact lt_self_pow₀ hc1 hp.one_lt
    have : ‖b‖ = ‖c ^ p‖ := by
      rw [← hc, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_neg]; exact hlt.ne'), norm_neg, max_eq_left hlt.le]
    have hb1' : ‖b‖ = 1 := by rw [← coe_nnnorm, hb1]; rfl
    rw [hb1', norm_pow] at this
    exact absurd this (ne_of_lt (one_lt_pow₀ hc1 hp0))
  set x := γ * c
  have hx1 : ‖x‖ < 1 := by
    rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hγ1 hc1
  have he1 : ‖1 + x‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hx1.ne'),
      norm_one, max_eq_left hx1.le]
  set h' := h * algebraMap C F (1 + x)
  have he0 : (1 + x) ≠ 0 := by intro h0; rw [h0, norm_zero] at he1; exact zero_ne_one he1
  have hh'0 : h' ≠ 0 := mul_ne_zero hh0 ((map_ne_zero_iff _ (algebraMap C F).injective).2 he0)
  have hσh' : σ h' = h' := by rw [map_mul, hσh, algEquiv_algebraMap_C]
  have hξh' : ξ' h' = ξ' h := by
    rw [map_mul, hconst]
    have : ‖1 + x‖₊ = 1 := NNReal.coe_injective he1
    rw [this, mul_one]
  have hle' := le_valuation_pow_sub hp0 hconst hζ hσξ hh'0 hσθ hσh'
  -- the binomial expansion
  set R := (1 + x) ^ p - 1 - x ^ p - p * x
  have hR : ‖R‖ ≤ ‖(p : C)‖ * ‖x‖ ^ 2 := PthPower.norm_one_add_pow_sub_le hp hx1.le
  have hexp : (1 + x) ^ p - 1 = γ ^ p * b + R := by
    simp only [R, x]
    rw [← hc, mul_pow, hγp]
    ring
  have hRlt : ‖R‖ < ‖γ‖ ^ p := by
    calc ‖R‖ ≤ ‖(p : C)‖ * ‖x‖ ^ 2 := hR
      _ ≤ ‖γ‖ ^ (p - 1) * ‖γ‖ ^ 2 := by
          have hpγ : ‖(p : C)‖ = ‖γ‖ ^ (p - 1) := by rw [← norm_pow, hγ, norm_neg]
          rw [hpγ]
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
            (pow_nonneg (norm_nonneg _) _)
          rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hc1
      _ = ‖γ‖ ^ p * ‖γ‖ := by
          rw [← pow_add, ← pow_succ]; congr 1; have := hp.two_le; omega
      _ < ‖γ‖ ^ p := mul_lt_of_lt_one_right (pow_pos (norm_pos_iff.2 hγ0) p) hγ1
  -- `θ^p - h'^p = h^p (γ^p (u - b) - R)`
  have hmain : θ ^ p - h' ^ p =
      h ^ p * (algebraMap C F (γ ^ p) * (u - algebraMap C F b) - algebraMap C F R) := by
    have ht : θ = t * h := by simp only [t]; field_simp
    have hu : t ^ p - 1 = algebraMap C F (γ ^ p) * u := by
      simp only [u]; field_simp
    have hR' : algebraMap C F ((1 + x) ^ p) = 1 + algebraMap C F (γ ^ p * b + R) := by
      rw [← hexp]; simp
    simp only [h', mul_pow, ← map_pow (algebraMap C F) (1 + x), hR']
    rw [ht, mul_pow]
    have : t ^ p = 1 + algebraMap C F (γ ^ p) * u := by rw [← hu]; ring
    rw [this, map_add, map_mul]
    ring
  have hlt : ξ' (θ ^ p - h' ^ p) < ‖1 - ζ‖₊ ^ p * ξ' h' ^ p := by
    rw [hmain, map_mul, map_pow, hξh', hδ, mul_comm]
    refine mul_lt_mul_of_pos_right ?_ (pow_pos hξh p)
    refine (Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul, hconst, nnnorm_pow]
      exact mul_lt_of_lt_one_right (pow_pos (nnnorm_pos.2 hγ0) p) hb
    · rw [hconst]
      exact_mod_cast hRlt
  exact absurd hle' (not_le.2 hlt)

end Strict

end TypeFour

end SemistableReduction
