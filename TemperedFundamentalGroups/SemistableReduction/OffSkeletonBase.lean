/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DiscCondSmooth
import TemperedFundamentalGroups.SemistableReduction.SectionLift

/-!
# Smooth points from a local coordinate

Blueprint §9.12, O11 (T⇒), off-skeleton clause (lemma (L)), algebraic part.

* `OffSkeleton.zeros_sub_of_adjoin_eq_top`, `exists_rep`: on a rational residue curve `κ = k(z)`,
  `z - ζ` has a single simple zero, and `O_R` consists of the `A(z)/B(z)` with `B(z)` a unit;
* `OffSkeleton.isDiscSmooth_of_coord`: a point of `DRint 0 1 H` over the residue point is smooth
  if a branch `(v, R)` through it has `κ(v) = k(ū)`, `x̄ + 1 = λ ūᵈ`, and there are `Y₁, Y₂ ∈ R'`
  with `Ȳ₂ = (x̄ + 1)ᵐ`, `Ȳ₁ = μ Ȳ₂ ū` at `v` and `Ȳ₂ = 0` at every other extension;
* `OffSkeleton.exists_pow_mul_isIntegral_of_nodeRing`: elements integral over the node chart become
  integral over `C[x]` after multiplication by a power of `x`.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace OffSkeleton

open PlaceNorm CurvePlace

section Core

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

omit [IsAlgClosed k] in
lemma notMem_range_of_adjoin_eq_top {z : κ} (hz : k⟮z⟯ = ⊤) : z ∉ (algebraMap k κ).range := by
  rintro ⟨c, rfl⟩
  obtain ⟨x, hx, -⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ)
  have hxm : x ∈ k⟮algebraMap k κ c⟯ := by rw [hz]; exact IntermediateField.mem_top
  rw [IntermediateField.adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ c),
    IntermediateField.mem_bot] at hxm
  obtain ⟨b, rfl⟩ := hxm
  exact hx (isAlgebraic_algebraMap b)

/-- **A coordinate of a rational curve**: if `κ = k(z)` and `ζ ∈ k`, then `z - ζ` has exactly one
zero, of order one. -/
lemma zeros_sub_of_adjoin_eq_top {z : κ} (hz : k⟮z⟯ = ⊤) (ζ : k) :
    (zeros k (z - algebraMap k κ ζ)).card = 1 ∧
      ∀ R ∈ zeros k (z - algebraMap k κ ζ), R.valuation (z - algebraMap k κ ζ) = exp (-1) := by
  have hzr := notMem_range_of_adjoin_eq_top hz
  have hyr : z - algebraMap k κ ζ ∉ (algebraMap k κ).range := by
    rintro ⟨c, hc⟩
    exact hzr ⟨c + ζ, by rw [map_add, hc, sub_add_cancel]⟩
  have htop : k⟮z - algebraMap k κ ζ⟯ = ⊤ := by
    refine eq_top_iff.2 (hz ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)
    have h := add_mem (IntermediateField.mem_adjoin_simple_self k (z - algebraMap k κ ζ))
      (IntermediateField.algebraMap_mem k⟮z - algebraMap k κ ζ⟯ ζ)
    rwa [sub_add_cancel] at h
  have hf : Module.finrank k⟮z - algebraMap k κ ζ⟯ κ = 1 := by
    rw [htop, IntermediateField.finrank_top]
  have hs := sum_ord hyr
  rw [hf] at hs
  have hpos : ∀ R ∈ zeros k (z - algebraMap k κ ζ), 1 ≤ ord (z - algebraMap k κ ζ) R :=
    fun R hR ↦ one_le_ord hR
  have hle := Finset.card_nsmul_le_sum _ _ 1 hpos
  rw [smul_eq_mul, mul_one, hs] at hle
  have hne : (zeros k (z - algebraMap k κ ζ)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hs
    exact zero_ne_one hs
  have hcard : (zeros k (z - algebraMap k κ ζ)).card = 1 := le_antisymm hle hne.card_pos
  refine ⟨hcard, fun R hR ↦ ?_⟩
  obtain ⟨R₀, hR₀⟩ := Finset.card_eq_one.1 hcard
  rw [hR₀, Finset.sum_singleton] at hs
  rw [hR₀, Finset.mem_singleton] at hR
  subst hR
  rw [valuation_x (hR₀ ▸ Finset.mem_singleton_self R), hs]
  rfl

/-- A polynomial in `z` not vanishing at `R.res z` is a unit at `R`. -/
lemma valuation_aeval_eq_one_of_not_dvd (R : CurvePlace k κ) {z : κ} (hzR : z ∈ R.V)
    (hR : R.valuation (z - algebraMap k κ (R.res z)) < 1) {P : k[X]}
    (hP : ¬ (X - Polynomial.C (R.res z)) ∣ P) : R.valuation (aeval z P) = 1 := by
  set ζ := R.res z
  have h := modByMonic_add_div P (X - Polynomial.C ζ)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  have he : P.eval ζ ≠ 0 := fun h0 ↦ hP (dvd_iff_isRoot.2 h0)
  have hz : aeval z P = algebraMap k κ (P.eval ζ) +
      (z - algebraMap k κ ζ) * aeval z (P /ₘ (X - Polynomial.C ζ)) := by
    conv_lhs => rw [← h]
    simp [map_add, map_mul, aeval_C, aeval_X]
  have hk : ∀ c : k, R.valuation (algebraMap k κ c) ≤ 1 := R.valuation_algebraMap_le_one
  rw [hz, Valuation.map_add_eq_of_lt_left, valuation_algebraMap_eq_one hk he]
  rw [valuation_algebraMap_eq_one hk he, map_mul]
  exact mul_lt_one_of_lt_of_le hR (valuation_aeval_le_one hk (R.valuation_le_one_iff.2 hzR) _)

/-- **Local representation on a rational curve**: if `κ = k(z)`, every `α ∈ O_R` is `A(z)/B(z)`
with `B(z)` a unit at `R`. -/
lemma exists_rep {z : κ} (hz : k⟮z⟯ = ⊤) (R : CurvePlace k κ) (hzR : z ∈ R.V) {α : κ}
    (hα : α ∈ R.V) : ∃ A B : k[X], R.valuation (aeval z B) = 1 ∧ α * aeval z B = aeval z A := by
  classical
  rcases eq_or_ne α 0 with rfl | hα0
  · exact ⟨0, 1, by simp, by simp⟩
  set ζ := R.res z
  have hlt : R.valuation (z - algebraMap k κ ζ) < 1 := R.valuation_sub_res_lt_one hzR
  obtain ⟨-, hval⟩ := zeros_sub_of_adjoin_eq_top hz ζ
  have hne : z - algebraMap k κ ζ ≠ 0 := by
    intro h0
    exact notMem_range_of_adjoin_eq_top hz ⟨ζ, (sub_eq_zero.1 h0).symm⟩
  have hRz : R ∈ zeros k (z - algebraMap k κ ζ) := by
    rw [mem_zeros, ← R.valuation_le_one_iff, map_inv₀, not_le,
      one_lt_inv₀ ((Valuation.pos_iff _).2 hne)]
    exact hlt
  have h1 := hval R hRz
  obtain ⟨r, s, hrs⟩ :=
    (IntermediateField.mem_adjoin_simple_iff k α).1 (hz ▸ IntermediateField.mem_top)
  have hs0 : aeval z s ≠ 0 := fun h0 ↦ hα0 (by rw [hrs, h0, div_zero])
  have hr0 : aeval z r ≠ 0 := fun h0 ↦ hα0 (by rw [hrs, h0, zero_div])
  have hsp : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
  have hrp : r ≠ 0 := by rintro rfl; exact hr0 (map_zero _)
  obtain ⟨s₀, hs, hs₀⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd s hsp ζ
  obtain ⟨r₀, hr, hr₀⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hrp ζ
  set ks := s.rootMultiplicity ζ
  set kr := r.rootMultiplicity ζ
  have hvs₀ := valuation_aeval_eq_one_of_not_dvd R hzR hlt hs₀
  have hvr₀ := valuation_aeval_eq_one_of_not_dvd R hzR hlt hr₀
  have hαs : α * aeval z s = aeval z r := by rw [hrs, div_mul_cancel₀ _ hs0]
  have hzs : aeval z s = (z - algebraMap k κ ζ) ^ ks * aeval z s₀ := by
    conv_lhs => rw [hs]
    simp [map_mul, map_pow, map_sub, aeval_X, aeval_C]
  have hzr : aeval z r = (z - algebraMap k κ ζ) ^ kr * aeval z r₀ := by
    conv_lhs => rw [hr]
    simp [map_mul, map_pow, map_sub, aeval_X, aeval_C]
  -- `ks ≤ kr`
  have hle : ks ≤ kr := by
    have h := congrArg R.valuation hαs
    rw [hzs, hzr, map_mul, map_mul, map_mul, map_pow, map_pow, h1, hvs₀, hvr₀, mul_one,
      mul_one] at h
    by_contra hlt'
    push Not at hlt'
    have hαle : R.valuation α ≤ 1 := R.valuation_le_one_iff.2 hα
    have : exp (-1 : ℤ) ^ ks < exp (-1 : ℤ) ^ kr := by
      rw [← exp_nsmul, ← exp_nsmul, exp_lt_exp]
      simp only [smul_neg, nsmul_eq_mul, mul_one, neg_lt_neg_iff]
      exact_mod_cast hlt'
    have h2 : R.valuation α * exp (-1 : ℤ) ^ ks ≤ exp (-1 : ℤ) ^ ks :=
      mul_le_of_le_one_left zero_le hαle
    rw [h] at h2
    exact absurd (this.trans_le h2) (lt_irrefl _)
  refine ⟨(X - Polynomial.C ζ) ^ (kr - ks) * r₀, s₀, hvs₀, ?_⟩
  have hpow : (z - algebraMap k κ ζ) ^ ks ≠ 0 := pow_ne_zero _ hne
  apply mul_left_cancel₀ hpow
  have hsplit : (z - algebraMap k κ ζ) ^ kr =
      (z - algebraMap k κ ζ) ^ ks * (z - algebraMap k κ ζ) ^ (kr - ks) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  calc (z - algebraMap k κ ζ) ^ ks * (α * aeval z s₀) = α * aeval z s := by rw [hzs]; ring
    _ = aeval z r := hαs
    _ = _ := by
      rw [hzr, hsplit]
      simp [map_mul, map_pow, map_sub, aeval_X, aeval_C]
      ring

end Core

section Smooth

open GaussFibre GaussTube DiscCount SmoothVertex

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {H : Type*} [Field H] [Algebra (RatFunc C) H] [Algebra C H]
  [IsScalarTower C (RatFunc C) H] [FiniteDimensional (RatFunc C) H]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [IsAlgClosed C] in
/-- A lift of a residue to `O_C`. -/
noncomputable def lift (c : 𝓀) : HenselComplete.integers C := (residue_surjective c).choose

omit [IsAlgClosed C] in
lemma residue_lift (c : 𝓀) : residue _ (lift c) = c := (residue_surjective c).choose_spec

/-- The homogenized polynomial `Σ cᵢ Y₁ⁱ (μ Y₂)ⁿ⁻ⁱ` in `R'`. -/
noncomputable def homEval (n : ℕ) (A : 𝓀[X]) (Y₁ Y₂ : DRint (0 : C) 1 H) (b : 𝓀) :
    DRint (0 : C) 1 H :=
  ∑ i ∈ Finset.range (n + 1), constD (lift (A.coeff i)) * Y₁ ^ i * (constD (lift b) * Y₂) ^ (n - i)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) H] in
lemma redD_homEval (v : Ext C H) {n : ℕ} {A : 𝓀[X]} (hA : A.natDegree ≤ n)
    (Y₁ Y₂ : DRint (0 : C) 1 H) (b : 𝓀) (u : ResidueField v.1.valuationSubring)
    (hY : redD v Y₁ = algebraMap 𝓀 _ b * redD v Y₂ * u) :
    redD v (homEval n A Y₁ Y₂ b) = (algebraMap 𝓀 _ b * redD v Y₂) ^ n * aeval u A := by
  rw [homEval, map_sum, aeval_eq_sum_range' (Nat.lt_succ_of_le hA), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [map_mul, map_pow, redD_constD, residue_lift, hY, Algebra.smul_def]
  rw [show n = i + (n - i) by omega, pow_add]
  rw [Nat.add_sub_cancel_left]
  ring

/-- **Smoothness from a local coordinate.** Let `(v, R)` be a branch through a point `P'` of
`R' = DRint 0 1 H` over the residue point, and suppose `κ(v) = k(ū)` with `x̄ + 1 = λ ūᵈ`, and
`Y₁, Y₂ ∈ R'` with `Ȳ₂ = (x̄ + 1)ᵐ`, `Ȳ₁ = μ Ȳ₂ ū` at `v` and `Ȳ₂ = 0` at every other extension.
Then `P'` is a smooth point. -/
theorem isDiscSmooth_of_coord (P : Ideal (DRint (0 : C) 1 H)) (v : Ext C H)
    {R : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hR : R ∈ zeros 𝓀 (red C (xF C H) v)) (hRP : placeIdealD v hR = P)
    {U : H} (htop : 𝓀⟮red C U v⟯ = ⊤) {d : ℕ} (hd : 1 ≤ d) {lam : 𝓀}
    (hx : red C (xF C H) v + 1 = algebraMap 𝓀 _ lam * red C U v ^ d)
    {Y₁ Y₂ : DRint (0 : C) 1 H} {m : ℕ} {mu : 𝓀} (hmu : mu ≠ 0)
    (hY₂ : redD v Y₂ = (red C (xF C H) v + 1) ^ m)
    (hY₁ : redD v Y₁ = algebraMap 𝓀 _ mu * redD v Y₂ * red C U v)
    (hoth : ∀ v' : Ext C H, v' ≠ v → redD v' Y₂ = 0) : IsDiscSmooth P := by
  classical
  set ū := red C U v
  set xb := red C (xF C H) v
  have hk : ∀ (R' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (c : 𝓀),
      R'.valuation (algebraMap 𝓀 _ c) ≤ 1 := fun R' ↦ R'.valuation_algebraMap_le_one
  -- facts at a zero `R'` of `xb`
  have hx1 : ∀ R' ∈ zeros 𝓀 xb, R'.valuation (xb + 1) = 1 := fun R' hR' ↦ by
    rw [add_comm, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact valuation_x_lt_one hR'),
      map_one]
  have huV : ∀ R' ∈ zeros 𝓀 xb, ū ∈ R'.V := fun R' hR' ↦ by
    rw [← R'.valuation_le_one_iff]
    have h := hx1 R' hR'
    rw [hx, map_mul] at h
    have h2 : R'.valuation ū ^ d ≤ 1 := by
      rw [← map_pow]
      rcases eq_or_ne lam 0 with h0 | h0
      · rw [h0, map_zero, map_zero, zero_mul] at h
        exact absurd h zero_ne_one
      · rw [valuation_algebraMap_eq_one (hk R') h0, one_mul] at h
        exact h.le
    exact (pow_le_one_iff_of_nonneg zero_le (by omega)).1 h2
  have hY₂1 : ∀ R' ∈ zeros 𝓀 xb, R'.valuation (redD v Y₂) = 1 := fun R' hR' ↦ by
    rw [hY₂, map_pow, hx1 R' hR', one_pow]
  set ζ := R.res ū
  have hzeros := zeros_sub_of_adjoin_eq_top htop ζ
  have hne : ū - algebraMap 𝓀 _ ζ ≠ 0 := fun h0 ↦
    notMem_range_of_adjoin_eq_top htop ⟨ζ, (sub_eq_zero.1 h0).symm⟩
  have hmemz : ∀ R' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring),
      R' ∈ zeros 𝓀 (ū - algebraMap 𝓀 _ ζ) ↔ R'.valuation (ū - algebraMap 𝓀 _ ζ) < 1 :=
    fun R' ↦ SmoothDisc.mem_zeros_iff_lt_one R' hne
  have hRz : R ∈ zeros 𝓀 (ū - algebraMap 𝓀 _ ζ) :=
    (hmemz R).2 (R.valuation_sub_res_lt_one (huV R hR))
  -- the separating elements
  set y₃ : DRint (0 : C) 1 H := Y₂ - 1
  set y₁ : DRint (0 : C) 1 H := Y₁ - constD (lift (mu * ζ)) * Y₂
  have hy₁ : redD v y₁ = algebraMap 𝓀 _ mu * redD v Y₂ * (ū - algebraMap 𝓀 _ ζ) := by
    simp only [y₁, map_sub, map_mul, redD_constD, residue_lift, hY₁]
    ring
  have hy₃ : redD v y₃ = (∑ i ∈ Finset.range m, (xb + 1) ^ i) * xb := by
    simp only [y₃, map_sub, map_one, hY₂]
    have := geom_sum_mul (xb + 1) m
    rw [add_sub_cancel_right] at this
    exact this.symm
  have hP3 : y₃ ∈ P := by
    rw [← hRP, mem_placeIdealD_iff, res_eq_zero_iff R (redD_mem_V v y₃ (xbar_mem_V v hR)), hy₃,
      map_mul]
    have ha : R.valuation (∑ i ∈ Finset.range m, (xb + 1) ^ i) ≤ 1 :=
      R.valuation_le_one_iff.2 (sum_mem fun i _ ↦ pow_mem (add_mem (xbar_mem_V v hR)
        (one_mem _)) _)
    exact (mul_le_mul_left ha _).trans_lt (by rw [one_mul]; exact valuation_x_lt_one hR)
  have hP1 : y₁ ∈ P := by
    rw [← hRP, mem_placeIdealD_iff, res_eq_zero_iff R (redD_mem_V v y₁ (xbar_mem_V v hR)), hy₁,
      map_mul, map_mul, valuation_algebraMap_eq_one (hk R) hmu, one_mul, hY₂1 R hR, one_mul]
    exact (hmemz R).1 hRz
  refine ⟨⟨v, ⟨R, hR⟩⟩, Set.ext fun b ↦ ?_, fun α hα ↦ ?_⟩
  · obtain ⟨v', R', hR'⟩ := b
    rw [Set.mem_singleton_iff]
    constructor
    · intro hb
      have hb' : placeIdealD v' hR' = P := hb
      have hv : v' = v := by
        by_contra hne'
        have h3 := hb' ▸ hP3
        rw [mem_placeIdealD_iff] at h3
        simp only [y₃, map_sub, map_one, hoth v' hne', zero_sub] at h3
        rw [show (-1 : ResidueField v'.1.valuationSubring) = algebraMap 𝓀 _ (-1) by simp,
          R'.res_algebraMap] at h3
        exact one_ne_zero (neg_eq_zero.1 h3)
      subst hv
      have h1 := hb' ▸ hP1
      rw [mem_placeIdealD_iff, res_eq_zero_iff R' (redD_mem_V v' y₁ (xbar_mem_V v' hR')), hy₁,
        map_mul, map_mul, valuation_algebraMap_eq_one (hk R') hmu, one_mul, hY₂1 R' hR',
        one_mul] at h1
      have hR'z := (hmemz R').2 h1
      obtain ⟨R₀, hR₀⟩ := Finset.card_eq_one.1 hzeros.1
      rw [hR₀, Finset.mem_singleton] at hR'z hRz
      subst hR'z
      subst hRz
      rfl
    · intro h
      rw [h]
      exact hRP
  · obtain ⟨A, B, hB1, hAB⟩ := exists_rep htop R (huV R hR) hα
    set n := max A.natDegree B.natDegree
    refine ⟨homEval n A Y₁ Y₂ mu, homEval n B Y₁ Y₂ mu, ?_, ?_⟩
    · rw [← hRP, mem_placeIdealD_iff,
        res_eq_zero_iff R (redD_mem_V v _ (xbar_mem_V v hR)),
        redD_homEval v (le_max_right _ _) Y₁ Y₂ mu ū hY₁, map_mul, map_pow, map_mul,
        valuation_algebraMap_eq_one (hk R) hmu, one_mul, hY₂1 R hR, one_pow, one_mul, hB1]
      exact lt_irrefl 1
    · have hAB' : α * aeval ū B = aeval ū A := hAB
      change redD v _ = α * redD v _
      rw [redD_homEval v (le_max_left _ _) Y₁ Y₂ mu ū hY₁,
        redD_homEval v (le_max_right _ _) Y₁ Y₂ mu ū hY₁]
      linear_combination (-(algebraMap 𝓀 _ mu * redD v Y₂) ^ max A.natDegree B.natDegree) * hAB'

end Smooth

section Node

open GaussTube GaussFibre GaussStability AffineTwist PlaceNorm SmoothDisc DiscCount SmoothVertex
  CurvePlace

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField GaussFibre.isCurveFunctionField_F

/-- The node chart lies in the valuation ring of every place of `G / C` at which `x` is a unit. -/
lemma nodeRing_le_V (c : C) (P : CurvePlace C G) (hx : xF C G ∈ P.V) (hxi : (xF C G)⁻¹ ∈ P.V)
    (r : nodeRing c) : P.valuation (algebraMap (nodeRing c) G r) ≤ 1 := by
  rw [P.valuation_le_one_iff]
  obtain ⟨r, hr⟩ := r
  change algebraMap (RatFunc C) G r ∈ P.V
  have hle : nodeRing c ≤ P.V.toSubring.comap (algebraMap (RatFunc C) G) := by
    refine Subring.closure_le.2 fun f hf ↦ ?_
    rcases hf with ⟨o, -, rfl⟩ | hf
    · change algebraMap (RatFunc C) G (algebraMap C (RatFunc C) o) ∈ P.V
      rw [← IsScalarTower.algebraMap_apply]
      exact P.algebraMap_mem o
    · rcases hf with rfl | rfl
      · exact hx
      · change algebraMap (RatFunc C) G (algebraMap C (RatFunc C) c / RatFunc.X) ∈ P.V
        rw [map_div₀, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv]
        exact mul_mem (P.algebraMap_mem c) hxi
  exact hle hr

/-- Elements integral over the node chart become integral over `C[x]` after multiplication by a
power of `x`. -/
lemma exists_pow_mul_isIntegral_of_nodeRing (c : C) {q : G} (hq : IsIntegral (nodeRing c) q) :
    ∃ D : ℕ, IsIntegral (Algebra.adjoin C {xF C G}) (xF C G ^ D * q) := by
  refine ⟨poleNorm C q, GaussFibre.isIntegral_of_forall_mem fun P hP ↦ ?_⟩
  by_cases hxi : (xF C G)⁻¹ ∈ P.V
  · exact mul_mem (pow_mem hP _) (P.valuation_le_one_iff.1
      (GaussFibre.valuation_le_one_of_isIntegral (nodeRing_le_V c P hP hxi) hq))
  · rw [← P.valuation_le_one_iff, map_mul, map_pow]
    have hv : P.valuation (xF C G) = (exp (P.poleOrder (xF C G)⁻¹ : ℤ))⁻¹ := by
      rw [← P.valuation_eq_exp_poleOrder hxi, map_inv₀, inv_inv]
    rw [hv]
    have h1 := P.one_le_poleOrder hxi
    have h2 := (P.valuation_le_exp_poleOrder q).trans
      (exp_le_exp.2 (by exact_mod_cast poleOrder_le_poleNorm P q :
        (P.poleOrder q : ℤ) ≤ poleNorm C q))
    calc (exp (P.poleOrder (xF C G)⁻¹ : ℤ))⁻¹ ^ poleNorm C q * P.valuation q ≤
        (exp (P.poleOrder (xF C G)⁻¹ : ℤ))⁻¹ ^ poleNorm C q * exp (poleNorm C q : ℤ) := by
          gcongr
      _ ≤ 1 := by
        rw [← exp_neg, ← exp_nsmul, ← exp_add, ← exp_zero, exp_le_exp, smul_neg, nsmul_eq_mul]
        have : (1 : ℤ) ≤ P.poleOrder (xF C G)⁻¹ := by exact_mod_cast h1
        nlinarith [Int.natCast_nonneg (poleNorm C q)]

end Node

end OffSkeleton

end SemistableReduction
