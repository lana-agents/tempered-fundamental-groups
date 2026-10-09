/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.HenselComplete
import TemperedFundamentalGroups.SemistableReduction.Unramified

/-!
# Unique extension of a complete rank-one valuation

Blueprint §9.4, C3. Let `K` be a complete non-archimedean nontrivially normed field, `u` the
valuation `x ↦ ‖x‖₊` of `K` (`NormedField.valuation`), `L / K` an algebraic extension and `w` any
valuation on `L` (with arbitrary value group) extending `u`.

* `valuation_le_one_iff`: `w x ≤ 1 ↔ ‖x‖_sp ≤ 1`, where `‖·‖_sp` is the spectral norm
  (`spectralNorm K L`, which is the unique norm on `L` extending the norm of `K`,
  `spectralNorm_unique`). Hence the valuation ring of `w` does not depend on `w`
  (`valuationSubring_eq`), and any two extensions of `u` to `L` are equivalent (`isEquiv`).
* `valuation_algEquiv_apply`: every `K`-automorphism of `L` preserves `w`: `w (σ x) = w x`.
* `henselianLocalRing_valuationSubring`: if `L / K` is finite, then `L` with the spectral norm is
  complete (`spectralNorm.completeSpace`, Mathlib), so the valuation ring of `w` is a Henselian
  local ring (C1, `HenselComplete.henselianLocalRing`).
* `henselianLocalRing_comap`, `valuation_algEquiv_apply'`: the same for the restrictions of `w`
  to the intermediate fields of a tower `K ⊆ M ⊆ N` with `N / K` finite, and for
  `M`-automorphisms of `N`. These are the hypotheses of the Hensel toolkit (C2, C4) and of the
  inertia group (D1–D3).

The key point is a dominance argument (`not_aeval_eq_zero_of_dominant`): if one term of a monic
polynomial equation has strictly larger value than all others, the equation cannot hold.
-/

open Polynomial Valuation

namespace SemistableReduction

namespace UniqueExtension

section Dominant

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

/-- **Dominance.** If `z` is a root of a monic `P` over `K` and the leading term `z ^ d` has
strictly larger value than all other terms, we have a contradiction. -/
theorem not_aeval_eq_zero_of_dominant {P : K[X]} (hP : P.Monic) {z : L} (hz : aeval z P = 0)
    (h : ∀ i < P.natDegree, w (algebraMap K L (P.coeff i)) * w z ^ i < w z ^ P.natDegree) :
    False := by
  set d := P.natDegree
  have hd0 : w z ^ d ≠ 0 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, pow_zero]; exact one_ne_zero
    · exact ne_of_gt (lt_of_le_of_lt zero_le (h 0 hd))
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_smul,
    add_eq_zero_iff_eq_neg'] at hz
  have hlt : w (∑ i ∈ Finset.range d, P.coeff i • z ^ i) < w z ^ d := by
    refine Valuation.map_sum_lt w hd0 fun i hi ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow]
    exact h i (Finset.mem_range.1 hi)
  rw [← Valuation.map_neg, ← hz, map_pow] at hlt
  exact lt_irrefl _ hlt

end Dominant

section Order

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

lemma one_le_inv_of_le_one {a : Γ} (h0 : a ≠ 0) (h : a ≤ 1) : 1 ≤ a⁻¹ := by
  rw [← mul_le_mul_iff_right₀ (zero_lt_iff.2 h0)]
  simpa [h0] using h

lemma one_le_of_inv_le_one {a : Γ} (h0 : a ≠ 0) (h : a⁻¹ ≤ 1) : 1 ≤ a := by
  simpa using one_le_inv_of_le_one (inv_ne_zero h0) h

end Order

/-- The coefficients of a monic polynomial with spectral value `< 1` (other than the leading one)
have norm `< 1`. -/
lemma norm_coeff_lt_one_of_spectralValue_lt_one {K : Type*} [NormedField K] {P : K[X]}
    (hP : spectralValue P < 1) {i : ℕ}
    (hi : i < P.natDegree) : ‖P.coeff i‖ < 1 := by
  have h := (le_ciSup (spectralValueTerms_bddAbove P) i).trans_lt hP
  rw [spectralValueTerms_of_lt_natDegree _ hi] at h
  by_contra! h1
  have : (1 : ℝ) ≤ ‖P.coeff i‖ ^ (1 / ((P.natDegree : ℝ) - i)) :=
    Real.one_le_rpow h1 (by
      rw [one_div_nonneg, sub_nonneg, Nat.cast_le]
      exact hi.le)
  exact lt_irrefl _ (h.trans_le this)

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {L : Type*} [Field L] [Algebra K L]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
  [(NormedField.valuation (K := K)).HasExtension w]

lemma valuation_algebraMap_le_one_iff (c : K) : w (algebraMap K L c) ≤ 1 ↔ ‖c‖ ≤ 1 := by
  rw [HasExtension.val_map_le_one_iff (vR := NormedField.valuation (K := K)),
    NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

lemma valuation_algebraMap_lt_one_iff (c : K) : w (algebraMap K L c) < 1 ↔ ‖c‖ < 1 := by
  rw [HasExtension.val_map_lt_one_iff (vR := NormedField.valuation (K := K)),
    NormedField.valuation_apply, ← NNReal.coe_lt_coe]
  simp

variable [CompleteSpace K] [Algebra.IsAlgebraic K L]

/-- **Unique extension.** The valuation ring of any extension `w` of the valuation of a complete
non-archimedean field `K` to an algebraic extension `L` is the unit ball of the spectral
norm. -/
theorem valuation_le_one_iff (x : L) : w x ≤ 1 ↔ spectralNorm K L x ≤ 1 := by
  constructor
  · intro hw
    by_contra! hsp
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [spectralNorm_zero] at hsp
      exact lt_irrefl _ (hsp.trans zero_lt_one)
    set y := x⁻¹
    have hy : spectralNorm K L y < 1 := by
      have h1 : spectralNorm K L x * spectralNorm K L y = 1 := by
        rw [← spectralAlgNorm_def, ← spectralAlgNorm_def, ← spectralAlgNorm_mul,
          mul_inv_cancel₀ hx0, spectralAlgNorm_one]
      by_contra! h2
      have : 1 < spectralNorm K L x * spectralNorm K L y := by nlinarith
      rw [h1] at this
      exact lt_irrefl _ this
    have hwy : 1 ≤ w y := by
      rw [map_inv₀]
      exact one_le_inv_of_le_one ((Valuation.ne_zero_iff w).2 hx0) hw
    set P := minpoly K y
    have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
    refine not_aeval_eq_zero_of_dominant w hP (minpoly.aeval K y) fun i hi ↦ ?_
    have hc : w (algebraMap K L (P.coeff i)) < 1 :=
      (valuation_algebraMap_lt_one_iff w _).2 (norm_coeff_lt_one_of_spectralValue_lt_one hy hi)
    have hpos : 0 < w y ^ i := pow_pos (lt_of_lt_of_le zero_lt_one hwy) i
    calc w (algebraMap K L (P.coeff i)) * w y ^ i < w y ^ i := mul_lt_of_lt_one_left hpos hc
      _ ≤ w y ^ P.natDegree := pow_le_pow_right₀ hwy hi.le
  · intro hsp
    by_contra! hw
    set P := minpoly K x
    have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
    have hcoeff := (spectralValue_le_one_iff hP).1 hsp
    refine not_aeval_eq_zero_of_dominant w hP (minpoly.aeval K x) fun i hi ↦ ?_
    have hc : w (algebraMap K L (P.coeff i)) ≤ 1 :=
      (valuation_algebraMap_le_one_iff w _).2 (hcoeff i)
    calc w (algebraMap K L (P.coeff i)) * w x ^ i ≤ w x ^ i :=
          mul_le_of_le_one_left zero_le hc
      _ < w x ^ P.natDegree := pow_lt_pow_right₀ hw hi

/-- The valuation ring of an extension of the valuation of `K` to `L` is independent of the
extension. -/
theorem valuationSubring_eq {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (w' : Valuation L Γ') [(NormedField.valuation (K := K)).HasExtension w'] :
    w.valuationSubring = w'.valuationSubring := by
  ext x
  rw [mem_valuationSubring_iff, mem_valuationSubring_iff, valuation_le_one_iff (K := K),
    valuation_le_one_iff (K := K)]

/-- Any two extensions of the valuation of `K` to `L` are equivalent. -/
theorem isEquiv {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (w' : Valuation L Γ') [(NormedField.valuation (K := K)).HasExtension w'] :
    w.IsEquiv w' :=
  (isEquiv_iff_valuationSubring w w').2 (valuationSubring_eq (K := K) w w')

/-- `K`-automorphisms preserve the valuation ring. -/
lemma valuation_algEquiv_le_one_iff (σ : L ≃ₐ[K] L) (x : L) : w (σ x) ≤ 1 ↔ w x ≤ 1 := by
  rw [valuation_le_one_iff (K := K), valuation_le_one_iff (K := K), ← spectralNorm_eq_of_equiv]

/-- **Automorphisms are isometries.** Every `K`-automorphism of `L` preserves `w`. -/
theorem valuation_algEquiv_apply (σ : L ≃ₐ[K] L) (x : L) : w (σ x) = w x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero]
  obtain ⟨n, hn, c, hc0, hc⟩ :=
    FundamentalInequality.exists_pow_valuation_eq w (Algebra.IsIntegral.isIntegral (R := K) x) hx0
  have hc' : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  set t := x ^ n / algebraMap K L c
  have hwc : w (algebraMap K L c) ≠ 0 := (Valuation.ne_zero_iff w).2 hc'
  have ht : w t = 1 := by
    rw [map_div₀, map_pow, hc, div_self hwc]
  have hσt : w (σ t) = 1 := by
    have h1 : w (σ t) ≤ 1 := (valuation_algEquiv_le_one_iff w σ t).2 ht.le
    have h2 : w (σ t⁻¹) ≤ 1 := (valuation_algEquiv_le_one_iff w σ t⁻¹).2 (by
      rw [map_inv₀, ht, inv_one])
    rw [map_inv₀, map_inv₀] at h2
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at ht
      exact zero_ne_one ht
    have hσt0 : w (σ t) ≠ 0 := (Valuation.ne_zero_iff w).2 ((_root_.map_ne_zero σ).2 ht0)
    exact le_antisymm h1 (one_le_of_inv_le_one hσt0 h2)
  have : w (σ x) ^ n = w x ^ n := by
    rw [hc, ← map_pow, ← map_pow, ← div_mul_cancel₀ (x ^ n) hc', map_mul, map_mul,
      AlgEquiv.commutes, hσt, one_mul]
  exact (pow_left_inj₀ zero_le zero_le hn.ne').1 this

section Henselian

variable [FiniteDimensional K L]

variable (K) in
include K in
/-- **Hensel's lemma for finite extensions.** The valuation ring of any extension `w` of the
valuation of `K` to a finite extension `L` is a Henselian local ring: it is the ring of integers
of `L` with the spectral norm, which is complete. -/
theorem henselianLocalRing_valuationSubring : HenselianLocalRing w.valuationSubring := by
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  haveI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  haveI : CompleteSpace L := spectralNorm.completeSpace K L
  have h : HenselComplete.integers L = w.valuationSubring := by
    ext x
    rw [HenselComplete.mem_integers_iff, mem_valuationSubring_iff,
      valuation_le_one_iff (K := K)]
    rfl
  have := HenselComplete.henselianLocalRing (K := L)
  rw [h] at this
  exact this

end Henselian

section Tower

variable {M N : Type*} [Field M] [Field N] [Algebra K M] [Algebra K N] [Algebra M N]
  [IsScalarTower K M N] [FiniteDimensional K N] (v : Valuation N Γ)
  [(NormedField.valuation (K := K)).HasExtension v]

variable (K) in
include K in
/-- In a tower `K ⊆ M ⊆ N` with `N / K` finite, the valuation rings of the restrictions of an
extension `v` of the valuation of `K` to the intermediate fields of `N / M` are Henselian. -/
theorem henselianLocalRing_comap (E : IntermediateField M N) :
    HenselianLocalRing (v.comap (algebraMap E N)).valuationSubring := by
  have : IsScalarTower K E N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsAlgebraic K E :=
    Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom K E N) (algebraMap E N).injective
  have : FiniteDimensional K E :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom K E N).toLinearMap
      (algebraMap E N).injective
  exact henselianLocalRing_valuationSubring K (v.comap (algebraMap E N))

variable (K) in
include K in
/-- In a tower `K ⊆ M ⊆ N` with `N / K` finite, every `M`-automorphism of `N` preserves an
extension `v` of the valuation of `K`. -/
theorem valuation_algEquiv_apply' (σ : N ≃ₐ[M] N) (x : N) : v (σ x) = v x :=
  have : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.of_finite K N
  valuation_algEquiv_apply (K := K) v (σ.restrictScalars K) x

end Tower

end UniqueExtension

end SemistableReduction
