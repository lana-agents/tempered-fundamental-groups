/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XLift

/-!
# Tools for x-lengths: representations of exponents, powers and inverses of residues

Blueprint §9.7 (XL5).

* `IsLogValue.pow_eq`, `isLogValue_iff`: `IsLogValue U ϖ f (N / D)` iff `U(f) ^ D = U(ϖ) ^ N`;
* `IsResidueTranscendental.pow`, `.inv`, `.of_inv`: residue transcendence of powers and inverses;
* `residueTranscendental_iff_repr`: the monomial `u ^ D / ϖ ^ N` of any representation
  `s = N / D` has transcendental residue iff the reduced one does.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- `IsLogValue` for a non-reduced representation. -/
theorem IsLogValue.pow_eq {U : ValuationSubring L} {ϖ f : L} {q : ℚ} (h : IsLogValue U ϖ f q)
    {N : ℤ} {D : ℕ} (hD : 0 < D) (hq : q = N / D) :
    U.valuation f ^ D = U.valuation ϖ ^ N := by
  unfold IsLogValue at h
  have hq' : q.num * (D : ℤ) = N * q.den := by
    have h1 : (q.num : ℚ) = q * q.den := q.mul_den_eq_num.symm
    have : (q.num : ℚ) * D = N * q.den := by
      rw [h1, hq]; field_simp
    exact_mod_cast this
  have key : (U.valuation f ^ D) ^ q.den = (U.valuation ϖ ^ N) ^ q.den := by
    rw [← pow_mul, mul_comm, pow_mul, h, ← zpow_natCast, ← zpow_mul, ← zpow_natCast,
      ← zpow_mul, hq', mul_comm]
  have hden := q.den_pos
  exact le_antisymm ((pow_le_pow_iff_left₀ zero_le zero_le hden.ne').mp key.le)
    ((pow_le_pow_iff_left₀ zero_le zero_le hden.ne').mp key.ge)

theorem isLogValue_iff {U : ValuationSubring L} {ϖ f : L} {N : ℤ} {D : ℕ} (hD : 0 < D) :
    IsLogValue U ϖ f ((N : ℚ) / D) ↔ U.valuation f ^ D = U.valuation ϖ ^ N :=
  ⟨fun h ↦ h.pow_eq hD rfl, IsLogValue.of_pow_eq hD⟩

variable {O : ValuationSubring K} {U : ValuationSubring L}

/-- Residue transcendence of powers. -/
theorem IsResidueTranscendental.pow (hU : U.comap (algebraMap K L) = O) {w : L}
    (h : IsResidueTranscendental O U w) {M : ℕ} (hM : 0 < M) :
    IsResidueTranscendental O U (w ^ M) := by
  have hw := h.1
  rw [isResidueTranscendental_iff hU hw] at h
  rw [isResidueTranscendental_iff hU (U.pow_mem hw M)]
  letI := residueAlgebra hU
  have : residue U ⟨w ^ M, U.pow_mem hw M⟩ = residue U ⟨w, hw⟩ ^ M := by
    rw [← map_pow]; rfl
  rw [this]
  intro halg
  exact h (halg.of_pow hM)

/-- Residue transcendence of inverses. -/
theorem IsResidueTranscendental.inv (hU : U.comap (algebraMap K L) = O) {w : L}
    (h : IsResidueTranscendental O U w) (hwi : w⁻¹ ∈ U) :
    IsResidueTranscendental O U w⁻¹ := by
  have hw := h.1
  rw [isResidueTranscendental_iff hU hw] at h
  rw [isResidueTranscendental_iff hU hwi]
  letI := residueAlgebra hU
  have hw0 : w ≠ 0 := fun h0 ↦ by
    apply h; rw [show (⟨w, hw⟩ : U) = 0 from Subtype.ext h0, map_zero]; exact isAlgebraic_zero
  have e : residue U ⟨w⁻¹, hwi⟩ = (residue U ⟨w, hw⟩)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← map_one (residue U)]
    congr 1; ext; simp [hw0]
  rw [e]
  intro halg
  exact h (by simpa using halg.inv)

/-- **Representations of exponents.** If `s = N / D` (`D > 0`) and `U(u ^ D / ϖ ^ N) = 1`,
the residue of `u ^ D / ϖ ^ N` is transcendental iff that of `u ^ den s / ϖ ^ num s` is. -/
theorem residueTranscendental_iff_repr (hU : U.comap (algebraMap K L) = O) {u ϖ : L}
    {s : ℚ} {N : ℤ} {D : ℕ} (hD : 0 < D) (hs : s = N / D)
    (hmem : u ^ s.den / ϖ ^ s.num ∈ U) :
    IsResidueTranscendental O U (u ^ D / ϖ ^ N) ↔
      IsResidueTranscendental O U (u ^ s.den / ϖ ^ s.num) := by
  -- `D = k den`, `N = k num`
  have hdvd : (s.den : ℤ) ∣ D := by
    have := Rat.den_dvd N D
    rw [Rat.divInt_eq_div] at this
    push_cast at this
    rw [← hs] at this
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by
    rcases lt_trichotomy k 0 with h | h | h
    · nlinarith [s.den_pos]
    · rw [h, mul_zero] at hk; omega
    · exact h
  have hN : N = k * s.num := by
    have h1 : (s.num : ℚ) * D = N * s.den := by
      have : (s.num : ℚ) = s * s.den := s.mul_den_eq_num.symm
      rw [this, hs]; field_simp
    have h2 : (s.num : ℤ) * D = N * s.den := by exact_mod_cast h1
    rw [show (D : ℤ) = s.den * k from hk] at h2
    have hden : (s.den : ℤ) ≠ 0 := by exact_mod_cast s.den_nz
    have := mul_right_cancel₀ hden (by linarith : N * (s.den : ℤ) = (k * s.num) * s.den)
    exact this
  lift k to ℕ using hk0.le
  have hD' : D = s.den * k := by exact_mod_cast hk
  have e : u ^ D / ϖ ^ N = (u ^ s.den / ϖ ^ s.num) ^ k := by
    rw [hD', hN, div_pow, ← pow_mul, mul_comm (k : ℤ), zpow_mul, zpow_natCast]
  rw [e]
  exact ⟨fun h ↦ h.of_pow hU hmem, fun h ↦ h.pow hU (by exact_mod_cast hk0)⟩

end SemistableReduction
