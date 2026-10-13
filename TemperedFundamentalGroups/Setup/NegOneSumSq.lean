/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# `−1` is a sum of squares in a complete field of residue characteristic `p > 0`

Let `O ⊆ K` be a valuation subring of a field of characteristic `0` which is complete for its
maximal ideal `𝔪` (hence Henselian), with `p ∈ 𝔪` for a prime `p`. Then `−1` is a sum of squares
in `K` (`isSumSq_neg_one`), i.e. `K` admits no ordering (it is not formally real):

* if `2 ∈ 𝔪`: `y² + y + 2` has the simple root `0` modulo `𝔪`; for a root `y`,
  `s = 2y + 1` satisfies `s² = −7`, and `−1 = ((2² + 1 + 1 + 1))/s²`;
* if `2 ∉ 𝔪` (so `p` is odd): `a² + b² ≡ −1 (mod p)` has a solution in `ℕ`
  (`Nat.sq_add_sq_modEq`), which lifts by Hensel's lemma (`X² + (b² + 1)` at `a`, or `X² + 1` at
  `b` if `a ∈ 𝔪`).
-/

open Polynomial IsLocalRing

namespace TemperedFundamentalGroups

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- Hensel's lemma for `O`, in the form used here. -/
lemma exists_root_of_henselian [IsAdicComplete (maximalIdeal O) O] (f : O[X]) (hf : f.Monic)
    (a₀ : O) (h₁ : f.eval a₀ ∈ maximalIdeal O) (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : O, f.IsRoot a :=
  let ⟨a, ha, _⟩ := HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)
  ⟨a, ha⟩

/-- **`−1` is a sum of squares** in a complete valued field of characteristic `0` with residue
characteristic `p > 0`. -/
theorem isSumSq_neg_one [CharZero K] [IsAdicComplete (maximalIdeal O) O]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ maximalIdeal O) : IsSumSq (-1 : K) := by
  by_cases h2 : (2 : O) ∈ maximalIdeal O
  · -- residue characteristic `2`: `−7` is a square
    obtain ⟨y, hy⟩ := exists_root_of_henselian O (X ^ 2 + X + C 2) (by monicity!) 0
      (by simpa using h2) (by simp)
    have hy' : (y : K) ^ 2 + y + 2 = 0 := by
      have h0 : y ^ 2 + y + 2 = 0 := by simpa using hy.eq_zero
      have := congrArg (algebraMap O K) h0
      rwa [map_add, map_add, map_pow, map_ofNat, map_zero] at this
    set s : K := 2 * y + 1 with hs
    have hs2 : s ^ 2 = -7 := by rw [hs]; linear_combination 4 * hy'
    have hs0 : s ≠ 0 := by
      rintro h
      rw [h] at hs2
      have : (7 : K) = 0 := by linear_combination hs2
      exact (by norm_num : (7 : K) ≠ 0) this
    have h : (-1 : K) = (2 / s) * (2 / s) + ((1 / s) * (1 / s) + ((1 / s) * (1 / s) +
        ((1 / s) * (1 / s) + 0))) := by
      field_simp
      linear_combination -hs2
    rw [h]
    exact .sq_add _ (.sq_add _ (.sq_add _ (.sq_add _ .zero)))
  · -- odd residue characteristic
    have hu2 : IsUnit (2 : O) := by
      by_contra h
      exact h2 ((mem_maximalIdeal _).2 h)
    obtain ⟨p, hpp, hpm⟩ := hp
    haveI := Fact.mk hpp
    obtain ⟨a, b, -, -, hab⟩ := Nat.sq_add_sq_modEq p (p - 1)
    have hdvd : p ∣ a ^ 2 + b ^ 2 + 1 := by
      have h1 : a ^ 2 + b ^ 2 + 1 ≡ p - 1 + 1 [MOD p] := hab.add_right 1
      rw [Nat.sub_add_cancel hpp.one_lt.le] at h1
      exact (Nat.modEq_zero_iff_dvd).1 (h1.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
    have hm : ((a : O) ^ 2 + (b : O) ^ 2 + 1) ∈ maximalIdeal O := by
      obtain ⟨k, hk⟩ := hdvd
      have : ((a ^ 2 + b ^ 2 + 1 : ℕ) : O) = (p : O) * k := by rw [hk]; push_cast; ring
      push_cast at this
      rw [this]
      exact Ideal.mul_mem_right _ _ hpm
    by_cases ha : (a : O) ∈ maximalIdeal O
    · -- `b² ≡ −1`: lift `b` to a root of `X² + 1`
      have hb1 : (b : O) ^ 2 + 1 ∈ maximalIdeal O := by
        have : (b : O) ^ 2 + 1 = ((a : O) ^ 2 + (b : O) ^ 2 + 1) - a * a := by ring
        rw [this]
        exact Ideal.sub_mem _ hm (Ideal.mul_mem_left _ _ ha)
      have hb : IsUnit (b : O) := by
        by_contra h
        have h' := Ideal.sub_mem _ hb1 (Ideal.mul_mem_left _ (b : O) ((mem_maximalIdeal _).2 h))
        rw [show (b : O) ^ 2 + 1 - b * b = 1 by ring] at h'
        exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h')
      have hd : (X ^ 2 + 1 : O[X]).derivative.eval (b : O) = 2 * b := by
        simp only [derivative_add, derivative_X_pow, derivative_one, add_zero, eval_mul, eval_C,
          eval_pow, eval_X]
        norm_num
      obtain ⟨α, hα⟩ := exists_root_of_henselian O (X ^ 2 + 1) (by monicity!) b
        (by simpa using hb1) (by rw [hd]; exact hu2.mul hb)
      have hα' : (α : K) ^ 2 + 1 = 0 := by
        have h0 : α ^ 2 + 1 = 0 := by simpa using hα.eq_zero
        have := congrArg (algebraMap O K) h0
        rwa [map_add, map_pow, map_one, map_zero] at this
      have h : (-1 : K) = α * α + 0 := by linear_combination -hα'
      rw [h]
      exact .sq_add _ .zero
    · -- lift `a` to a root of `X² + (b² + 1)`
      have hau : IsUnit (a : O) := by
        by_contra h
        exact ha ((mem_maximalIdeal _).2 h)
      have hm' : (a : O) ^ 2 + ((b : O) ^ 2 + 1) ∈ maximalIdeal O := by rwa [← add_assoc]
      generalize hbb : (b : O) ^ 2 + 1 = bb at hm'
      have hd : (X ^ 2 + C bb : O[X]).derivative.eval (a : O) = 2 * a := by
        simp only [derivative_add, derivative_X_pow, derivative_C, add_zero, eval_mul, eval_C,
          eval_pow, eval_X]
        norm_num
      obtain ⟨α, hα⟩ := exists_root_of_henselian O (X ^ 2 + C bb) (by monicity!)
        a (by simpa using hm') (by rw [hd]; exact hu2.mul hau)
      have hα' : (α : K) ^ 2 + (b : K) ^ 2 + 1 = 0 := by
        have h0 : α ^ 2 + bb = 0 := by simpa using hα.eq_zero
        rw [← hbb] at h0
        have := congrArg (algebraMap O K) h0
        rw [map_add, map_add, map_pow, map_pow, map_one, map_zero, map_natCast] at this
        rw [← this, add_assoc]
        rfl
      have h : (-1 : K) = α * α + ((b : K) * b + 0) := by linear_combination -hα'
      rw [h]
      exact .sq_add _ (.sq_add _ .zero)

end TemperedFundamentalGroups
