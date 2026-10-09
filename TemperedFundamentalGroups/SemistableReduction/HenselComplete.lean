/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Hensel's lemma for complete non-archimedean fields

Blueprint §9.4, C1. Let `K` be a complete field with a non-archimedean absolute value (a normed
field with `IsUltrametricDist K` and `CompleteSpace K`). Its ring of integers
`𝒪 = {‖x‖ ≤ 1}` (the valuation subring of `NormedField.valuation`) is a Henselian local ring
(`henselianLocalRing`); more generally, a simple root modulo the maximal ideal of any (not
necessarily monic) integral polynomial lifts (`exists_root_of_isUnit`).

Mathlib's `henselian_of_isAdicComplete` does not apply: for a dense value group the maximal
ideal is idempotent and the `𝔪`-adic topology is discrete. The proof is Newton's iteration
`x ↦ x - f(x) / f'(x)` (`newtonStep`): if `f'(x)` is a unit and `‖f(x)‖ < 1`, then
`‖f(x')‖ ≤ ‖f(x)‖ ^ 2`, `‖x' - x‖ = ‖f(x)‖` and `f'(x')` is again a unit (`newtonStep_spec`); the
iterates converge quadratically to a root.
-/

open Polynomial IsLocalRing Filter Topology

namespace SemistableReduction

namespace HenselComplete

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

variable (K) in
/-- The ring of integers `{‖x‖ ≤ 1}` of a non-archimedean normed field. -/
noncomputable abbrev integers : ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

local notation "𝒪" => integers K

lemma mem_integers_iff (x : K) : x ∈ 𝒪 ↔ ‖x‖ ≤ 1 := by
  simp [integers, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]

lemma norm_le_one (a : 𝒪) : ‖(a : K)‖ ≤ 1 := (mem_integers_iff _).1 a.2

lemma isUnit_iff_norm_eq_one (a : 𝒪) : IsUnit a ↔ ‖(a : K)‖ = 1 := by
  rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one]
  simp [← NNReal.coe_inj]

lemma mem_maximalIdeal_iff_norm_lt_one (a : 𝒪) : a ∈ maximalIdeal 𝒪 ↔ ‖(a : K)‖ < 1 := by
  rw [Valuation.mem_maximalIdeal_iff]
  simp [← NNReal.coe_lt_coe]

open Classical in
/-- One Newton step `x ↦ x - f(x) / f'(x)` inside `𝒪` (the identity if `f'(x)` is not a
unit). -/
noncomputable def newtonStep (f : 𝒪[X]) (x : 𝒪) : 𝒪 :=
  if hu : IsUnit (f.derivative.eval x) then x - f.eval x * ↑hu.unit⁻¹ else x

/-- **The Newton step.** If `f'(x)` is a unit and `‖f(x)‖ < 1`, then `f'(x')` is a unit,
`‖f(x')‖ ≤ ‖f(x)‖ ^ 2` and `‖x' - x‖ ≤ ‖f(x)‖` for `x' = newtonStep f x`. -/
lemma newtonStep_spec (f : 𝒪[X]) {x : 𝒪} (hu : IsUnit (f.derivative.eval x))
    (hlt : ‖((f.eval x : 𝒪) : K)‖ < 1) :
    IsUnit (f.derivative.eval (newtonStep f x)) ∧
      ‖((f.eval (newtonStep f x) : 𝒪) : K)‖ ≤ ‖((f.eval x : 𝒪) : K)‖ ^ 2 ∧
      ‖((newtonStep f x : 𝒪) : K) - x‖ ≤ ‖((f.eval x : 𝒪) : K)‖ := by
  set h : 𝒪 := -(f.eval x * ↑hu.unit⁻¹) with hh
  have hstep : newtonStep f x = x + h := by
    rw [newtonStep, dif_pos hu, hh, sub_eq_add_neg]
  have hunorm : ‖((↑hu.unit⁻¹ : 𝒪) : K)‖ = 1 :=
    (isUnit_iff_norm_eq_one _).1 (Units.isUnit _)
  have hnorm : ‖(h : K)‖ = ‖((f.eval x : 𝒪) : K)‖ := by
    rw [hh]
    push_cast
    rw [norm_neg, norm_mul, hunorm, mul_one]
  have hfx : f.eval x + f.derivative.eval x * h = 0 := by
    rw [hh, mul_neg, ← mul_assoc, mul_comm (f.derivative.eval x), mul_assoc,
      show f.derivative.eval x * (↑hu.unit⁻¹ : 𝒪) = 1 from hu.mul_val_inv, mul_one,
      add_neg_cancel]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := f.derivative.evalSubFactor (x + h) x
    rw [add_sub_cancel_left] at hz
    have hd : f.derivative.eval (x + h) = f.derivative.eval x + z * h := by
      rw [← hz]; ring
    rw [hstep, isUnit_iff_norm_eq_one, hd]
    push_cast
    have h1 : ‖((f.derivative.eval x : 𝒪) : K)‖ = 1 := (isUnit_iff_norm_eq_one _).1 hu
    have h2 : ‖(z : K) * h‖ < 1 := by
      rw [norm_mul, hnorm]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one z)) hlt
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1,
      max_eq_left h2.le]
  · obtain ⟨k, hk⟩ := f.binomExpansion x h
    rw [hstep, hk, hfx, zero_add]
    push_cast
    rw [norm_mul, norm_pow, hnorm]
    exact mul_le_of_le_one_left (by positivity) (norm_le_one k)
  · rw [hstep]
    push_cast
    rw [add_sub_cancel_left, hnorm]

variable [CompleteSpace K]

/-- **Hensel's lemma** for an arbitrary (not necessarily monic) polynomial over the ring of
integers of a complete non-archimedean field: a simple root modulo the maximal ideal lifts. -/
theorem exists_root_of_isUnit (f : 𝒪[X]) {a₀ : 𝒪} (ha₀ : f.eval a₀ ∈ maximalIdeal 𝒪)
    (hu₀ : IsUnit (f.derivative.eval a₀)) : ∃ a : 𝒪, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal 𝒪 := by
  have hev (z : 𝒪) : aeval (z : K) f = ((f.eval z : 𝒪) : K) := by
    rw [show (z : K) = algebraMap 𝒪 K z from rfl, aeval_algebraMap_apply, coe_aeval_eq_eval]
    rfl
  set c := ‖((f.eval a₀ : 𝒪) : K)‖ with hc
  have hc1 : c < 1 := (mem_maximalIdeal_iff_norm_lt_one _).1 ha₀
  have hc0 : 0 ≤ c := norm_nonneg _
  set s : ℕ → 𝒪 := fun n ↦ (newtonStep f)^[n] a₀ with hs
  have hsucc (n : ℕ) : s (n + 1) = newtonStep f (s n) := by
    simp only [hs]
    rw [Function.iterate_succ_apply']
  -- the invariant: `f'(sₙ)` is a unit and `‖f(sₙ)‖ ≤ c ^ 2 ^ n`
  have hinv : ∀ n, IsUnit (f.derivative.eval (s n)) ∧ ‖((f.eval (s n) : 𝒪) : K)‖ ≤ c ^ 2 ^ n := by
    intro n
    induction n with
    | zero => exact ⟨hu₀, by simp [hs, hc]⟩
    | succ n ih =>
      have hlt : ‖((f.eval (s n) : 𝒪) : K)‖ < 1 :=
        lt_of_le_of_lt ih.2 (lt_of_le_of_lt (pow_le_of_le_one hc0 hc1.le
          (pow_ne_zero _ two_ne_zero)) hc1)
      obtain ⟨h1, h2, -⟩ := newtonStep_spec f ih.1 hlt
      rw [hsucc]
      refine ⟨h1, h2.trans ((pow_le_pow_left₀ (norm_nonneg _) ih.2 2).trans_eq ?_)⟩
      rw [← pow_mul, ← pow_succ]
  have hfs (n : ℕ) : ‖((f.eval (s n) : 𝒪) : K)‖ ≤ c ^ n :=
    (hinv n).2.trans (pow_le_pow_of_le_one hc0 hc1.le (Nat.lt_two_pow_self).le)
  have hlt (n : ℕ) : ‖((f.eval (s n) : 𝒪) : K)‖ < 1 :=
    lt_of_le_of_lt (hinv n).2 (lt_of_le_of_lt (pow_le_of_le_one hc0 hc1.le
      (pow_ne_zero _ two_ne_zero)) hc1)
  have hstep (n : ℕ) : ‖((s (n + 1) : 𝒪) : K) - s n‖ ≤ ‖((f.eval (s n) : 𝒪) : K)‖ := by
    rw [hsucc]
    exact (newtonStep_spec f (hinv n).1 (hlt n)).2.2
  have hinc (n : ℕ) : ‖((s (n + 1) : 𝒪) : K) - s n‖ ≤ c ^ n := (hstep n).trans (hfs n)
  have hfc (n : ℕ) : ‖((f.eval (s n) : 𝒪) : K)‖ ≤ c :=
    (hinv n).2.trans (pow_le_of_le_one hc0 hc1.le (pow_ne_zero _ two_ne_zero))
  -- the iterates form a Cauchy sequence in `K`
  set u : ℕ → K := fun n ↦ s n with hu
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric c 1 hc1 fun n ↦ ?_
    rw [dist_eq_norm, norm_sub_rev, one_mul]
    exact hinc n
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hy1 : ‖y‖ ≤ 1 :=
    le_of_tendsto' ((continuous_norm.tendsto y).comp hy) fun n ↦ norm_le_one (s n)
  -- distance to the starting point
  have hdist : ∀ n, ‖u n - a₀‖ ≤ c := by
    intro n
    induction n with
    | zero => simp [hu, hs, hc0]
    | succ n ih =>
      calc ‖u (n + 1) - a₀‖ = ‖(u (n + 1) - u n) + (u n - a₀)‖ := by ring_nf
        _ ≤ max ‖u (n + 1) - u n‖ ‖u n - a₀‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ c := max_le ((hstep n).trans (hfc n)) ih
  have hya : ‖y - a₀‖ ≤ c :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp (hy.sub_const _)) hdist
  -- the limit is a root
  have hroot : aeval y f = 0 := by
    have hlim : Tendsto (fun n ↦ aeval (u n) f) atTop (𝓝 (aeval y f)) :=
      ((Polynomial.continuous_aeval f).tendsto y).comp hy
    have hzero : Tendsto (fun n ↦ aeval (u n) f) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n ↦ ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1)
      rw [hu]
      dsimp only
      rw [hev]
      exact hfs n
    exact tendsto_nhds_unique hlim hzero
  refine ⟨⟨y, (mem_integers_iff y).2 hy1⟩, ?_, ?_⟩
  · apply Subtype.val_injective
    rw [← hev]
    exact hroot
  · rw [mem_maximalIdeal_iff_norm_lt_one]
    exact lt_of_le_of_lt hya hc1

/-- **Hensel's lemma**: the ring of integers of a complete non-archimedean field is a Henselian
local ring. -/
theorem henselianLocalRing : HenselianLocalRing 𝒪 :=
  ⟨fun f _ _ ha₀ hu₀ ↦ exists_root_of_isUnit f ha₀ hu₀⟩

end HenselComplete

end SemistableReduction
