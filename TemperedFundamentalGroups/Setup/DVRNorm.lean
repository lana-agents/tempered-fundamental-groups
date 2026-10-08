/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The norm of a complete discrete valuation field

Let `K` be a field and `O` a valuation subring of `K` which is a complete discrete valuation ring.

* `DVRNorm.normedField O : NontriviallyNormedField K`: the norm `‖x‖ = 2 ^ (- v (x))` of the
  normalized discrete valuation `v` of `O`; it is ultrametric (`isUltrametricDist`), complete
  (`completeSpace`, from `IsAdicComplete`), `‖x‖ ≤ 1 ↔ x ∈ O` (`norm_le_one_iff`) and
  `‖x‖ < 1 ↔ x ∈ 𝔪_O` (`norm_lt_one_iff`).
* `DVRNorm.normedFieldAlgCl O : NontriviallyNormedField (AlgebraicClosure K)`: the spectral norm,
  with `NormedAlgebra K (AlgebraicClosure K)` (`normedAlgebraAlgCl`), ultrametric, extending the
  norm of `K` (`norm_algebraMap`), invariant under `K`-automorphisms (`norm_algEquiv_apply`),
  with unit ball the integral closure of `O` (`norm_le_one_iff_isIntegral`).

These are definitions, not global instances; consumers use `letI`.
-/

open IsLocalRing Polynomial
open scoped WithZero

namespace TemperedFundamentalGroups.DVRNorm

variable {K : Type*} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]

/-- The normalized discrete valuation of `O`, with values in `ℤᵐ⁰`. -/
noncomputable def valuation : Valuation K ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal O).valuation K

/-- The valued field structure of `K` given by `valuation O`. -/
@[implicit_reducible]
noncomputable def valued : Valued K ℤᵐ⁰ := Valued.mk' (valuation O)

/-- The valuation of `O` has rank one (with base `2`). -/
@[implicit_reducible]
noncomputable def rankOne : (@Valued.v K _ ℤᵐ⁰ _ (valued O)).RankOne :=
  haveI : (valuation O).IsRankOneDiscrete := IsDiscreteValuationRing.isRankOneDiscrete O K
  Valuation.IsRankOneDiscrete.rankOne (valuation O) (e := 2) one_lt_two

/-- The norm of `K` determined by `O`. -/
@[implicit_reducible]
noncomputable def normedField : NontriviallyNormedField K :=
  @Valued.toNontriviallyNormedField K _ ℤᵐ⁰ _ (valued O) (rankOne O)

lemma mem_iff_valuation_le_one (x : K) : x ∈ O ↔ valuation O x ≤ 1 := by
  have h := congrArg (x ∈ ·)
    (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := O) (K := K))
  simp only [Subring.mem_map, Subring.mem_top, true_and, eq_iff_iff] at h
  rw [← Valuation.mem_valuationSubring_iff]
  refine ⟨fun hx ↦ h.1 ⟨⟨x, hx⟩, rfl⟩, fun hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := h.2 hx
  exact y.2

theorem isUltrametricDist : letI := normedField O; IsUltrametricDist K :=
  @Valued.instIsUltrametricDist K _ ℤᵐ⁰ _ (valued O) (rankOne O)

theorem norm_le_one_iff (x : K) : letI := normedField O; ‖x‖ ≤ 1 ↔ x ∈ O := by
  letI := valued O
  letI := rankOne O
  rw [mem_iff_valuation_le_one]
  exact Valued.toNormedField.norm_le_one_iff


theorem isUnit_iff_norm_eq_one (a : O) : letI := normedField O; IsUnit a ↔ ‖(a : K)‖ = 1 := by
  letI := normedField O
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · obtain ⟨u, rfl⟩ := ha
    have h1 : ‖((u : O) : K)‖ ≤ 1 := (norm_le_one_iff O _).2 (u : O).2
    have h2 : ‖((u⁻¹ : Oˣ) : K)‖ ≤ 1 := (norm_le_one_iff O _).2 (u⁻¹ : Oˣ).1.2
    have h3 : ‖((u : O) : K)‖ * ‖((u⁻¹ : Oˣ) : K)‖ = 1 := by
      rw [← norm_mul, ← MulMemClass.coe_mul, Units.mul_inv]
      simp
    nlinarith [norm_nonneg ((u : O) : K), norm_nonneg ((u⁻¹ : Oˣ) : K)]
  · have ha0 : (a : K) ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      exact zero_ne_one ha
    have hinv : (a : K)⁻¹ ∈ O := (norm_le_one_iff O _).1 (by rw [norm_inv, ha, inv_one])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) (Subtype.ext (mul_inv_cancel₀ ha0))

theorem norm_lt_one_iff (x : K) :
    letI := normedField O; ‖x‖ < 1 ↔ ∃ h : x ∈ O, (⟨x, h⟩ : O) ∈ maximalIdeal O := by
  letI := normedField O
  refine ⟨fun hx ↦ ⟨(norm_le_one_iff O x).1 hx.le, ?_⟩, fun ⟨h, hm⟩ ↦ ?_⟩
  · rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm_eq_one]
    exact hx.ne
  · rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm_eq_one] at hm
    exact lt_of_le_of_ne ((norm_le_one_iff O x).2 h) hm

section Uniformizer

variable {O} {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

lemma norm_uniformizer_pos : letI := normedField O; 0 < ‖(ϖ : K)‖ := by
  letI := normedField O
  refine norm_pos_iff.2 fun h ↦ hϖ.ne_zero (Subtype.ext h)

lemma norm_uniformizer_lt_one : letI := normedField O; ‖(ϖ : K)‖ < 1 :=
  (norm_lt_one_iff O _).2 ⟨ϖ.2, (mem_maximalIdeal _).2 hϖ.not_isUnit⟩

lemma mem_maximalIdeal_pow_iff (a : O) (n : ℕ) :
    letI := normedField O; a ∈ maximalIdeal O ^ n ↔ ‖(a : K)‖ ≤ ‖(ϖ : K)‖ ^ n := by
  letI := normedField O
  have hϖ0 : (ϖ : K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hpos : 0 < ‖(ϖ : K)‖ ^ n := pow_pos (norm_uniformizer_pos hϖ) n
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : ‖(c : K)‖ ≤ 1 := (norm_le_one_iff O _).2 c.2
    calc ‖((ϖ ^ n * c : O) : K)‖ = ‖(ϖ : K)‖ ^ n * ‖(c : K)‖ := by
          rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
      _ ≤ ‖(ϖ : K)‖ ^ n := mul_le_of_le_one_right hpos.le hc
  · intro h
    have hc : (a : K) / (ϖ : K) ^ n ∈ O := (norm_le_one_iff O _).1 (by
      rw [norm_div, norm_pow]
      exact (div_le_one hpos).2 h)
    refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    field_simp

end Uniformizer

theorem completeSpace [IsAdicComplete (maximalIdeal O) O] :
    letI := normedField O; CompleteSpace K := by
  letI := normedField O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 := norm_uniformizer_pos hϖ
  have h1 := norm_uniformizer_lt_one hϖ
  have hsmul (n : ℕ) : (maximalIdeal O ^ n • ⊤ : Submodule O O) = maximalIdeal O ^ n := by
    rw [smul_eq_mul, Ideal.mul_top]
  refine Metric.complete_of_convergent_controlled_sequences (fun N ↦ ‖(ϖ : K)‖ ^ N)
    (fun N ↦ pow_pos h0 N) fun u hu ↦ ?_
  have hO (n : ℕ) : u n - u 0 ∈ O := (norm_le_one_iff O _).1 (by
    have := hu 0 n 0 (Nat.zero_le n) le_rfl
    rw [dist_eq_norm, pow_zero] at this
    exact this.le)
  let f : ℕ → O := fun n ↦ ⟨u n - u 0, hO n⟩
  have hf {m n : ℕ} (hmn : m ≤ n) : f m ≡ f n [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    rw [SModEq.sub_mem, hsmul, mem_maximalIdeal_pow_iff hϖ]
    have := hu m m n le_rfl hmn
    rw [dist_eq_norm] at this
    calc ‖((f m - f n : O) : K)‖ = ‖u m - u n‖ := by
          congr 1
          simp only [f, AddSubgroupClass.coe_sub]
          ring
      _ ≤ _ := this.le
  obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hf
  refine ⟨u 0 + L, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε h1
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, hsmul, mem_maximalIdeal_pow_iff hϖ] at h
  rw [dist_eq_norm]
  calc ‖u n - (u 0 + L)‖ = ‖((f n - L : O) : K)‖ := by
        congr 1
        simp only [f, AddSubgroupClass.coe_sub]
        ring
    _ ≤ ‖(ϖ : K)‖ ^ n := h
    _ ≤ ‖(ϖ : K)‖ ^ N := pow_le_pow_of_le_one h0.le h1.le hn
    _ < ε := hN


section AlgebraicClosure

variable [IsAdicComplete (maximalIdeal O) O]

local notation "C" => AlgebraicClosure K

/-- The spectral norm on the algebraic closure of `K` (extending `normedField O`). -/
@[implicit_reducible]
noncomputable def normedFieldAlgCl : NontriviallyNormedField C :=
  letI := normedField O
  haveI := isUltrametricDist O
  haveI := completeSpace O
  spectralNorm.nontriviallyNormedField K C

/-- `K` acts isometrically on its algebraic closure with the spectral norm. -/
@[implicit_reducible]
noncomputable def normedAlgebraAlgCl :
    letI := normedField O; letI := normedFieldAlgCl O; NormedAlgebra K C :=
  letI := normedField O
  haveI := isUltrametricDist O
  haveI := completeSpace O
  spectralNorm.normedAlgebra K C

theorem norm_algCl_def (x : C) :
    letI := normedField O; letI := normedFieldAlgCl O; ‖x‖ = spectralNorm K C x :=
  rfl

theorem isUltrametricDist_algCl : letI := normedFieldAlgCl O; IsUltrametricDist C := by
  letI := normedField O
  haveI := isUltrametricDist O
  letI := normedFieldAlgCl O
  letI := normedAlgebraAlgCl O
  exact IsUltrametricDist.of_normedAlgebra K

theorem norm_algebraMap (x : K) :
    letI := normedField O; letI := normedFieldAlgCl O; ‖algebraMap K C x‖ = ‖x‖ := by
  letI := normedField O
  haveI := isUltrametricDist O
  exact spectralNorm_extends x

/-- **Galois isometry.** `K`-automorphisms of the algebraic closure preserve the spectral
norm. -/
theorem norm_algEquiv_apply (σ : C ≃ₐ[K] C) (x : C) :
    letI := normedFieldAlgCl O; ‖σ x‖ = ‖x‖ := by
  letI := normedField O
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem norm_natCast_lt_one {p : ℕ} (hp : (p : O) ∈ maximalIdeal O) :
    letI := normedFieldAlgCl O; ‖(p : C)‖ < 1 := by
  letI := normedField O
  letI := normedFieldAlgCl O
  rw [← map_natCast (algebraMap K C), norm_algebraMap]
  refine (norm_lt_one_iff O _).2 ⟨(p : O).2, ?_⟩
  convert hp
  simp

/-- The unit ball of the spectral norm is the integral closure of `O`. -/
theorem norm_le_one_iff_isIntegral (x : C) :
    letI := normedFieldAlgCl O; ‖x‖ ≤ 1 ↔ IsIntegral O x := by
  letI := normedField O
  rw [norm_algCl_def, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
  simp only [norm_le_one_iff]
  constructor
  · intro h
    have hl : minpoly K x ∈ lifts (algebraMap O K) := by
      rw [lifts_iff_coeff_lifts]
      exact fun n ↦ ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ :=
      lifts_and_degree_eq_and_monic hl (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap K, hq, minpoly.aeval]
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h, coeff_map]
    exact ((minpoly O x).coeff n).2

end AlgebraicClosure

end TemperedFundamentalGroups.DVRNorm
