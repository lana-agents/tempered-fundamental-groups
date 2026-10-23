/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KaehlerChartModule
import TemperedFundamentalGroups.SemistableReduction.ChartModuleVanish
import TemperedFundamentalGroups.SemistableReduction.KaehlerKill
import TemperedFundamentalGroups.SemistableReduction.KaehlerLocal

/-!
# Differentials killed modulo all `Iⁿ` are killed (Blueprint §12.8, M2.5 (f))

For the chart module of relative differentials `Ω_{𝒴/𝒳}` (`KaehlerChart.chartModule`) of a
coherent `𝒴` over `ℙ¹_A`, `A` Noetherian and `I`-adically complete:

* **`KaehlerChart.kills_of_quot`**: if a constant `c ∈ A` kills the differentials of the
  reductions `S_i ⧸ Iⁿ S_i` over `R_i` for all `n` (both charts), it kills `Ω[S_i⁄R_i]`;
* **`KaehlerChart.kills_x_of_quot`**: the same with `c x` on the first chart (a covering
  ramified over `x = 0`) and `c` on the second.

Proof: `c Ω ⊆ Iⁿ Ω` by `KaehlerDifferential.smul_mem_smul_top_of_quot`, then
`ChartModule.smul_eq_zero_of_forall_mem` (`smul_x0_eq_zero_of_forall_mem`).
-/

universe u

open Polynomial

namespace KaehlerChart

variable (A : Type u) [CommRing A] {R0 R1 R01 S0 S1 S01 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R01] [CommRing S0] [CommRing S1] [CommRing S01]
  [Algebra A R0] [Algebra A R1] [Algebra A R01] [Algebra A S0] [Algebra A S1] [Algebra A S01]
  [Algebra R0 S0] [Algebra R1 S1] [Algebra R01 S01]
  [IsScalarTower A R0 S0] [IsScalarTower A R1 S1] [IsScalarTower A R01 S01]
  [Algebra R0 R01] [Algebra R1 R01] [Algebra S0 S01] [Algebra S1 S01]
  [Algebra R0 S01] [Algebra R1 S01]
  [IsScalarTower R0 R01 S01] [IsScalarTower R0 S0 S01] [IsScalarTower R1 R01 S01]
  [IsScalarTower R1 S1 S01] [IsScalarTower A S0 S01] [IsScalarTower A S1 S01]
  (x : R0) (y : R1) [IsLocalization.Away x R01] [IsLocalization.Away y R01]
  [IsLocalization.Away (algebraMap R0 S0 x) S01] [IsLocalization.Away (algebraMap R1 S1 y) S01]
  (I : Ideal A)

omit [Algebra A R01] [IsScalarTower A R01 S01] in
/-- `c Ω ⊆ Iⁿ Ω` as `A`-modules, from the reduction modulo `Iⁿ`. -/
lemma mem_smul_top_of_quot {R S : Type u} [CommRing R] [CommRing S] [Algebra A R] [Algebra R S]
    [Algebra A S] [IsScalarTower A R S] (n : ℕ) {s : S}
    (hs : KaehlerLocal.Kills R (Ideal.Quotient.mk ((I ^ n).map (algebraMap A S)) s))
    (ω : Ω[S⁄R]) : s • ω ∈ I ^ n • (⊤ : Submodule A Ω[S⁄R]) := by
  have hm := KaehlerDifferential.smul_mem_smul_top_of_quot (I ^ n) hs ω
  have := (Submodule.restrictScalars_mem A _ _).2 hm
  rwa [Ideal.smul_restrictScalars, Submodule.restrictScalars_top] at this

variable [IsNoetherianRing A] [IsAdicComplete I A]

/-- **Differentials killed modulo all `Iⁿ` are killed** (both charts). -/
theorem kills_of_quot (hxy : algebraMap R0 S01 x * algebraMap R1 S01 y = 1)
    [Module.Finite A[X] (Module.AEval' (chartModule (R0 := R0) (R1 := R1) (R01 := R01) (S0 := S0)
      (S1 := S1) (S01 := S01) A x y hxy).x0)]
    [Module.Finite A[X] (Module.AEval' (chartModule (R0 := R0) (R1 := R1) (R01 := R01) (S0 := S0)
      (S1 := S1) (S01 := S01) A x y hxy).x1)] {c : A}
    (h0 : ∀ n, KaehlerLocal.Kills R0
      (Ideal.Quotient.mk ((I ^ n).map (algebraMap A S0)) (algebraMap A S0 c)))
    (h1 : ∀ n, KaehlerLocal.Kills R1
      (Ideal.Quotient.mk ((I ^ n).map (algebraMap A S1)) (algebraMap A S1 c))) :
    KaehlerLocal.Kills R0 (algebraMap A S0 c) ∧ KaehlerLocal.Kills R1 (algebraMap A S1 c) := by
  have := ProjectiveLine.ChartModule.smul_eq_zero_of_forall_mem I
    (N := chartModule (R0 := R0) (R1 := R1) (R01 := R01) (S0 := S0) (S1 := S1) (S01 := S01)
      A x y hxy) (c := c)
    (fun n m ↦ by
      have := mem_smul_top_of_quot A I n (h0 n) m
      rwa [algebraMap_smul] at this)
    (fun n m ↦ by
      have := mem_smul_top_of_quot A I n (h1 n) m
      rwa [algebraMap_smul] at this)
  exact ⟨fun ω ↦ by rw [algebraMap_smul]; exact this.1 ω,
    fun ω ↦ by rw [algebraMap_smul]; exact this.2 ω⟩

/-- **Differentials killed modulo all `Iⁿ`, ramified over `x = 0`**: `c x` on the first chart
and `c` on the second. -/
theorem kills_x_of_quot (hxy : algebraMap R0 S01 x * algebraMap R1 S01 y = 1)
    [Module.Finite A[X] (Module.AEval' (chartModule (R0 := R0) (R1 := R1) (R01 := R01) (S0 := S0)
      (S1 := S1) (S01 := S01) A x y hxy).x0)]
    [Module.Finite A[X] (Module.AEval' (chartModule (R0 := R0) (R1 := R1) (R01 := R01) (S0 := S0)
      (S1 := S1) (S01 := S01) A x y hxy).x1)] {c : A}
    (h0 : ∀ n, KaehlerLocal.Kills R0 (Ideal.Quotient.mk ((I ^ n).map (algebraMap A S0))
      (algebraMap A S0 c * algebraMap R0 S0 x)))
    (h1 : ∀ n, KaehlerLocal.Kills R1
      (Ideal.Quotient.mk ((I ^ n).map (algebraMap A S1)) (algebraMap A S1 c))) :
    KaehlerLocal.Kills R0 (algebraMap A S0 c * algebraMap R0 S0 x) ∧
      KaehlerLocal.Kills R1 (algebraMap A S1 c) := by
  have := ProjectiveLine.ChartModule.smul_x0_eq_zero_of_forall_mem I
    (N := chartModule (R0 := R0) (R1 := R1) (R01 := R01) (S0 := S0) (S1 := S1) (S01 := S01)
      A x y hxy) (c := c)
    (fun n m ↦ by
      have := mem_smul_top_of_quot A I n (h0 n) m
      rw [mul_smul, algebraMap_smul] at this
      exact this)
    (fun n m ↦ by
      have := mem_smul_top_of_quot A I n (h1 n) m
      rwa [algebraMap_smul] at this)
  refine ⟨fun ω ↦ ?_, fun ω ↦ by rw [algebraMap_smul]; exact this.2 ω⟩
  rw [mul_smul, algebraMap_smul]
  exact this.1 ω

end KaehlerChart
