/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KaehlerTower
import TemperedFundamentalGroups.SemistableReduction.KaehlerSeparated

/-!
# From the levels to the algebraization: killing by a local element (M2.5 (f), T1b)

`TwoChartTower.kills_shift` transports killing constants `c Xʲ` from the levels to the
algebraization. For an element `d` of the first chart `D.R0` of the base model which is not a
global section of `ℙ¹`:

* **`TwoChartTower.kills_quot0_of_base`**: if `c · β_n(d)` kills `Ω[(E n).R0⁄D.R0]` for all `n`,
  then `c d` kills the differentials of every reduction `B₀ ⧸ Iⁿ⁺¹ B₀` over `D.R0`;
* **`TwoChartTower.kills_local0`**: for `I = (ϖ)` and `c = ϖᵐ`, if moreover `ϖᵐ X` kills
  `Ω[B₀⁄D.R0]` and `1 − ϖ b` is a unit modulo `X` in `B₀`, then `ϖᵐ d` kills `Ω[B₀⁄D.R0]`
  (`KaehlerLocal.kills_of_iInf`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TwoChartTower

open ProjectiveLine ProjectiveLine.ChartModule

variable {A : Type u} [CommRing A] {E : ℕ → TwoChartRings A}
  {e : ∀ n, TwoChartMap (E (n + 1)) (E n)} {I : Ideal A} [IsNoetherianRing A] [IsAdicComplete I A]
  {he0 : ∀ n, Function.Surjective (e n).f0} {he1 : ∀ n, Function.Surjective (e n).f1}
  {hker0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0)}
  {hker1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1)}
  {hkill0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥}
  {hkill1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥}
  {hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0)}
  {hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)}
  {N : ChartModule A} [Module.Finite A[X] (Module.AEval' N.x0)]
  [Module.Finite A[X] (Module.AEval' N.x1)] {B : AlgStr N}
  {α : ∀ n, Hom N ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).M n)}

omit [IsNoetherianRing A] [IsAdicComplete I A] [Module.Finite A[X] (Module.AEval' N.x0)]
  [Module.Finite A[X] (Module.AEval' N.x1)] in
/-- **Killing by a base element on the reductions** (see the module docstring). -/
theorem kills_quot0_of_base (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n))
    {D : TwoChartRings A} {φ : Hom D.chartModule N} (h : D.algStr.IsHom B φ)
    {β : ∀ n, TwoChartMap D (E n)} (hβ : ∀ n, (α (n + 1)).comp φ = (β n).toHom)
    {c : A} {d : D.R0}
    (h0 : ∀ n, letI := (β n).f0.toRingHom.toAlgebra
      KaehlerLocal.Kills D.R0 (algebraMap A (E n).R0 c * (β n).f0 d)) (n : ℕ) :
    letI := B.algR0 h
    KaehlerLocal.Kills D.R0 (Ideal.Quotient.mk ((I ^ (n + 1)).map B.const0)
      (B.const0 c * algebraMap D.R0 B.Ring0 d)) := by
  letI := B.algR0 h
  letI := (β n).f0.toRingHom.toAlgebra
  let eq : (B.Ring0 ⧸ (I ^ (n + 1)).map B.const0) ≃ₐ[D.R0] (E n).R0 :=
    AlgEquiv.ofRingEquiv (f := quotEquivShift0 hα hB n) fun d ↦ by
      change (α (n + 1)).f0 (φ.f0 d) = (β n).f0 d
      exact Hom.f0_eq_of_eq (hβ n) d
  refine KaehlerLocal.kills_of_equiv eq ?_
  have hd : eq (Ideal.Quotient.mk _ (algebraMap D.R0 B.Ring0 d)) = (β n).f0 d :=
    eq.commutes d
  change KaehlerLocal.Kills D.R0 (quotEquivShift0 hα hB n (Ideal.Quotient.mk _ _))
  rw [map_mul, map_mul, quotEquivShift0_const0]
  change KaehlerLocal.Kills D.R0 (_ * eq (Ideal.Quotient.mk _ (algebraMap D.R0 B.Ring0 d)))
  rw [hd]
  exact h0 n

omit [IsNoetherianRing A] [IsAdicComplete I A] [Module.Finite A[X] (Module.AEval' N.x0)]
  [Module.Finite A[X] (Module.AEval' N.x1)] in
/-- **Killing by a local element on the algebraization** (see the module docstring). -/
theorem kills_local0 {ϖ : A} (hI : I = Ideal.span {ϖ})
    (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n))
    {D : TwoChartRings A} {φ : Hom D.chartModule N} (h : D.algStr.IsHom B φ)
    {β : ∀ n, TwoChartMap D (E n)} (hβ : ∀ n, (α (n + 1)).comp φ = (β n).toHom)
    [IsNoetherianRing B.Ring0]
    [hΩ : letI := B.algR0 h; Module.Finite B.Ring0 Ω[B.Ring0⁄D.R0]]
    {m : ℕ} {d : D.R0}
    (hX : letI := B.algR0 h; KaehlerLocal.Kills D.R0 (B.const0 (ϖ ^ m) * B.X0))
    (h0 : ∀ n, letI := (β n).f0.toRingHom.toAlgebra
      KaehlerLocal.Kills D.R0 (algebraMap A (E n).R0 (ϖ ^ m) * (β n).f0 d))
    (hunit : ∀ b : B.Ring0, ∃ u s, (1 - B.const0 ϖ * b) * u = 1 + B.X0 * s) :
    letI := B.algR0 h
    KaehlerLocal.Kills D.R0 (B.const0 (ϖ ^ m) * algebraMap D.R0 B.Ring0 d) := by
  letI := B.algR0 h
  letI : Algebra A B.Ring0 := B.const0.toAlgebra
  haveI : IsScalarTower A D.R0 B.Ring0 := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change B.const0 a = h.ringHom0 ((TwoChartRings.ring0Equiv D).symm (algebraMap A D.R0 a))
    rw [← TwoChartRings.ring0Equiv_const0, RingEquiv.symm_apply_apply, h.ringHom0_const0]
  rw [map_pow] at hX ⊢
  refine KaehlerLocal.kills_of_iInf hX (fun n ω ↦ ?_) hunit
  have hspan : (Ideal.span {B.const0 ϖ}) ^ n = (I ^ n).map (algebraMap A B.Ring0) := by
    rw [hI, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl
  rw [hspan]
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top, Ideal.map_top, Submodule.top_smul]
    exact Submodule.mem_top
  have hq := kills_quot0_of_base hα hB h hβ (c := ϖ ^ m) h0 n
  rw [map_pow] at hq
  exact KaehlerDifferential.smul_mem_smul_top_of_quot (I ^ (n + 1)) hq ω

end TwoChartTower

end SemistableReduction
