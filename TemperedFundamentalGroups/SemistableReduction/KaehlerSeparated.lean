/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.GoingUp
import TemperedFundamentalGroups.SemistableReduction.KaehlerLocal

/-!
# Killing differentials by a local element, through Krull's intersection theorem (M2.5 (f), T1b)

`AlgStr.IsHom.kills_of_quot` transports killing constants from all levels `S/ϖⁿ` to the
algebraization only for **global** elements of `ℙ¹` (constants and `c X`), through the chart
module of `Ω`. A local element `y` of the first chart (in the Tate case `z = w/ℓ₀`, which separates
the cusp from the two other points of the fibre `h = 0`) is handled here when the differentials
are already killed by `ϖᵐ x` for a global `x` (in the Tate case `x = h`): then `ϖᵐ y Ω` is a
module over `S/(x)`, on which `1 − ϖ b` is invertible if `S/(x)` is integral over a ring in whose
Jacobson radical `ϖ` lies, and Krull's intersection theorem applies.

* **`KaehlerLocal.kills_of_iInf`**: if `ϖᵐ x` kills `Ω[S⁄R]`, `ϖᵐ y Ω ⊆ ϖⁿ Ω` for all `n`, and
  every `1 − ϖ b` is a unit modulo `x`, then `ϖᵐ y` kills `Ω[S⁄R]` (`S` Noetherian, `Ω` finite);
* **`KaehlerLocal.isUnit_one_sub_of_isIntegral`**: in an integral `O`-algebra, `1 − ϖ b` is a unit
  for `ϖ` in the Jacobson radical of `O`.
-/

universe u

namespace KaehlerLocal

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- **Killing by a local element via Krull** (see the module docstring). -/
theorem kills_of_iInf [IsNoetherianRing S] [Module.Finite S Ω[S⁄R]] {ϖ x y : S} {m : ℕ}
    (h1 : Kills R (ϖ ^ m * x))
    (h2 : ∀ n (ω : Ω[S⁄R]),
      (ϖ ^ m * y) • ω ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule S Ω[S⁄R]))
    (hunit : ∀ b : S, ∃ u s, (1 - ϖ * b) * u = 1 + x * s) :
    Kills R (ϖ ^ m * y) := by
  intro ω
  set X0 := (ϖ ^ m * y) • ω
  have hx : X0 ∈ (⨅ i : ℕ, (Ideal.span {ϖ}) ^ i • ⊤ : Submodule S Ω[S⁄R]) :=
    Submodule.mem_iInf _ |>.2 fun i ↦ h2 i ω
  obtain ⟨⟨r, hr⟩, hr'⟩ := ((Ideal.span {ϖ}).mem_iInf_smul_pow_eq_bot_iff X0).1 hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  obtain ⟨u, s, hus⟩ := hunit b
  have hb : (ϖ * b) • X0 = X0 := by rw [mul_comm]; exact hr'
  have hxx : x • X0 = 0 := by
    change x • ((ϖ ^ m * y) • ω) = 0
    rw [smul_smul, show x * (ϖ ^ m * y) = y * (ϖ ^ m * x) by ring, ← smul_smul, h1 ω, smul_zero]
  have h0 : (1 - ϖ * b) • X0 = 0 := by rw [sub_smul, one_smul, hb, sub_self]
  calc X0 = (u * (1 - ϖ * b) - x * s) • X0 := by
        rw [mul_comm u, hus, add_sub_cancel_right, one_smul]
    _ = 0 := by
        rw [sub_smul, mul_smul, h0, smul_zero, mul_comm x s, mul_smul, hxx, smul_zero, sub_zero]

/-- **`1 − ϖ b` is a unit in an integral extension** of a ring with `ϖ` in its Jacobson radical
(every maximal ideal of `S` lies over a maximal ideal of `O`). -/
theorem isUnit_one_sub_of_isIntegral {O S : Type*} [CommRing O] [CommRing S] [Algebra O S]
    [Algebra.IsIntegral O S] {ϖ : O} (hϖ : ϖ ∈ (⊥ : Ideal O).jacobson) (b : S) :
    IsUnit (1 - algebraMap O S ϖ * b) := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top h)
  have hc := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) M
  have hϖM : ϖ ∈ M.comap (algebraMap O S) := Ideal.mem_sInf.1 hϖ ⟨bot_le, hc⟩
  have h1 : (1 : S) ∈ M := by
    have := M.add_mem (hle (Ideal.mem_span_singleton_self _)) (M.mul_mem_right b hϖM)
    rwa [sub_add_cancel] at this
  exact hM.ne_top ((Ideal.eq_top_iff_one M).2 h1)

end KaehlerLocal
