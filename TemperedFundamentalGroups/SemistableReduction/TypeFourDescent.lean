/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Splitting

/-!
# The degree reduction at a type-4 point (interface)

Blueprint §9.12, leaf T4, core of `TypeFour.KummerStepFor`. Let `η` be a type-4 valuation of
`C(z)` (radius `r = inf_b η(z - b) > 0`, not attained), `A = ‖p‖^(p/(p-1)) = ‖γ‖^p`
(`γ^(p-1) = -p`), and `Q ∈ C[z]` with `η(Q) = 1` which is **not approximable by `p`-th powers to
`A`** at `η`: `A η(H)^p < η(Q - H^p)` for every rational function `H` (in the Kummer step this is
proved from `σ θ = ζ θ`, `Q` an approximant of `θ^p`). Then some `H` makes `Q - H^p`
**linear-dominant** on a disc `E` around `η`.

**Why it is true** (Temkin, *Stable modification of relative curves* §6.3, Prop. 6.3.2
(`immprop`), Lemma 6.3.6 (`dirtylem`), Prop. 6.3.3 (`modramprop`, type 4); equivalently Arzdorf's
best approximations K1, critical radius K4 and good centre K5, `CriticalRadius`, `GoodCentre`).
Write `μ = inf_H η(Q/H^p - 1) ≥ A`; it is not attained (the residue field and the values at a
type-4 point are those of `C`). Translated to Temkin's language, `Q/H^p - 1` represents the
critical coset `b + S_{a,s}`, `s = μ`, with `a = 0` if `μ > A` (purely inseparable type) and
`|a| = s^((p-1)/p)` if `μ = A` (Artin–Schreier type, Temkin's case (b)). Temkin's degree
reduction moves `b` inside the coset to a polynomial of degree `≤ 1` in `z` (`dirtylem`: the top
coefficient of a representative of degree `m > 1`, `p ∤ m`, satisfies `|b_m| r^m < s`, so it can be
removed by a recentred term of value `< s`; for `p ∣ m` subtract a `p`-th power). In both cases
`Q/H^p - 1 = l₀ + l₁ z + e` with `η(e) < |l₁| r` and `|l₁| r ≥ A`. On a disc `E = D(a, |c|)`
with `η(z - a) < |c|` and `|c|` slightly larger than `r` (deep enough that `e` has its `η`-value as
Gauss value on `E`), after rescaling `H` by a constant so that `Q(a) = H(a)^p`, the expansion of
`Q - H^p` in `Y = (z - a)/c` has its maximal coefficient `M = |l₁||c| > A` at `Y`. Since `η` is
deep inside any disc `D₀` around it, `E` can be chosen inside `D₀`. (If `Q` were a `p`-th power
up to an error `< A`, the hypothesis fails, so the statement is vacuous there.)
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

variable (C : Type*) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

/-- `A = ‖p‖^(p/(p-1))`, the Kummer bound. -/
noncomputable def kummerBound (p : ℕ) : ℝ := ‖(p : C)‖ ^ ((p : ℝ) / (p - 1))

/-- **Degree reduction at a type-4 point** (Temkin §6.3 / Arzdorf K1–K5; see the module doc). -/
def DegreeReductionFor (p : ℕ) : Prop :=
  ∀ η : Valuation (RatFunc C) ℝ≥0, Splitting.IsTypeFour η →
    (∃ r : ℝ≥0, 0 < r ∧ ∀ b : C, r ≤ η (RatFunc.X - algebraMap C (RatFunc C) b)) →
    ∀ Q : C[X], η (algebraMap C[X] (RatFunc C) Q) = 1 →
    (∀ H : RatFunc C, H ≠ 0 →
      kummerBound C p * (η H : ℝ) ^ p < η (algebraMap C[X] (RatFunc C) Q - H ^ p)) →
    ∀ (a₀ : C) (ρ₀ : ℝ≥0), η (RatFunc.X - algebraMap C (RatFunc C) a₀) < ρ₀ →
    ∃ (H : C[X]) (a c : C), c ≠ 0 ∧
      η (RatFunc.X - algebraMap C (RatFunc C) a) < ‖c‖₊ ∧ ‖c‖₊ ≤ ρ₀ ∧ ‖a - a₀‖₊ ≤ ρ₀ ∧
      ‖H.eval a‖ = 1 ∧ (∀ i, 1 ≤ i → ‖(H.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ < 1) ∧
      Q.eval a = H.eval a ^ p ∧
      ∃ M : ℝ, kummerBound C p < M ∧
        ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff 1‖ = M ∧
        ∀ i, ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ ≤ M

end TypeFour

end SemistableReduction
