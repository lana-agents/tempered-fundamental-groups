/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialChart
import TemperedFundamentalGroups.SemistableReduction.MobiusLine
import TemperedFundamentalGroups.SemistableReduction.P1ThreeLine

/-!
# The special fibre of `V₁` in the coordinate `h'` of the Tate line (MR13 step 7, D1 (S5))

**`P1Three.vertexChartEquiv`**: for `θ a ≠ 0, 1`, the special fibre `R1/J` of the chart
`V₁ = ℙ¹ ∖ {0, 1, a}` is `k[h', 1/(h'(h' + 1))]`, through `tsEquiv1` (`R1/J ≃ R1 k ā`),
`lineEquiv` (`R1 k ā ≃ k[s, 1/((1 − s)(1 − ā s))]`, `s = 1/t`) and the Möbius re-charting
`MobiusLine.equiv` (`s = (h' + 1 − ā)/(ā h')`): the line `ℓ` of the special fibre of the Tate
curve minus its two nodes `h' = 0, −1` (sent to `t = 0, 1`; the cusp `h' = ∞` goes to `t = ā`).
-/

namespace SemistableReduction

namespace P1Three

open EtaleTower

noncomputable section

universe u

variable {O : Type u} [CommRing O] (a : O) {k : Type u} [Field k] {θ : O →+* k}
  [Fact (Function.Surjective θ)]

/-- **`R1/J ≃ k[h', 1/(h'(h' + 1))]`** (Möbius re-charting of `V₁` onto the Tate line minus its
nodes). -/
def vertexChartEquiv (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) : Ts θ (R1 O a) ≃+* MobiusLine.B k :=
  ((tsEquiv1 a (θ := θ)).trans (lineEquiv k (θ a)).toRingEquiv).trans
    (MobiusLine.equiv ha0 ha1).toRingEquiv

lemma vertexChartEquiv_s1 (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) :
    vertexChartEquiv a ha0 ha1 (Ideal.Quotient.mk _ (s1 O a)) = MobiusLine.sImg (θ a) := by
  rw [vertexChartEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, tsEquiv1_mk]
  change MobiusLine.equiv ha0 ha1 (lineEquiv k (θ a) (toBar1 a (AdjoinRoot.root _))) = _
  rw [toBar1_root]
  exact (congrArg (MobiusLine.equiv ha0 ha1) (lineEquiv_s1 k (θ a))).trans
    (MobiusLine.equiv_s ha0 ha1)

end

end P1Three

end SemistableReduction
