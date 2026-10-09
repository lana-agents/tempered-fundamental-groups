/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhaustGluing

/-!
# The two `δ`-count steps of O12 (named interfaces, R5)

Blueprint §9.12, O12. The local `δ`-formula (`LocalFormula.local_formula`) yields two statements
about exhausting discs, from which (D⇐) `SmoothOfDiscCond` and (T⇐) `ExhaustingOfTube` follow by
germ/limit arguments:

* `ExhaustDescentFor`: if `D(b, |d c'|)` is exhausting in `U = D(b, |d|)` and `w_{b,|d c'|}` is a
  disc of a tube, a singular point over `U` forces a singular point over a residue class of `D`;
* `ExhaustGlueFor`: exhaustion glues through a Gauss point `w_{a,|c u|}` which is a circle of a tube
  and whose residue classes off the centre are good.
-/

namespace SemistableReduction

namespace ExhaustGluing

open AffineTwist

lemma norm_mul_lt_one {K : Type*} [NormedField K] {u u' : K} (hu : ‖u‖ < 1) (hu' : ‖u'‖ < 1) :
    ‖u * u'‖ < 1 := by
  rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hu hu'.le

variable (C : Type*) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- **Descent of singularities into an exhausting disc of a tube.** -/
def ExhaustDescentFor : Prop :=
  ∀ (b d c' : C) (hd : d ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0),
    IsExhausting b hd hc' hc0' F → IsTubeDisc F b (mul_ne_zero hd hc0') →
      ¬ DiscSmooth F b hd → ∃ β : C, ‖β‖ ≤ 1 ∧ ¬ DiscSmooth F (b + d * c' * β) (mul_ne_zero hd hc0')

/-- **Gluing of exhaustion through a circle of a tube.** -/
def ExhaustGlueFor : Prop :=
  ∀ (a c u u' : C) (hc : c ≠ 0) (hu : ‖u‖ < 1) (hu0 : u ≠ 0) (hu' : ‖u'‖ < 1) (hu0' : u' ≠ 0),
    IsExhausting a hc hu hu0 F → IsExhausting a (mul_ne_zero hc hu0) hu' hu0' F →
      IsTubeCircle F a (mul_ne_zero hc hu0) →
      (∀ β : C, ‖β‖ = 1 → DiscSmooth F (a + c * u * β) (mul_ne_zero hc hu0)) →
        IsExhausting a hc (norm_mul_lt_one hu hu') (mul_ne_zero hu0 hu0') F

end ExhaustGluing

end SemistableReduction
