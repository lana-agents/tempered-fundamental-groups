/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The quadratic standard étale algebra `A[S]/(S² + S − c)` away from `2S + 1`

(Blueprint §12.8, M2.3 (a'), generic commutative algebra.) Near its two nodes `p` (`s = 0`) and
`q` (`s = −1`) the chart `x₀ ≠ 0` of the Tate model is `A_D[S]/(S² + S − c)` over the node ring
`A = O[u,v]/(uv − ϖⁿ)` (`TateNormal.eq_zero_of_nodeToL_add_mul_sL_eq_zero` for the injectivity);
the derivative of `S² + S − c` is `2S + 1`, a unit at both nodes (`±1`), so it is standard étale
there, with no condition on the residue characteristic:

* `QuadraticEtale.pair c`: the standard étale pair `(X² + X − c, 2X + 1)`
  (`f′ · 1 + f · 0 = g`);
* **`QuadraticEtale.etale`**: `(A[S]/(S² + S − c))[1/(2S + 1)]` is étale over `A`
  (Mathlib `StandardEtalePair.equivAwayAdjoinRoot`).
-/

open Polynomial

namespace SemistableReduction

namespace QuadraticEtale

variable {A : Type*} [CommRing A] (c : A)

/-- The quadratic polynomial `X² + X − c`. -/
noncomputable def poly : A[X] := X ^ 2 + X - C c

lemma monic_poly : (poly c).Monic := by
  nontriviality A
  have h : poly c = X ^ 2 + (X - C c) := by unfold poly; ring
  rw [h]
  refine (monic_X_pow 2).add_of_left ?_
  rw [degree_X_pow, degree_X_sub_C]
  norm_num

/-- **The standard étale pair** `(X² + X − c, 2X + 1)`. -/
noncomputable def pair : StandardEtalePair A where
  f := poly c
  monic_f := monic_poly c
  g := 2 * X + 1
  cond := ⟨1, 0, 1, by
    simp only [poly, derivative_sub, derivative_add, derivative_X_pow, derivative_X,
      derivative_C, mul_one, mul_zero, add_zero, pow_one, sub_zero]
    push_cast
    rw [map_ofNat C 2]
    ring⟩

/-- **`(A[S]/(S² + S − c))[1/(2S + 1)]` is étale over `A`.** -/
theorem etale : Algebra.Etale A (Localization.Away (AdjoinRoot.mk (poly c) (2 * X + 1))) :=
  Algebra.Etale.of_equiv (pair c).equivAwayAdjoinRoot

end QuadraticEtale

end SemistableReduction
