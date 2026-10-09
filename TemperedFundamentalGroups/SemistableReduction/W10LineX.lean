/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10ComponentClause

/-!
# The x-line in the components of `E ⊗_K B`

`ψ_one_tmul_X`: the image of the x-line `X ∈ B` (the `K[X]`-structure of `B`) in the component
`Comp K E B 𝔪` is the image of `X ∈ E(X)`.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields

attribute [local instance] polyAlgebra

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] {E : Type u} [Field E] [Algebra K E]

/-- **The x-line of the components.** -/
lemma ψ_one_tmul_X (𝔪 : MaximalSpectrum (LX K E B)) :
    ψ (K := K) (B := B) (E := E) (1 ⊗ₜ algebraMap K[X] B X) 𝔪 =
      algebraMap (RatFunc E) (Comp K E B 𝔪) RatFunc.X := by
  change Ideal.Quotient.mk 𝔪.asIdeal (algebraMap (BX K E B) (LX K E B)
    (tensorEquiv K E B (1 ⊗ₜ algebraMap K[X] B X))) =
      Ideal.Quotient.mk 𝔪.asIdeal (algebraMap (RatFunc E) (LX K E B) RatFunc.X)
  congr 1
  have h1 : BX.ofA K E B (algebraMap K[X] B X) = algebraMap E[X] (BX K E B) X := by
    change (Algebra.TensorProduct.includeRight : B →ₐ[K[X]] E[X] ⊗[K[X]] B)
      (algebraMap K[X] B X) = _
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    change algebraMap E[X] (E[X] ⊗[K[X]] B) (Polynomial.map (algebraMap K E) X) = _
    rw [Polynomial.map_X]
    rfl
  rw [tensorEquiv_one_tmul, h1, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply E[X] (RatFunc E) (LX K E B), RatFunc.algebraMap_X]

end W10Assembly

end SemistableReduction
