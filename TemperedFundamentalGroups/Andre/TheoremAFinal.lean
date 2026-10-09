/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.Refinement
import TemperedFundamentalGroups.SemistableReduction.StrongAProof

/-!
# Theorem A, unconditionally

Blueprint §10. `andreEquiv` with the semistable-reduction input `hW` discharged by
`SemistableReduction.Statement.strongA`.
-/

universe u

namespace TemperedFundamentalGroups

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type u} [CommRing R] [Algebra K R]
  [Algebra.Smooth K R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω] [IsAlgClosed Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Theorem A** (André's identification of the tempered fundamental group), unconditionally. -/
noncomputable def andreEquiv' [IsDomain R] [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1) :
    temperedPi1 O R A V hV ≃ₜ* andreGroup O R A V hV :=
  andreEquiv V hV SemistableReduction.Statement.strongA hp hR

end TemperedFundamentalGroups
