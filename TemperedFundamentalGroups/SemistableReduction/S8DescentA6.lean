/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8DescentChart
import TemperedFundamentalGroups.SemistableReduction.TypeOneGerm

/-!
# A6 in its owner's form

Blueprint §9.10 A6, §9.12 O6.1f(iii). `ClassicalSmooth.A6For C E L` (smooth points descend along
a Galois extension `L / E`, on the vertex charts `DRint 0 1 (Aff a c E)`) from
`S8A.Descent.isDiscSmooth_of_galois`, applied to the twists `Aff a c E ⊆ Aff a c L`.
-/

namespace SemistableReduction

namespace ClassicalSmooth

open GaussFibre DiscCount SmoothVertex AffineTwist S8A.Descent

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E L : Type*} [Field E] [Field L] [Algebra (RatFunc C) E] [Algebra (RatFunc C) L]
  [Algebra E L] [IsScalarTower (RatFunc C) E L] [Algebra C E] [Algebra C L]
  [IsScalarTower C (RatFunc C) E] [IsScalarTower C (RatFunc C) L]
  [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]

/-- `algebraMap E L` between the twists. -/
@[reducible] noncomputable def algebraAffAff (a c : C) (hc : c ≠ 0) :
    Algebra (Aff a c hc E) (Aff a c hc L) :=
  inferInstanceAs (Algebra E L)

attribute [local instance] algebraAffAff

omit [IsAlgClosed C] [CharZero C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) E]
  [FiniteDimensional (RatFunc C) L] in
lemma isScalarTower_affAff (a c : C) (hc : c ≠ 0) :
    IsScalarTower (RatFunc C) (Aff a c hc E) (Aff a c hc L) :=
  IsScalarTower.of_algebraMap_eq fun φ ↦
    (IsScalarTower.algebraMap_apply (RatFunc C) E L (aff a c hc φ))

include hp hp1 in
/-- **A6** (Blueprint §9.10 L1 A6, O6.1f(iii)): smooth points descend along Galois extensions. -/
theorem a6For [IsGalois E L] : A6For C E L := by
  intro a c hc P' hP' _ hsm
  haveI := isScalarTower_affAff (E := E) (L := L) a c hc
  haveI : IsGalois (Aff a c hc E) (Aff a c hc L) := inferInstanceAs (IsGalois E L)
  exact isDiscSmooth_of_galois (E := Aff a c hc E) (L := Aff a c hc L) hp hp1
    fun Q hQ hQP ↦ hsm Q hQ hQP

end ClassicalSmooth

end SemistableReduction
