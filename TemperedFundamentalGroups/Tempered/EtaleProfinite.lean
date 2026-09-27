/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Tempered.Etale

/-!
# The étale fundamental group of `[Spec R / A]` is profinite

If the geometric point `Ω` is a field, the fibres `B →ₐ[R] Ω` of the fibre functor on finite
étale covers of `[Spec R / A]` are finite, hence `etalePi1 R A Ω` is compact; it is Hausdorff and
totally separated, i.e. a profinite group (`etalePi1Profinite`).
-/

universe u

open CategoryTheory

namespace TemperedFundamentalGroups

noncomputable section

variable (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]
  (Ω : Type u) [Field Ω] [Algebra R Ω]

instance EquivEtale.finite_etaleFibre (X : EquivEtale R A) :
    Finite ((etaleFibre R A Ω).obj X) :=
  letI := X.finite
  inferInstanceAs (Finite (X.B →ₐ[R] Ω))

instance : CompactSpace (etalePi1 R A Ω) := FibreAut.compactSpace_of_finite _

/-- **The étale fundamental group** of `[Spec R / A]` at a geometric point `Spec Ω → Spec R`
(`Ω` a field), as a profinite group. -/
abbrev etalePi1Profinite : ProfiniteGrp.{u} := ProfiniteGrp.of (etalePi1 R A Ω)

end

end TemperedFundamentalGroups
