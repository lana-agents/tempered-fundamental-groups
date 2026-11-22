/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Localization.Integral

/-!
# The normalisation in a separable extension is unramified at the zero prime (MR12, debt D3)

**`UnramifiedBot.isUnramifiedAt_bot`**: if `B` is the integral closure of a domain `R` (fraction
field `K`) in a finite separable extension `L / K`, then `B` is unramified over `R` at `⊥`
(`B_(0) = L` and `L / K` is separable).

Use for the debt `hunr` (D3/A1) of the Tate S5/S6 statements (`hunr₀`, `hunr₁` in `TateS5`): the
primes `𝔮 = Q ∩ R` strictly inside a maximal ideal `P ∋ ϖ` of a chart `R` of dimension two are
`⊥`, the horizontal height-one primes (`ϖ ∉ 𝔮`: unramifiedness there is the étaleness of the
generic-fibre cover off the cusp, an input of the cover) and the vertical height-one primes
(`ϖ ∈ 𝔮`, the generic points of the special-fibre components: the remaining debt A1, Abhyankar
after a tame base change). This file discharges the case `⊥` and splits `hunr` into the
horizontal and vertical cases (**`UnramifiedBot.isUnramifiedAt_of_split`**).
-/

namespace SemistableReduction

namespace UnramifiedBot

/-- **The normalisation is unramified at the zero prime.** -/
theorem isUnramifiedAt_bot (R : Type*) {K L B : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Algebra R L] [IsScalarTower R K L] [CommRing B] [Algebra R B]
    [Algebra B L] [IsScalarTower R B L] [IsIntegralClosure B R L] :
    haveI : IsDomain B :=
      (IsIntegralClosure.algebraMap_injective B R L).isDomain (algebraMap B L)
    Algebra.IsUnramifiedAt R (⊥ : Ideal B) := by
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B R L).isDomain (algebraMap B L)
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension R K L B
  have : IsLocalization (nonZeroDivisors B) (Localization.AtPrime (⊥ : Ideal B)) := by
    convert!
      (inferInstance :
        IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B)))
    ext; simp [Ideal.primeCompl]
  haveI : Algebra.FormallyUnramified R K := .of_isLocalization (nonZeroDivisors R)
  haveI : Algebra.FormallyUnramified K L := by
    rwa [Algebra.FormallyUnramified.iff_isSeparable]
  haveI : Algebra.FormallyUnramified R L := .comp R K L
  exact (Algebra.FormallyUnramified.iff_of_equiv
    ((IsLocalization.algEquiv (nonZeroDivisors B) L _).restrictScalars R)).mp inferInstance

/-- **Splitting `hunr`** (D3/A1): unramifiedness at every prime `Q` of the normalisation lying over
a prime strictly inside a maximal ideal `P ∋ ϖ` (and satisfying an extra condition `p`, e.g. "not
the origin section" for `hunr₀`) follows from the horizontal case (`ϖ ∉ Q ∩ R`, `Q ≠ ⊥`: the
generic-fibre cover) and the vertical case (`ϖ ∈ Q ∩ R`: the generic points of the special
fibre); the case `Q = ⊥` is `isUnramifiedAt_bot`. -/
theorem isUnramifiedAt_of_split (R : Type*) {K L B : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Algebra R L] [IsScalarTower R K L] [CommRing B] [Algebra R B]
    [Algebra B L] [IsScalarTower R B L] [IsIntegralClosure B R L] (ϖ : R) (p : Ideal R → Prop)
    (hH : ∀ (P : Ideal R) [P.IsMaximal], ϖ ∈ P → ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap R B) < P → p (Q.comap (algebraMap R B)) → Q ≠ ⊥ →
        ϖ ∉ Q.comap (algebraMap R B) → Algebra.IsUnramifiedAt R Q)
    (hV : ∀ (P : Ideal R) [P.IsMaximal], ϖ ∈ P → ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap R B) < P → p (Q.comap (algebraMap R B)) →
        ϖ ∈ Q.comap (algebraMap R B) → Algebra.IsUnramifiedAt R Q)
    (P : Ideal R) [P.IsMaximal] (hϖ : ϖ ∈ P) (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R B) < P) (hp : p (Q.comap (algebraMap R B))) :
    Algebra.IsUnramifiedAt R Q := by
  by_cases hQ0 : Q = ⊥
  · subst hQ0
    exact isUnramifiedAt_bot R (K := K) (L := L)
  by_cases hϖQ : ϖ ∈ Q.comap (algebraMap R B)
  · exact hV P hϖ Q hQ hp hϖQ
  · exact hH P hϖ Q hQ hp hQ0 hϖQ

end UnramifiedBot

end SemistableReduction
