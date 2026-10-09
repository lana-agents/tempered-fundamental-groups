/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Setup.Valuation
import TemperedFundamentalGroups.Tempered.Comparison
import Pi1.Orbifold.EtaleProfinite

/-!
# Pointed affine orbifolds and their fundamental groups

`AffineOrbifold k` bundles the data of Blueprint §3.1 except the valuation: a commutative
`k`-algebra `R` with an action of a group `A` by `k`-algebra automorphisms (the orbifold
`[Spec R / A]`) and a geometric point `R → Ω` into a field `Ω ⊇ k`.

For a valuation subring `O` of `k`, `AffineOrbifold.temperedPi1 X O` is the tempered fundamental
group, the valuation on `Ω` being a chosen extension of `O` (Chevalley,
`ValuationSubring.exists_comap_eq`); `AffineOrbifold.etalePi1 X` is the (profinite) étale
fundamental group and `AffineOrbifold.temperedToEtale X O` the continuous comparison map.
With `O = canonicalValuationSubring k` this is the form in which the construction is consumed by
`Iut.Anabelian.TemperedPi1Theory`, whose orbicurves only carry `[Field k]`.
-/

universe u

open Pi1.Orbifold

namespace TemperedFundamentalGroups

/-- **A pointed affine orbifold** `[Spec R / A]` over `k` with a geometric point `R → Ω`. -/
structure AffineOrbifold (k : Type u) [Field k] : Type (u + 1) where
  /-- The coordinate ring. -/
  R : Type u
  [commRing : CommRing R]
  [algebra : Algebra k R]
  /-- The group acting. -/
  A : Type u
  [group : Group A]
  [action : MulSemiringAction A R]
  [smulComm : SMulCommClass A k R]
  /-- The field of the geometric point. -/
  Ω : Type u
  [field : Field Ω]
  [algebraKΩ : Algebra k Ω]
  [algebraRΩ : Algebra R Ω]
  [tower : IsScalarTower k R Ω]

namespace AffineOrbifold

attribute [instance] commRing algebra group action smulComm field algebraKΩ algebraRΩ tower

variable {k : Type u} [Field k] (X : AffineOrbifold k) (O : ValuationSubring k)

/-- The chosen extension of `O` to the field `Ω` of the geometric point. -/
noncomputable def V : ValuationSubring X.Ω := (ValuationSubring.exists_comap_eq (Ω := X.Ω) O).choose

lemma V_comap : (X.V O).comap (algebraMap k X.Ω) = O :=
  (ValuationSubring.exists_comap_eq (Ω := X.Ω) O).choose_spec

/-- **The tempered fundamental group** of the orbifold over the valued field `(k, O)`. -/
abbrev temperedPi1 : Type u := TemperedFundamentalGroups.temperedPi1 O X.R X.A (X.V O) (X.V_comap O)

/-- **The étale fundamental group** of the orbifold. -/
abbrev etalePi1 : Type u := Pi1.Orbifold.etalePi1 X.R X.A X.Ω

/-- The étale fundamental group as a profinite group. -/
noncomputable abbrev etalePi1Profinite : ProfiniteGrp.{u} :=
  Pi1.Orbifold.etalePi1Profinite X.R X.A X.Ω

/-- **The comparison homomorphism** from the tempered to the étale fundamental group. -/
noncomputable def temperedToEtale : X.temperedPi1 O →* X.etalePi1 :=
  TemperedFundamentalGroups.temperedToEtale O X.R X.A (X.V O) (X.V_comap O)

lemma continuous_temperedToEtale : Continuous (X.temperedToEtale O) :=
  TemperedFundamentalGroups.continuous_temperedToEtale O X.R X.A (X.V O) (X.V_comap O)

/-- The tempered fundamental group for the canonical valuation of `k`
(`canonicalValuationSubring`). -/
abbrev canonicalTemperedPi1 : Type u := X.temperedPi1 (canonicalValuationSubring k)

end AffineOrbifold

end TemperedFundamentalGroups
