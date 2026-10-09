/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Orbicurve.GeomModel
import TemperedFundamentalGroups.Setup.Orbifold

/-!
# IUT's model orbicurves as pointed affine orbifolds

The orbicurve `(E, ℓ, M, ±)` over a field `k` (an elliptic curve `E`, a level `ℓ`, a subgroup
`M ≤ E(k)` and a sign flag) is presented as `[Y / A]` with

* `Y = Spec R`, `R = geomOrbicurveRing W ℓ M = ringAway W (E[ℓ] + M)`, the ring of functions
  on `E` regular away from the closed subset `E[ℓ] + M` — all of its geometric points, not
  only the rational ones — so that `Y = E ∖ (E[ℓ] + M)`;
* `A = affGroup W M pm`: the maps `P ↦ εP + m`, `m ∈ M`, `ε = 1` (or `ε = ±1` when `pm` is
  set), acting on `R` by `k`-algebra automorphisms (`E[ℓ] + M` is `A`-stable);
* the generic geometric point `R ⊆ k(E) → Ω = k(E)^alg`.

For every field `k`, `[Y / A]` is thus `(E/M) ∖ (E[ℓ]/M)`, resp. its quotient by `{±1}` (for
`M ≤ E(k)[ℓ]` as in IUT, `E[ℓ] + M = E[ℓ]`). When `E[ℓ] + M` is finite — for `ℓ ≥ 1` and finite
`M` in characteristic `0` or in characteristic `p ∤ 2ℓ` — `R` is the localization `k[E][Ψ(x)⁻¹]`
of the affine coordinate ring at a function `Ψ(x)` with zero set `(E[ℓ] + M) ∖ {0}`
(`exists_isLocalization_geomOrbicurveRing_of_charZero`,
`exists_isLocalization_geomOrbicurveRing_of_not_dvd_charP`), so that `Y` is the open subscheme
`D(Ψ(x)) = E ∖ (E[ℓ] + M)` of `E`.
-/

universe u

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

/-- The model orbicurve `(E, ℓ, M, ±)` as a pointed affine orbifold `[(E ∖ (E[ℓ] + M)) / A]`
(generic geometric point). -/
def orbicurveOrbifold (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    AffineOrbifold k :=
  letI : Algebra (geomOrbicurveRing W ℓ M) (AlgebraicClosure (funField W)) :=
    ((algebraMap (funField W) (AlgebraicClosure (funField W))).comp
      (geomOrbicurveRing W ℓ M).val.toRingHom).toAlgebra
  { R := geomOrbicurveRing W ℓ M
    A := affGroup W M pm
    Ω := AlgebraicClosure (funField W)
    tower := IsScalarTower.of_algebraMap_eq fun a => by
      change _ = algebraMap (funField W) _ (algebraMap k (funField W) a)
      rw [← IsScalarTower.algebraMap_apply] }

lemma orbicurveOrbifold_R (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    (orbicurveOrbifold W ℓ M pm).R = geomOrbicurveRing W ℓ M :=
  rfl

end

end TemperedFundamentalGroups.Orbicurve
