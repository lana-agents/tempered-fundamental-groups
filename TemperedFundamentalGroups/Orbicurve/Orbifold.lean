/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Orbicurve.Model
import TemperedFundamentalGroups.Setup.Orbifold

/-!
# IUT's model orbicurves as pointed affine orbifolds

The orbicurve `(E, ℓ, M, ±)` is presented as `[Y / A]` with `Y = Spec R`,
`R = orbicurveRing W ℓ M` (the coordinate ring of `E ∖ (E(k)[ℓ] + M)`), `A = affGroup W M pm`
(the maps `P ↦ εP + m`, `m ∈ M`, `ε = 1` or `ε = ±1` when `pm` is set), and the generic
geometric point `R ⊆ k(E) → Ω = k(E)^alg`. When `E[ℓ] ⊆ E(k)` and `M ⊆ E(k)[ℓ]` this is
`(E/M) ∖ (E[ℓ]/M)`, resp. its quotient by `{±1}`.
-/

universe u

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

/-- The model orbicurve `(E, ℓ, M, ±)` as a pointed affine orbifold (generic geometric point). -/
def orbicurveOrbifold (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    AffineOrbifold k :=
  letI : Algebra (orbicurveRing W ℓ M) (AlgebraicClosure (funField W)) :=
    ((algebraMap (funField W) (AlgebraicClosure (funField W))).comp
      (orbicurveRing W ℓ M).val.toRingHom).toAlgebra
  { R := orbicurveRing W ℓ M
    A := affGroup W M pm
    Ω := AlgebraicClosure (funField W)
    tower := IsScalarTower.of_algebraMap_eq fun a => by
      change _ = algebraMap (funField W) _ (algebraMap k (funField W) a)
      rw [← IsScalarTower.algebraMap_apply] }

end

end TemperedFundamentalGroups.Orbicurve
