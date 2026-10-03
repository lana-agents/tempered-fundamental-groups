/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Statement

/-!
# Points on two components are nodes (geometric input for B5)

The dual graph of a model `c` (`DualGraph.lean`) has as edges the **node points**
(`ModelCode.IsNodePt`: points of the special fibre which are not smooth, i.e. not étale-locally
the affine line `O[u]`), while the universal covering of the special fibre
(`TemperedFundamentalGroups.universalCovering`, built from `curveConfig`) branches at the
**special points**: the points lying on two distinct irreducible components. Theorem B (B5)
needs that these agree, i.e. that a smooth point lies on only one component.

`Statement.NodeOfTwoComponents` is this fact for semistable models over discrete valuation
rings. It is a statement of local commutative algebra (Blueprint §9.7, XL10, second half): at a
smooth point `y`, `c` is étale-locally `O[u]`, so the local ring of the special fibre at `y` has
an étale local neighbourhood which is a localization of `κ[u]`, a domain; flat local maps satisfy
going down, so the minimal primes of the local ring of the special fibre at `y` (the components
through `y`) inject into those of the neighbourhood, of which there is one. It is **not**
targeted on the W-chain; Theorem B takes it as an explicit hypothesis.
-/

universe u

namespace TemperedFundamentalGroups.SemistableReduction

/-- **Points on two components are nodes**: for a semistable projective model `c` over a
discrete valuation ring, every point of the special fibre lying on two distinct irreducible
components of the special fibre is a node point (equivalently: a smooth point lies on exactly
one component). -/
def Statement.NodeOfTwoComponents : Prop :=
  ∀ (K' : Type u) [Field K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O'] (ϖ' : O'),
    Irreducible ϖ' → ∀ c : TemperedFundamentalGroups.ModelCode O',
    ModelCode.IsSemistable ϖ' c → ∀ (y : c.scheme), ∀ v ∈ ModelCode.components c,
    ∀ w ∈ ModelCode.components c, v ≠ w → y ∈ v → y ∈ w → ModelCode.IsNodePt c y

end TemperedFundamentalGroups.SemistableReduction
