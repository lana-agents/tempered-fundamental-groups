/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Statement

/-!
# `Statement.ZariskiConnected` (targeted hypothesis, Blueprint §10.3.8)

Only a **definition**. A semistable projective model `c'` over the valuation ring `O'` of a
finite extension `K'` of a complete discretely valued field `K` (characteristic `0`), whose
generic fibre is integral (a scheme-theoretically dominant point `Spec L ⟶ c'` over `O'` from a
field `L`), has a **connected special fibre**.

This is Zariski's connectedness theorem: `c'` is normal (semistable), proper and flat over `O'`,
and by Stein factorization its special fibre is connected because `Γ(c', O)` is a finite
`O'`-algebra contained in `L`, i.e. a domain finite over the henselian `O'`, hence local. It is
used for the component clause of `Statement.StrongComponentA` (connected special fibres of the
summands of the W10 model). It is proved in `SemistableReduction/ZariskiConnectedProof.lean`
(`Statement.zariskiConnected`), from Zariski's connectedness theorem for integral projective
schemes over a complete DVR in oka (`AlgebraicGeometry.ProjectiveSpace.isPreconnected_closedFibre`,
via Serre finiteness and the degree-zero theorem on formal functions).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

/-- **Zariski connectedness for semistable models with integral generic fibre** (targeted). -/
def Statement.ZariskiConnected : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    (_ : O'.comap (algebraMap K K') = O) [IsDiscreteValuationRing O'] (ϖ' : O')
    (_ : Irreducible ϖ') (L : Type u) [Field L] [Algebra O' L]
    (c' : TemperedFundamentalGroups.ModelCode O') (j' : Spec (CommRingCat.of L) ⟶ c'.scheme),
    ModelCode.IsSemistable ϖ' c' → IsSchemeTheoreticallyDominant j' →
      j' ≫ c'.toSpec = Spec.map (CommRingCat.ofHom (algebraMap O' L)) →
      ConnectedSpace (specialFibre c'.toSpec)

end TemperedFundamentalGroups.SemistableReduction
