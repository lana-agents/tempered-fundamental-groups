/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremBUnfolded
import TemperedFundamentalGroups.SemistableReduction.ZariskiConnectedProof

/-!
# Theorem B without targeted hypotheses (good Tate presentations)

`Statement.ZariskiConnected` is proved (`Statement.zariskiConnected`), so the forms of
`TheoremBUnfolded` hold with no hypothesis beyond the Tate data:

* `TateObject.exists_character_ne_one_of_goodTate`;
* `TateOrbicurve.nondegenerate_of_goodTate`: IUT's orbicurves with `HasGoodTatePresentation`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

namespace TateObject

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] (T : Data O R)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Theorem B (scheme case)** for good Tate data, with no further hypothesis. -/
theorem exists_character_ne_one_of_goodTate
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (ϖ : O) (hϖ : Irreducible ϖ)
    (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hb : IsUnit T.b₆ ∨ (T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ≠ 0 ∧ T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ∣ T.π))
    (hx : Transcendental K T.x) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ ≠ 1 :=
  exists_character_ne_one_of_zariski T V hV SemistableReduction.Statement.zariskiConnected
    p hp hpm hR ϖ hϖ hd hb hx

end TateObject

namespace TateOrbicurve

open Orbicurve

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {W : WeierstrassCurve K} [W.IsElliptic]
  [DecidableEq K]
  (A : Type u) [Group A] [Finite A] (A' : Type u) [Group A'] [Subsingleton A']
  {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
  [MulSemiringAction A (geomOrbicurveRing W ℓ M)] [SMulCommClass A K (geomOrbicurveRing W ℓ M)]
  [MulSemiringAction A' (geomOrbicurveRing W ℓ M)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra (geomOrbicurveRing W ℓ M) Ω]
  [IsScalarTower K (geomOrbicurveRing W ℓ M) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

include A' in
/-- **Theorem B for IUT's orbicurves** with a good Tate presentation, with no further
hypothesis: `temperedPi1 [Y/A]` has an open normal subgroup with infinite quotient. -/
theorem nondegenerate_of_goodTate
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) (ϖ : O) (hϖ : Irreducible ϖ)
    (hgood : HasGoodTatePresentation W O) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) :=
  nondegenerate_of_zariski A A' V hV SemistableReduction.Statement.zariskiConnected
    p hp hpm hℓ hM ϖ hϖ hgood

end TateOrbicurve

end

end TemperedFundamentalGroups
