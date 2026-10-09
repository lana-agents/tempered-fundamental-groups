/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremBCrossing
import TemperedFundamentalGroups.SemistableReduction.W10MainComponent
import TemperedFundamentalGroups.SemistableReduction.W10TreeUnfoldedProof

/-!
# Theorem B with `StrongComponentA` reduced to its targeted inputs

`StrongComponentA` follows from `W10.TreeComponentsUnfolded` (the component models are split,
without loops and unfolded) and `Statement.ZariskiConnected`
(`Statement.strongComponentA_of`). Hence:

* `TateObject.exists_character_ne_one_of_unfolded`;
* `TateOrbicurve.nondegenerate_of_unfolded` (IUT's orbicurves with a good Tate presentation).

`NodeOfTwoComponents` (`SemistableReduction.nodeOfTwoComponents`), `HarmonicX` and `CrossingX1`
are proved; the only remaining inputs are `TreeComponentsUnfolded` and `ZariskiConnected`.
`TreeComponentsUnfolded` follows from `W10.TreeComponentsGeomIrred` (geometric irreducibility of the
components; `W10.treeComponentsUnfolded_of`), giving `nondegenerate_of_geomIrred`.
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

/-- **Theorem B (scheme case)** from `TreeComponentsUnfolded` and `ZariskiConnected`. -/
theorem exists_character_ne_one_of_unfolded
    (hU : _root_.SemistableReduction.W10.TreeComponentsUnfolded.{u})
    (hZ : SemistableReduction.Statement.ZariskiConnected.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (ϖ : O) (hϖ : Irreducible ϖ)
    (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hb : IsUnit T.b₆ ∨ (T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ≠ 0 ∧ T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ∣ T.π))
    (hx : Transcendental K T.x) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ ≠ 1 :=
  exists_character_ne_one_of_crossing T V hV
    (SemistableReduction.Statement.strongComponentA_of hU hZ) p hp hpm hR
    SemistableReduction.nodeOfTwoComponents ϖ hϖ hd hb hx

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
/-- **Theorem B for IUT's orbicurves** from `TreeComponentsUnfolded` and `ZariskiConnected`, for
an elliptic curve with a good Tate presentation. -/
theorem nondegenerate_of_unfolded
    (hU : _root_.SemistableReduction.W10.TreeComponentsUnfolded.{u})
    (hZ : SemistableReduction.Statement.ZariskiConnected.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite)
    (ϖ : O) (hϖ : Irreducible ϖ)
    (hgood : HasGoodTatePresentation W O) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) :=
  nondegenerate_of_crossing A A' V hV (SemistableReduction.Statement.strongComponentA_of hU hZ)
    p hp hpm hℓ hM SemistableReduction.nodeOfTwoComponents ϖ hϖ hgood

include A' in
/-- **Theorem B for IUT's orbicurves** from the geometric irreducibility of the components
(`W10.TreeComponentsGeomIrred`) and `ZariskiConnected`. -/
theorem nondegenerate_of_geomIrred
    (hG : _root_.SemistableReduction.W10.TreeComponentsGeomIrred.{u})
    (hZ : SemistableReduction.Statement.ZariskiConnected.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) (ϖ : O) (hϖ : Irreducible ϖ)
    (hgood : HasGoodTatePresentation W O) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) :=
  nondegenerate_of_unfolded A A' V hV (_root_.SemistableReduction.W10.treeComponentsUnfolded_of hG)
    hZ p hp hpm hℓ hM ϖ hϖ hgood

end TateOrbicurve

end

end TemperedFundamentalGroups
