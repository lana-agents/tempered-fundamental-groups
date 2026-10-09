/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictCrossing
import TemperedFundamentalGroups.Andre.TateRestrictFinal
import TemperedFundamentalGroups.Andre.TateRestrictInduced
import TemperedFundamentalGroups.Andre.TateRestrictOrbicurve
import TemperedFundamentalGroups.Andre.TheoremBGoodTate

/-!
# Theorem B for `v(q) = 1` (Blueprint §10.3.8, B4)

* `TateRestrict.exists_character'_ne_one`: the character of the restricted Tate object `X₀'` is
  nontrivial (scheme case), with no hypotheses beyond the data (`b₆` a unit, `x` transcendental).
* `TateOrbicurve.nondegenerate_of_isTate1`: **Theorem B for IUT's orbicurves `[Y/A]` with
  `W : y² + xy = x³ + ϖ b₄ x + ϖ b₆`, `b₆` a unit** (`v(q) = 1`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open RamifiedQuadratic SemistableReduction.W10Apply

namespace TateRestrict

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} {ϖ : O}
  (hϖ : Irreducible ϖ) [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  (R : Type u) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R] {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Theorem B for the restricted Tate object** (`v(q) = 1`, scheme case): some element of
`temperedPi1` has nontrivial character, for `b₆` a unit and `x` transcendental. -/
theorem exists_character'_ne_one [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ)
    (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (hb : IsUnit b₆) (hx : Transcendental K x) :
    ∃ τ : temperedPi1 O R A V hV, character' hϖ b₄ b₆ R heqR A V hV τ ≠ 1 :=
  exists_character'_ne_one_of hϖ b₄ b₆ R heqR A V hV
    (SemistableReduction.Statement.strongComponentAS_of
      SemistableReduction.Statement.zariskiConnected) p hp hpm hR
    SemistableReduction.nodeOfTwoComponents
    (fun P a ↦ P.exists_image_eq_C_R hϖ b₄ b₆ heqR hx a)
    {(decompR hϖ b₄ b₆).E}
    (fun S hS ↦ by
      rw [Set.mem_singleton_iff.1 hS]
      exact ⟨subset_rfl, not_E_eq_singleton hϖ b₄ b₆⟩)
    (fun Q a ↦ Q.harmonicTateR_of_crossingX1 hϖ b₄ b₆ heqR SemistableReduction.crossingX1S hb
      hx a)

end TateRestrict

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
/-- **Theorem B for IUT's orbicurves with `v(q) = 1`**: for
`W : y² + xy = x³ + ϖ b₄ x + ϖ b₆` with `ϖ` a uniformizer and `b₆` a unit,
`temperedPi1 [Y/A]` (`Y = E ∖ (E[ℓ] + M)`) has an open normal subgroup with infinite quotient. -/
theorem nondegenerate_of_isTate1 [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ)
    (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) {ϖ b₄ b₆ : O} (hϖ : Irreducible ϖ)
    (hW : IsTate1 W ϖ b₄ b₆) (hb : IsUnit b₆) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) := by
  haveI := smooth_geomOrbicurveRing_of_charZero (W := W) hℓ hM
  haveI : Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆))) := ⟨squarefree_of_isTate1 hW⟩
  exact TateRestrict.exists_open_normal_infinite_quotient_of_ne_one' (A := A) A' hϖ b₄ b₆
    (heqR_of_isTate1 hW ℓ M) V hV
    (TateRestrict.exists_character'_ne_one hϖ b₄ b₆ _ (heqR_of_isTate1 hW ℓ M) A' V hV p hp hpm
      (ringKrullDim_geomOrbicurveRing_of_charZero hℓ hM) hb (transcendental_xR ℓ M))

include A' in
/-- **Theorem B for IUT's orbicurves, every Tate curve in normal form**: for
`W : y² + xy = x³ + a₄ x + a₆` with `ϖ^m ∣ a₄`, `a₆ = ϖ^m ε` (`ε` a unit) and `m ≥ 1`,
`temperedPi1 [Y/A]` (`Y = E ∖ (E[ℓ] + M)`) has an open normal subgroup with infinite quotient.
`m = 1` is the restricted Tate object over `K(√ϖ)` (`nondegenerate_of_isTate1`), `m ≥ 2` the Tate
object (`nondegenerate_of_goodTate`). -/
theorem nondegenerate_of_normalForm [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ)
    (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) {ϖ : O} (hϖ : Irreducible ϖ) (ha₁ : W.a₁ = 1)
    (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0) {m : ℕ} (hm : 1 ≤ m) (u₄ : O)
    (ha₄ : W.a₄ = ((ϖ ^ m * u₄ : O) : K)) (ε : Oˣ) (ha₆ : W.a₆ = ((ϖ ^ m * ε : O) : K)) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) := by
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    refine nondegenerate_of_isTate1 A A' V hV p hp hpm hℓ hM hϖ (b₄ := u₄) (b₆ := ε)
      ⟨ha₁, ha₂, ha₃, ?_, ?_⟩ ε.isUnit
    · rw [ha₄, pow_one]; push_cast; rfl
    · rw [ha₆, pow_one]; push_cast; rfl
  · exact TateOrbicurve.nondegenerate_of_goodTate A A' V hV p hp hpm hℓ hM ϖ hϖ
      (hasGoodTatePresentation_of_normalForm hϖ ha₁ ha₂ ha₃ h2 u₄ ha₄ ε ha₆)

end TateOrbicurve

end

end TemperedFundamentalGroups
