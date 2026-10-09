/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremBFinal
import TemperedFundamentalGroups.Andre.TateCrossing
import TemperedFundamentalGroups.SemistableReduction.CrossingX1Proof

/-!
# Theorem B with `CrossingX1` in place of `HarmonicTate` (Blueprint §10.3.8)

When `b₆` is a unit (the special fibre of the Tate model is the 2-gon `C ∪ E`), the targeted
`HarmonicTate` follows from `Statement.CrossingX1` (`Pres.harmonicTate_of_crossingX1`), which is
proved (`SemistableReduction.crossingX1`). So Theorem B and its IUT corollary hold without
`HarmonicTate`:

* `TateObject.exists_character_ne_one_of_crossing`;
* `TateOrbicurve.nondegenerate_of_crossing`.
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

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Algebra.Smooth K R] in
/-- The conic `E` is not a point. -/
lemma decomp_E_not_singleton : ¬ ∃ y, (decomp (A := A) T).E = {y} := by
  rintro ⟨y, hy⟩
  obtain ⟨-, -, hpq, -⟩ := decomp_spec (A := A) T
  have hp : TateModel.pZ T.π T.b₄ T.b₆ T.π_mem ∈ (decomp (A := A) T).E :=
    TateModel.pZ_mem_Eset T.π_mem
  have hq : TateModel.qZ T.π T.b₄ T.b₆ T.π_mem ∈ (decomp (A := A) T).E :=
    TateModel.qZ_mem_Eset T.π_mem
  rw [hy] at hp hq
  exact hpq (hp.trans hq.symm)

/-- **Theorem B (scheme case) without `HarmonicTate`**, for `b₆` a unit. -/
theorem exists_character_ne_one_of_crossing
    (hW : SemistableReduction.Statement.StrongComponentA.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆)) (hb : IsUnit T.b₆)
    (hx : Transcendental K T.x) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ ≠ 1 := by
  haveI : Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆)) := ⟨hd⟩
  exact exists_character_ne_one T V hV hW p hp hpm hR hX hN ϖ hϖ {(decomp (A := A) T).E}
    (fun S hS => by
      rw [Set.mem_singleton_iff.1 hS]
      exact ⟨subset_rfl, decomp_E_not_singleton T⟩)
    (fun P a => P.harmonicTate_of_crossingX1 T SemistableReduction.crossingX1 hb hx hϖ a) hd hx

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
/-- **Theorem B for IUT's orbicurves without `HarmonicTate`**, for Tate data with `b₆` a unit:
`temperedPi1 [Y/A]` has an open normal subgroup with infinite quotient. -/
theorem nondegenerate_of_crossing (hSCA : SemistableReduction.Statement.StrongComponentA.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite)
    (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0) (hπm : π ∈ IsLocalRing.maximalIdeal O)
    (hb : IsUnit b₆) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) := by
  haveI := smooth_geomOrbicurveRing_of_charZero (W := W) hℓ hM
  have h2 : (2 : O) ≠ 0 := fun h => two_ne_zero (congrArg Subtype.val h : ((2 : O) : K) = 0)
  have hΔ : TateNormal.tateDisc π b₄ b₆ ≠ 0 := by
    intro h
    have hW' := TateNormal.Δ_eq_tateDisc (π := π) (b₄ := b₄) (b₆ := b₆) O.subtype W hW.a₁ hW.a₂
      hW.a₃ (by rw [hW.a₄]; simp) (by rw [hW.a₆]; simp)
    rw [h, map_zero] at hW'
    exact W.isUnit_Δ.ne_zero hW'
  refine nondegenerate_of_character_ne_one A A' V hV hW hπ hπm ?_
  exact TateObject.exists_character_ne_one_of_crossing (data hW hπ hπm ℓ M) V hV hSCA p hp hpm
    (ringKrullDim_geomOrbicurveRing_of_charZero hℓ hM) hX hN ϖ hϖ
    (TateNormal.squarefree_dpoly π b₄ b₆ h2 hΔ) hb (transcendental_data_x hW hπ hπm ℓ M)

end TateOrbicurve

end

end TemperedFundamentalGroups
