/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremBFinal
import TemperedFundamentalGroups.Andre.TateThreeGon
import TemperedFundamentalGroups.SemistableReduction.CrossingX1Proof
import TemperedFundamentalGroups.SemistableReduction.HarmonicXProof

/-!
# Theorem B with `CrossingX1` in place of `HarmonicTate` (Blueprint §10.3.8)

When `b₆` is a unit (the special fibre of the Tate model is the 2-gon `C ∪ E`), or for the 3-gon
when `c = b₆ − π² b₄² ≠ 0` divides `π`, the targeted `HarmonicTate` follows from
`Statement.CrossingX1` (`Pres.harmonicTate_of_crossingX1`, `harmonicTate_of_crossingX1_threeGon`),
which is proved (`SemistableReduction.crossingX1`). `Statement.HarmonicX` is proved as well
(`SemistableReduction.harmonicX`). So Theorem B and its IUT corollary hold without `HarmonicTate`
and without `HarmonicX`:

* `TateObject.exists_character_ne_one_of_crossing`;
* `TateOrbicurve.nondegenerate_of_crossing`, for `W` with a good Tate presentation
  (`TateOrbicurve.HasGoodTatePresentation`: `b₆` a unit, or `c = b₆ − π² b₄² ≠ 0` dividing `π`),
  e.g. normal-form Tate curves with `v(q) ≥ 2` (`hasGoodTatePresentation_of_normalForm`).
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

/-- **Theorem B (scheme case) without `HarmonicTate` and `HarmonicX`**, for Tate data with `b₆`
a unit (2-gon) or with `c = b₆ − π² b₄² ≠ 0` dividing `π` (3-gon with an exact node at `r`). -/
theorem exists_character_ne_one_of_crossing
    (hW : SemistableReduction.Statement.StrongComponentA.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hb : IsUnit T.b₆ ∨ (T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ≠ 0 ∧ T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ∣ T.π))
    (hx : Transcendental K T.x) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ ≠ 1 := by
  haveI : Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆)) := ⟨hd⟩
  by_cases hu : IsUnit T.b₆
  · exact exists_character_ne_one T V hV hW p hp hpm hR SemistableReduction.harmonicX hN ϖ hϖ
      {(decomp (A := A) T).E}
      (fun S hS => by
        rw [Set.mem_singleton_iff.1 hS]
        exact ⟨subset_rfl, decomp_E_not_singleton T⟩)
      (fun P a => P.harmonicTate_of_crossingX1 T SemistableReduction.crossingX1 hu hx hϖ a) hd hx
  · obtain ⟨hc0, hcπ⟩ := hb.resolve_left hu
    have hm : T.b₆ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hu
    exact exists_character_ne_one T V hV hW p hp hpm hR SemistableReduction.harmonicX hN ϖ hϖ _
      (threeGon_lines T hm)
      (fun P a => P.harmonicTate_of_crossingX1_threeGon T SemistableReduction.crossingX1 hm hc0
        hcπ hx hϖ a) hd hx

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

/-- A **good Tate presentation** of `W`: `W` is `y² + xy = x³ + π² b₄ x + π² b₆` with `π ∈ 𝔪`
nonzero, and either `b₆` is a unit (2-gon) or `c = b₆ − π² b₄² ≠ 0` divides `π` (3-gon with an
exact node at `r`). A property of `W` alone (`π` is internal). -/
def HasGoodTatePresentation (W : WeierstrassCurve K) (O : ValuationSubring K) : Prop :=
  ∃ π b₄ b₆ : O, IsTate W π b₄ b₆ ∧ π ≠ 0 ∧ π ∈ IsLocalRing.maximalIdeal O ∧
    (IsUnit b₆ ∨ (b₆ - π ^ 2 * b₄ ^ 2 ≠ 0 ∧ b₆ - π ^ 2 * b₄ ^ 2 ∣ π))

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [W.IsElliptic] [DecidableEq K] in
/-- **Normal-form Tate curves have good Tate presentations**: if `a₁ = 1`, `a₂ = a₃ = 0`,
`ϖ^m ∣ a₄` and `a₆ = ϖ^m ε` (`ε` a unit, `m ≥ 2`) — e.g. `E_q` in normal form with `v(q) = m` —
take `π = ϖ^⌊m/2⌋`: then `b₆ = ϖ^(m mod 2) ε`, a unit for `m` even, and `c = ϖ · unit` for `m`
odd. -/
lemma hasGoodTatePresentation_of_normalForm {ϖ : O} (hϖ : Irreducible ϖ) (ha₁ : W.a₁ = 1)
    (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0) {m : ℕ} (hm : 2 ≤ m) (u₄ : O)
    (ha₄ : W.a₄ = ((ϖ ^ m * u₄ : O) : K)) (ε : Oˣ) (ha₆ : W.a₆ = ((ϖ ^ m * ε : O) : K)) :
    HasGoodTatePresentation W O := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal O := hϖ.not_isUnit
  obtain ⟨k, r, hr, hmk⟩ : ∃ k r : ℕ, r < 2 ∧ m = 2 * k + r :=
    ⟨m / 2, m % 2, Nat.mod_lt _ two_pos, (Nat.div_add_mod m 2).symm⟩
  have hk : 1 ≤ k := by omega
  refine ⟨ϖ ^ k, ϖ ^ r * u₄, ϖ ^ r * ε, ⟨ha₁, ha₂, ha₃, ?_, ?_⟩, pow_ne_zero _ hϖ0,
    Ideal.pow_mem_of_mem _ hϖm k hk, ?_⟩
  · rw [ha₄, hmk]; push_cast; ring
  · rw [ha₆, hmk]; push_cast; ring
  · interval_cases r
    · left; simp
    · right
      have hc : ϖ ^ 1 * (ε : O) - (ϖ ^ k) ^ 2 * (ϖ ^ 1 * u₄) ^ 2 =
          ϖ * ((ε : O) - ϖ ^ (2 * k + 1) * u₄ ^ 2) := by ring
      have hunit : IsUnit ((ε : O) - ϖ ^ (2 * k + 1) * u₄ ^ 2) := by
        have hmem : ϖ ^ (2 * k + 1) * u₄ ^ 2 ∈ IsLocalRing.maximalIdeal O :=
          Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))
        by_contra h
        have h' := (IsLocalRing.mem_maximalIdeal _).2 h
        exact (IsLocalRing.mem_maximalIdeal _).1 (by simpa using Ideal.add_mem _ h' hmem)
          ε.isUnit
      rw [hc]
      refine ⟨mul_ne_zero hϖ0 hunit.ne_zero, ?_⟩
      obtain ⟨w, hw⟩ := hunit
      refine ⟨ϖ ^ (k - 1) * ↑w⁻¹, ?_⟩
      rw [← hw]
      calc ϖ ^ k = ϖ * ϖ ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
        _ = ϖ * ↑w * (ϖ ^ (k - 1) * ↑w⁻¹) := by
          rw [show ϖ * ↑w * (ϖ ^ (k - 1) * ↑w⁻¹) = ϖ * ϖ ^ (k - 1) * (↑w * ↑w⁻¹) by ring,
            Units.mul_inv, mul_one]

include A' in
/-- **Theorem B for IUT's orbicurves without `HarmonicTate` and `HarmonicX`**: for an elliptic
curve `W` with a
good Tate presentation (`HasGoodTatePresentation`, e.g. `E_q` in normal form with `v(q) ≥ 2`,
`hasGoodTatePresentation_of_normalForm`), `temperedPi1 [Y/A]` has an open normal subgroup with
infinite quotient. -/
theorem nondegenerate_of_crossing (hSCA : SemistableReduction.Statement.StrongComponentA.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite)
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (hgood : HasGoodTatePresentation W O) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) := by
  obtain ⟨π, b₄, b₆, hW, hπ, hπm, hb⟩ := hgood
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
    (ringKrullDim_geomOrbicurveRing_of_charZero hℓ hM) hN ϖ hϖ
    (TateNormal.squarefree_dpoly π b₄ b₆ h2 hΔ) hb (transcendental_data_x hW hπ hπm ℓ M)

end TateOrbicurve

end

end TemperedFundamentalGroups
