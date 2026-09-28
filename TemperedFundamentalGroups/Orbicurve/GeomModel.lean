/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import EllipticCurves.Torsion.XSupport
import TemperedFundamentalGroups.Orbicurve.Exact

/-!
# The coordinate ring of `E ∖ (E[ℓ] + M)` is a localization of `k[E]`

IUT's removed set `geomRemovedSet W ℓ M = E[ℓ] + M ⊆ E(k̄)` is symmetric and Galois stable
(`isGaloisStable_geomRemovedSet`), and finite when `M` is finite and `E[ℓ]` is finite over `k̄`
(`finite_geomRemovedSet`), e.g. for `ℓ ≥ 1` in characteristic `0`
(`finite_geomRemovedSet_of_charZero`) or for `char k ∤ 2ℓ`
(`finite_geomRemovedSet_of_not_dvd_charP`); finiteness of `E[ℓ]` is
`WeierstrassCurve.Affine.finite_torsion_of_charZero` resp.
`WeierstrassCurve.Affine.finite_torsion_of_not_dvd_charP` from `lana-agents/elliptic-curves`.
For `M ≤ E(k)[ℓ]` (as in IUT) it is `E(k̄)[ℓ]` (`geomRemovedSet_eq_torsion`).

In that case `E[ℓ] + M ∖ {0}` is the zero set of a function `Ψ(x)` of `x`, and the coordinate
ring `geomOrbicurveRing W ℓ M` of `E ∖ (E[ℓ] + M)` is the localization `k[E][Ψ(x)⁻¹]`
(`exists_isLocalization_geomOrbicurveRing`): its spectrum is the open subscheme
`D(Ψ(x)) = E ∖ (E[ℓ] + M)` of `E`.
-/

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] [DecidableEq k] {W : WeierstrassCurve k} {ℓ : ℕ}
  {M : AddSubgroup W.toAffine.Point}

/-! ### Galois stability and finiteness of `E[ℓ] + M` -/

lemma map_mem_removedSetIn {K L : Type*} [Field K] [DecidableEq K] [Algebra k K] [Field L]
    [DecidableEq L] [Algebra k L] (φ : K →ₐ[k] L) {P : (W.toAffine⁄K).Point}
    (hP : P ∈ removedSetIn W K ℓ M) : Point.map φ P ∈ removedSetIn W L ℓ M := by
  obtain ⟨m, hm, h⟩ := hP
  refine ⟨m, hm, ?_⟩
  rw [← map_bc φ m, ← map_sub, ← map_nsmul, h, map_zero]

lemma isGaloisStable_geomRemovedSet : IsGaloisStable W (geomRemovedSet W ℓ M) :=
  fun _ _ hP => map_mem_removedSetIn _ hP

lemma removedSetIn_subset {K : Type*} [Field K] [DecidableEq K] [Algebra k K] :
    removedSetIn W K ℓ M ⊆
      ⋃ m ∈ (M : Set W.toAffine.Point), (· + bc W K m) '' ((W.toAffine⁄K).torsion ℓ) := by
  rintro P ⟨m, hm, h⟩
  exact Set.mem_biUnion hm ⟨P - bc W K m, mem_torsion_iff.mpr h, sub_add_cancel P _⟩

/-- If `M ≤ E(k)[ℓ]` (as in IUT), then `E[ℓ] + M = E[ℓ]`. -/
lemma removedSetIn_eq_torsion {K : Type*} [Field K] [DecidableEq K] [Algebra k K]
    (hM : ∀ m ∈ M, ℓ • m = 0) :
    removedSetIn W K ℓ M = ((W.toAffine⁄K).torsion ℓ : Set (W.toAffine⁄K).Point) := by
  ext P
  rw [SetLike.mem_coe, mem_torsion_iff]
  constructor
  · rintro ⟨m, hm, h⟩
    rwa [smul_sub, ← map_nsmul, hM m hm, map_zero, sub_zero] at h
  · intro h
    exact ⟨0, M.zero_mem, by rw [map_zero, sub_zero]; exact h⟩

/-- If `M ≤ E(k)[ℓ]` (as in IUT), the geometric removed set is `E(k̄)[ℓ]`. -/
lemma geomRemovedSet_eq_torsion (hM : ∀ m ∈ M, ℓ • m = 0) :
    geomRemovedSet W ℓ M = ((W.toAffine⁄(AlgebraicClosure k)).torsion ℓ :
      Set (W.toAffine⁄(AlgebraicClosure k)).Point) :=
  removedSetIn_eq_torsion hM

/-- `E[ℓ] + M ⊆ E(K)` is finite if `M` and `E(K)[ℓ]` are. -/
lemma finite_removedSetIn {K : Type*} [Field K] [DecidableEq K] [Algebra k K]
    (hM : (M : Set W.toAffine.Point).Finite)
    (hℓ : ((W.toAffine⁄K).torsion ℓ : Set (W.toAffine⁄K).Point).Finite) :
    (removedSetIn W K ℓ M).Finite :=
  (hM.biUnion fun _ _ => hℓ.image _).subset removedSetIn_subset

/-- `E[ℓ] + M ⊆ E(k̄)` is finite if `M` and `E(k̄)[ℓ]` are. -/
lemma finite_geomRemovedSet (hM : (M : Set W.toAffine.Point).Finite)
    (hℓ : ((W.toAffine⁄(AlgebraicClosure k)).torsion ℓ :
      Set (W.toAffine⁄(AlgebraicClosure k)).Point).Finite) :
    (geomRemovedSet W ℓ M).Finite :=
  finite_removedSetIn hM hℓ

/-- `E[ℓ] + M ⊆ E(k̄)` is finite for `ℓ ≥ 1` and finite `M` in characteristic `0`. -/
theorem finite_geomRemovedSet_of_charZero [CharZero k] (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) : (geomRemovedSet W ℓ M).Finite :=
  finite_geomRemovedSet hM (Set.finite_coe_iff.mp (finite_torsion_of_charZero hℓ))

/-- `E[ℓ] + M ⊆ E(k̄)` is finite for finite `M` if the characteristic `p` of `k` is not `2` and
does not divide `ℓ`. -/
theorem finite_geomRemovedSet_of_not_dvd_charP (h2 : (2 : k) ≠ 0) {p : ℕ} [CharP k p]
    (hℓ : ¬ p ∣ ℓ) (hM : (M : Set W.toAffine.Point).Finite) : (geomRemovedSet W ℓ M).Finite := by
  have h2' : (2 : AlgebraicClosure k) ≠ 0 := by
    rw [← map_ofNat (algebraMap k (AlgebraicClosure k)) 2]
    exact (_root_.map_ne_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).mpr h2
  exact finite_geomRemovedSet hM (Set.finite_coe_iff.mp (finite_torsion_of_not_dvd_charP h2' hℓ))

/-! ### Exactness -/

omit [DecidableEq k] in
lemma injective_algebraMap_polynomial :
    Function.Injective (algebraMap k[X] W.toAffine.CoordinateRing) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero (by rw [W.toAffine.degree_polynomial]; decide)

variable [W.IsElliptic]

/-- **Exactness.** If `E[ℓ] + M ⊆ E(k̄)` is finite, then it is, away from `0`, the zero set of a
function `Ψ(x)` of `x`, and the coordinate ring of `E ∖ (E[ℓ] + M)` is the localization
`k[E][Ψ(x)⁻¹]`. -/
theorem exists_isLocalization_geomOrbicurveRing (hfin : (geomRemovedSet W ℓ M).Finite) :
    ∃ Ψ : k[X], Ψ ≠ 0 ∧
      zeroSet W (algebraMap k[X] W.toAffine.CoordinateRing Ψ) = geomRemovedSet W ℓ M \ {0} ∧
      IsLocalization.Away (algebraMap k[X] W.toAffine.CoordinateRing Ψ)
        (geomOrbicurveRing W ℓ M) := by
  obtain ⟨Ψ, hΨ, hz⟩ := exists_polynomial_zeroSet hfin (fun _ => neg_mem_removedSetIn)
    isGaloisStable_geomRemovedSet
  exact ⟨Ψ, hΨ, hz, isLocalization_away_ringAway
    ((_root_.map_ne_zero_iff _ injective_algebraMap_polynomial).mpr hΨ) hz⟩

/-- **Exactness in characteristic `0`.** For `ℓ ≥ 1` and finite `M`, the coordinate ring of
`E ∖ (E[ℓ] + M)` is a localization `k[E][Ψ(x)⁻¹]`, `E[ℓ] + M ∖ {0}` being the zero set of
`Ψ(x)`. -/
theorem exists_isLocalization_geomOrbicurveRing_of_charZero [CharZero k] (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) :
    ∃ Ψ : k[X], Ψ ≠ 0 ∧
      zeroSet W (algebraMap k[X] W.toAffine.CoordinateRing Ψ) = geomRemovedSet W ℓ M \ {0} ∧
      IsLocalization.Away (algebraMap k[X] W.toAffine.CoordinateRing Ψ)
        (geomOrbicurveRing W ℓ M) :=
  exists_isLocalization_geomOrbicurveRing (finite_geomRemovedSet_of_charZero hℓ hM)

/-- **Exactness in characteristic `p ∤ 2ℓ`.** For finite `M`, the coordinate ring of
`E ∖ (E[ℓ] + M)` is a localization `k[E][Ψ(x)⁻¹]`, `E[ℓ] + M ∖ {0}` being the zero set of
`Ψ(x)`. -/
theorem exists_isLocalization_geomOrbicurveRing_of_not_dvd_charP (h2 : (2 : k) ≠ 0) {p : ℕ}
    [CharP k p] (hℓ : ¬ p ∣ ℓ) (hM : (M : Set W.toAffine.Point).Finite) :
    ∃ Ψ : k[X], Ψ ≠ 0 ∧
      zeroSet W (algebraMap k[X] W.toAffine.CoordinateRing Ψ) = geomRemovedSet W ℓ M \ {0} ∧
      IsLocalization.Away (algebraMap k[X] W.toAffine.CoordinateRing Ψ)
        (geomOrbicurveRing W ℓ M) :=
  exists_isLocalization_geomOrbicurveRing (finite_geomRemovedSet_of_not_dvd_charP h2 hℓ hM)

end

end TemperedFundamentalGroups.Orbicurve
