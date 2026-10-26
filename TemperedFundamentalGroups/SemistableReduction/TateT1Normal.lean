/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeNormal
import TemperedFundamentalGroups.SemistableReduction.NormalLocalCriterion

/-!
# The chart `u ≠ 0` of the Tate model is integrally closed (MR12, Tate chart)

Let `O` be a discrete valuation ring with uniformizer `ϖ`, `m ≥ 1`, `ε ∈ Oˣ`, `π = ε ϖᵐ`, and
`T1 = O[h'][w]/(G₁)` the chart `u ≠ 0` of the Tate model (`TateTwoChart.T1`), with
`κ (t² − b₆) = 1`. Assume `3 ≠ 0` in `O` and `E = tateE π b₄ b₆ ≠ 0`.

* `algT1NR`, `isScalarTower_NR`, `isLocalization_NR`: via `toNode`, the quadratic node chart
  `NR` is the localization `T1[1/D]`, `D = 1 + b₄ w²` (transport of `chartEquiv`).
* **`isIntegrallyClosed_T1`**: if `T1` is a domain and `ϖ` is prime in the local ring of `T1`
  at every maximal ideal containing `ϖ` but not `w`, then `T1` is integrally closed.

## Proof

Local criterion (`NormalLocal.isIntegrallyClosed_of_cover`) at a maximal ideal `P`:
* `ϖ ∉ P`: `T1[1/ϖ]` is a Dedekind domain (`TateTwoChart.isDedekindDomain_away_T1_of_dvr`);
* `ϖ ∈ P`, `w ∉ P`: again `T1[1/ϖ]`, and `ϖ` is prime in `T1_P` (hypothesis);
* `w ∈ P`: then `D ∉ P` and `T1[1/D] ≅ NR` is integrally closed
  (`TateTwoChartNode.isIntegrallyClosed_NR`).
-/

universe u

open TemperedFundamentalGroups

namespace SemistableReduction

open TateTwoChart

namespace TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] {ϖ : O} {m : ℕ} {b₄ b₆ ε εi π t κ : O}

/-- The `T1`-algebra structure on the node chart given by `toNode` (`h' ↦ S − t u`,
`w ↦ u`). -/
abbrev algT1NR (b₄ : O) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) :
    Algebra (T1 π b₄ t κ) (NR b₄ b₆ ϖ m ε) :=
  (toNode b₄ hκ hπ).toRingHom.toAlgebra

lemma isScalarTower_NR (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) :
    letI := algT1NR b₄ hκ hπ
    IsScalarTower O (T1 π b₄ t κ) (NR b₄ b₆ ϖ m ε) :=
  letI := algT1NR b₄ hκ hπ
  IsScalarTower.of_algebraMap_eq fun o ↦ ((toNode b₄ hκ hπ).commutes o).symm

/-- **The node chart is the localization `T1[1/D]`** for the `T1`-algebra structure
`algT1NR`. -/
lemma isLocalization_NR (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) :
    letI := algT1NR b₄ hκ hπ
    IsLocalization.Away (DT π b₄ t κ) (NR b₄ b₆ ϖ m ε) :=
  letI := algT1NR b₄ hκ hπ
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (DT π b₄ t κ))
    (AlgEquiv.ofRingEquiv (f := (chartEquiv b₄ hκ hπ hε).toRingEquiv)
      fun a ↦ chartEquiv_algebraMap hκ hπ hε a)

/-- **The chart `u ≠ 0` of the Tate model is integrally closed**: `O` a discrete valuation ring
with uniformizer `ϖ`, `m ≥ 1`, `ε` a unit, `3 ≠ 0`, `E = tateE (ε ϖᵐ) b₄ b₆ ≠ 0`, `T1` a domain,
and `ϖ` prime in `T1_P` for every maximal `P` containing `ϖ` but not `w`. -/
theorem isIntegrallyClosed_T1 [IsDomain O] [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ)
    (hm : 1 ≤ m) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0) (hE : TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) [IsDomain (T1 (ε * ϖ ^ m) b₄ t κ)]
    (hprime : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal],
      algebraMap O _ ϖ ∈ P → w1 (ε * ϖ ^ m) b₄ t κ ∉ P →
        Prime (algebraMap O (Localization.AtPrime P) ϖ)) :
    IsIntegrallyClosed (T1 (ε * ϖ ^ m) b₄ t κ) := by
  have hεu : IsUnit ε := .of_mul_eq_one_right εi hε
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hπ0 : ε * ϖ ^ m ≠ 0 := mul_ne_zero hεu.ne_zero (pow_ne_zero _ hϖ0)
  haveI := isDedekindDomain_away_T1_of_dvr (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) hϖ0
    hϖ.not_isUnit hκ h3 hπ0 hE
  haveI : IsIntegrallyClosed (NR b₄ b₆ ϖ m ε) := isIntegrallyClosed_NR hϖ hm hεu h3 hE
  haveI : IsIntegrallyClosed (T1D (ε * ϖ ^ m) b₄ t κ) :=
    IsIntegrallyClosed.of_equiv (chartEquiv b₄ hκ rfl hε).symm.toRingEquiv
  refine NormalLocal.isIntegrallyClosed_of_cover fun P hP ↦ ?_
  by_cases hw : w1 (ε * ϖ ^ m) b₄ t κ ∈ P
  · have hD : DT (ε * ϖ ^ m) b₄ t κ ∉ P := by
      intro hD
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have : algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) b₄ * w1 (ε * ϖ ^ m) b₄ t κ ^ 2 ∈ P :=
        P.mul_mem_left _ (P.pow_mem_of_mem hw 2 two_pos)
      have h1 := P.sub_mem hD this
      rwa [DT, add_sub_cancel_right] at h1
    exact ⟨_, fun h0 ↦ hD (by rw [h0]; exact P.zero_mem), inferInstance, Or.inl hD⟩
  · by_cases hϖP : algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) ϖ ∈ P
    · have hp := hprime P hϖP hw
      rw [IsScalarTower.algebraMap_apply O (T1 (ε * ϖ ^ m) b₄ t κ)
        (Localization.AtPrime P)] at hp
      exact ⟨_, fun h0 ↦ hp.ne_zero (by rw [h0, map_zero]), inferInstance, Or.inr hp⟩
    · exact ⟨_, fun h0 ↦ hϖP (by rw [h0]; exact P.zero_mem), inferInstance, Or.inl hϖP⟩

end

end TateTwoChartNode

end SemistableReduction
