/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Points
import TemperedFundamentalGroups.SemistableReduction.SegreModel
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization

/-!
# The root chart

Blueprint §9.7a (W10 assembly, `hroot`). Let `D ⊆ F'` contain every element of `F'` integral over
`E[X]` (the image of `E ⊗_K B` in a component, `W10Fields.mem_D_of_isIntegral`). The chart
`O[(X - a i)/c i : i]` of the tree of lines (the Segre chart at `σ = false`) consists of
polynomials, so its normalization in `F'` lies in `D` (`normChart_le_of_polynomial`). If this
normalization is a chart of `projModel g`, then `D` locally dominates the charts of `g`
(`locallyDominates_root`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel ProjScheme

variable {E : Type*} [Field E] {F' : Type*} [Field F'] [Algebra E[X] F'] [Algebra (RatFunc E) F']
  [IsScalarTower E[X] (RatFunc E) F']

/-- The normalization of a chart consisting of polynomials is integral over `E[X]`. -/
lemma isIntegral_of_mem_normChart {A : Subring (RatFunc E)}
    (hA : ∀ t ∈ A, t ∈ (algebraMap E[X] (RatFunc E)).range) {z : F'}
    (hz : z ∈ normChart F' A) : IsIntegral E[X] z := by
  set I := integralClosure E[X] F'
  have hle : A.map (algebraMap (RatFunc E) F') ≤ I.toSubring := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨p, rfl⟩ := hA t ht
    change IsIntegral E[X] (algebraMap (RatFunc E) F' (algebraMap E[X] (RatFunc E) p))
    rw [← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hzI : IsIntegral I z := by
    have := IsIntegral.map_of_comp_eq (Subring.inclusion hle) (RingHom.id F')
      (RingHom.ext fun _ ↦ rfl) hz
    exact this
  exact isIntegral_trans z hzI

/-- The Segre chart at `σ = false` of polynomial coordinates consists of polynomials. -/
lemma mem_range_of_mem_segreChart {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation E Γ₀} {ι : Type*} {y : ι → RatFunc E}
    (hy : ∀ i, y i ∈ (algebraMap E[X] (RatFunc E)).range) {t : RatFunc E}
    (ht : t ∈ segreChart v y fun _ ↦ false) : t ∈ (algebraMap E[X] (RatFunc E)).range := by
  revert t
  change segreChart v y (fun _ ↦ false) ≤ (algebraMap E[X] (RatFunc E)).range
  refine sup_le ?_ (iSup_le fun i ↦ ?_)
  · rintro _ ⟨o, -, rfl⟩
    exact ⟨Polynomial.C o, RatFunc.algebraMap_C o⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine Subring.closure_le.2 (Set.union_subset ?_ (Set.singleton_subset_iff.2 (hy i)))
    rintro _ ⟨o, -, rfl⟩
    exact ⟨Polynomial.C o, RatFunc.algebraMap_C o⟩

/-- **`hroot`**: if the normalization of a polynomial chart is a chart of `projModel g` and `D`
contains everything integral over `E[X]` (and the base ring), then `D` locally dominates the
charts of `g`. -/
theorem locallyDominates_root {n : ℕ} {g : Fin (n + 1) → F'} {R : Subring F'} (D : Subring F')
    (hD : ∀ z : F', IsIntegral E[X] z → z ∈ D) (hRD : R ≤ D) {A : Subring (RatFunc E)}
    (hA : ∀ t ∈ A, t ∈ (algebraMap E[X] (RatFunc E)).range) {l : Fin (n + 1)}
    (hl : projChart R g l = normChart F' A) :
    LocallyDominates R (RingHom.id F') D.subtype g := by
  refine locallyDominates_of_localAt (RingHom.id F') D (fun y hy ↦ hRD hy) fun W _ ↦ ⟨l, ?_⟩
  intro k
  refine le_localAt (hD _ (isIntegral_of_mem_normChart hA ?_))
  rw [← hl]
  exact div_mem_projChart l k

end SemistableReduction
