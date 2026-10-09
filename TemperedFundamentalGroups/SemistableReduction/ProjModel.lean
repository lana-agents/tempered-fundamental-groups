/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiModel

/-!
# The projective model of a finite family of functions

Blueprint §9.6 (W5), layer M9a (preparation of the scheme realization). A finite family
`f : ι → F` of nonzero functions defines a rational map `Spec F → ℙ^ι_R`; the closure of its image
is covered by the affine charts `A i = R[f j / f i : j]` (the standard opens `x_i ≠ 0`). As a
Zariski model (`projModel f`) it is proper and separated (`projModel_isProper`,
`projModel_isSeparated`) and of finite type. The lines `ℙ¹` (`f = (1, y)`) and their joins
(Segre families of products of the coordinates) are of this form; the scheme realization of
`projModel f` is the scheme-theoretic image of `Spec F → ℙ^ι_R` (a `ModelCode`), which is the
bridge M9 to the tempered group.
-/

namespace SemistableReduction

variable {F : Type*} [Field F] {R : Subring F} {ι : Type*} {f : ι → F}

/-- The standard affine chart `R[f j / f i : j]`. -/
def projChart (R : Subring F) (f : ι → F) (i : ι) : Subring F :=
  Subring.closure ((R : Set F) ∪ Set.range fun j ↦ f j / f i)

lemma div_mem_projChart (i j : ι) : f j / f i ∈ projChart R f i :=
  Subring.subset_closure (Or.inr ⟨j, rfl⟩)

lemma base_le_projChart (i : ι) : R ≤ projChart R f i :=
  fun _ hx ↦ Subring.subset_closure (Or.inl hx)

lemma projChart_le {A : Subring F} {i : ι} (hR : R ≤ A) (h : ∀ j, f j / f i ∈ A) :
    projChart R f i ≤ A :=
  Subring.closure_le.2 (Set.union_subset hR (Set.range_subset_iff.2 h))

namespace ZariskiModel

variable [Fintype ι]

open scoped Classical in
variable (R f) in
/-- The **projective model** of a finite family of functions: the charts `R[f j / f i : j]`. -/
noncomputable def projModel : ZariskiModel R where
  charts := Finset.univ.image (projChart R f)
  le_chart A hA := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    exact base_le_projChart i

lemma mem_projModel_charts {A : Subring F} :
    A ∈ (projModel R f).charts ↔ ∃ i, projChart R f i = A := by
  classical
  simp [projModel]

/-- The projective model of a family of nonzero functions is proper: a valuation subring contains
the chart of an index of maximal valuation. -/
theorem projModel_isProper [Nonempty ι] : (projModel R f).IsProper := by
  intro W hW
  obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image (fun i ↦ W.valuation (f i))
    Finset.univ_nonempty
  refine ⟨_, mem_projModel_charts.2 ⟨i, rfl⟩, projChart_le hW fun j ↦ ?_⟩
  change f j / f i ∈ W
  rw [← W.valuation_le_one_iff, map_div₀]
  rcases eq_or_ne (W.valuation (f i)) 0 with h0 | h0
  · rw [h0, div_zero]
    exact zero_le
  · exact (div_le_one₀ (zero_lt_iff.2 h0)).2 (hi j (Finset.mem_univ j))

/-- The projective model of a family of nonzero functions is separated. -/
theorem projModel_isSeparated (hf : ∀ i, f i ≠ 0) : (projModel R f).IsSeparated := by
  intro A hA B hB W hAW hBW
  obtain ⟨i, rfl⟩ := mem_projModel_charts.1 hA
  obtain ⟨k, rfl⟩ := mem_projModel_charts.1 hB
  refine projChart_le ((base_le_projChart i).trans le_localAt) fun j ↦ ?_
  have h₁ : f k / f i ∈ W := hAW (div_mem_projChart i k)
  have h₂ : f i / f k ∈ W := hBW (div_mem_projChart k i)
  have hne : f k / f i ≠ 0 := div_ne_zero (hf k) (hf i)
  have hunit : W.valuation (f k / f i) = 1 := by
    rw [← W.valuation_le_one_iff] at h₁ h₂
    refine le_antisymm h₁ ?_
    rw [← inv_div, map_inv₀] at h₂
    exact one_le_of_inv_le_one (by simpa using hne) h₂
  have : f j / f k = (f j / f i) * (f k / f i)⁻¹ := by
    field_simp [hf i, hf k]
  rw [this]
  exact Subring.mul_mem _ (le_localAt (div_mem_projChart i j))
    (inv_mem_localAt (div_mem_projChart i k) hunit)

theorem projModel_isFiniteType : (projModel R f).IsFiniteType := by
  classical
  intro A hA
  obtain ⟨i, rfl⟩ := mem_projModel_charts.1 hA
  exact ⟨Finset.univ.image fun j ↦ f j / f i, by simp [projChart]⟩

end ZariskiModel

end SemistableReduction
