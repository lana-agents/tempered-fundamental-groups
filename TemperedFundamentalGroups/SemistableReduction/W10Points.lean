/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Local
import TemperedFundamentalGroups.SemistableReduction.ChartLocalization

/-!
# Local domination from Zariski points

Blueprint §9.7a (W10 assembly). Local domination of the charts of a projective model (W10Local) in
terms of the Zariski points (local rings `localAt P W` of the charts at the centers of valuation
subrings): `locallyDominates_of_localAt` and, for a whole projective model,
`locallyDominates_of_points`.
-/

universe u

namespace SemistableReduction

open ZariskiModel

namespace ProjScheme

variable {F₁ : Type u} [Field F₁] {m : ℕ} {f : Fin (m + 1) → F₁} {R₁ : Subring F₁}
  {F₂ : Type u} [Field F₂] (φ : F₁ →+* F₂)

/-- **Local domination from local rings**: if `φ (R₁) ⊆ P` and every local ring `localAt P W` of
`P` contains the `φ`-images of the generators of some chart `R₁[f / f i]`, then `P` locally
dominates the charts. -/
theorem locallyDominates_of_localAt (P : Subring F₂) (hR : ∀ y ∈ R₁, φ y ∈ P)
    (h : ∀ W : ValuationSubring F₂, P ≤ W.toSubring → ∃ i, ∀ k, φ (f k / f i) ∈ localAt P W) :
    LocallyDominates R₁ φ P.subtype f := by
  refine locallyDominates_of_forall R₁ φ Subtype.val_injective
    (fun y hy ↦ ⟨⟨φ y, hR y hy⟩, rfl⟩) fun 𝔮 ↦ ?_
  obtain ⟨W, hPW, hcen⟩ := exists_centerIdeal_eq P 𝔮.asIdeal
  obtain ⟨i, hi⟩ := h W hPW
  refine ⟨i, fun k ↦ ?_⟩
  obtain ⟨s, hsP, hs1, hsd⟩ := mem_localAt.1 (hi k)
  refine ⟨⟨_, hsd⟩, ⟨s, hsP⟩, ?_, rfl⟩
  rw [← hcen, mem_centerIdeal_iff]
  exact hs1.not_lt

/-- **Local domination from Zariski points**: if every point of `projModel R₂ g` contains the
`φ`-image of some chart `R₁[f / f i]` (and `φ (R₁) ⊆ R₂`), then every chart of `projModel R₂ g`
locally dominates the charts of `f`. -/
theorem locallyDominates_of_points {n : ℕ} {g : Fin (n + 1) → F₂} {R₂ : Subring F₂}
    (hR : ∀ y ∈ R₁, φ y ∈ R₂)
    (h : ∀ Q ∈ (projModel R₂ g).points, ∃ i, ∀ y ∈ projChart R₁ f i, φ y ∈ Q) (l : Fin (n + 1)) :
    LocallyDominates R₁ φ (projChart R₂ g l).subtype f := by
  refine locallyDominates_of_localAt φ _ (fun y hy ↦ base_le_projChart l (hR y hy))
    fun W hW ↦ ?_
  obtain ⟨i, hi⟩ := h (localAt (projChart R₂ g l) W)
    ⟨_, mem_projModel_charts.2 ⟨l, rfl⟩, W, hW, rfl⟩
  exact ⟨i, fun k ↦ hi _ (div_mem_projChart i k)⟩

end ProjScheme

end SemistableReduction
