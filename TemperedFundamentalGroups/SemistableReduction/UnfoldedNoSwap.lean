/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.BranchSwap
import TemperedFundamentalGroups.SemistableReduction.UnfoldedNodeMain
import TemperedFundamentalGroups.SemistableReduction.CrossingZero
import TemperedFundamentalGroups.SemistableReduction.WModelCentre
import TemperedFundamentalGroups.SemistableReduction.CentreMap

/-!
# Endomorphisms over the x-line do not swap the branches of a node (Blueprint §12.7, M3)

Let `c` be an unfolded split W-model without loops (over a discrete valuation ring `O'` of `K'`,
function field `L`, x-line `x ∈ L`) and `y` a node of `c`. Its two branches `v₁ ≠ v₂` (the only
components through `y`, `two_components`) restrict to Gauss points of the x-line with the same
centre and different radii (`exists_unfoldedNodeGerm`). A morphism `τ : c ⟶ c` compatible with
the generic point through a field endomorphism `σ` of `L` (`j ≫ τ = Spec σ ≫ j`) which fixes `x`
and a subfield `K₀` over which `K'` is algebraic cannot map `v₁` onto `v₂`: the centre
valuations would satisfy `σ⁻¹(W₁) = W₂` (`IsCentre.comap`, `centreDetermines_gp`), which is
impossible by `SemistableReduction.not_branch_swap`.

* **`exists_branches_not_swapped`**.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}

/-- **M3 at a node of an unfolded W-model**: the two components `v₁ ≠ v₂` through a node `y`
are the only ones, and no endomorphism over the x-line maps `v₁` onto `v₂`. -/
theorem exists_branches_not_swapped (hU : IsUnfolded O x c j) {ϖ : O} (hϖ : Irreducible ϖ)
    (hsplit : HasSplitNodes ϖ c) (hloops : NoLoops c) {K₀ : Type*} [Field K₀] [Algebra K₀ K]
    [Algebra K₀ L] [IsScalarTower K₀ K L] [Algebra.IsAlgebraic K₀ K] {ϖ₀ : K₀} {e₀ : ℕ}
    {η : Oˣ} (he₀ : 1 ≤ e₀) (hϖ₀ : algebraMap K₀ K ϖ₀ = (η : K) * (ϖ : K) ^ e₀)
    {y : c.scheme} (hy : IsNodePt c y) :
    ∃ v₁ ∈ components c, ∃ v₂ ∈ components c, v₁ ≠ v₂ ∧ y ∈ v₁ ∧ y ∈ v₂ ∧
      (∀ w ∈ components c, y ∈ w → w = v₁ ∨ w = v₂) ∧
      ∀ (τ : c.scheme ⟶ c.scheme) (σ : L →+* L),
        j ≫ τ = Spec.map (CommRingCat.ofHom σ) ≫ j → σ x = x →
        (∀ k : K₀, σ (algebraMap K₀ L k) = algebraMap K₀ L k) → τ '' v₁ ≠ v₂ := by
  have hW := hU.isWModel
  obtain ⟨P, u, v, n, a, β, e, α, ε, v₁, v₂, hv₁, hv₂, H, -, -, hy₁, hy₂, -⟩ :=
    exists_unfoldedNodeGerm hU hϖ hsplit hloops hy
  have h₁ := H.germ.comap_eq hϖ H.isMonomialPt₁
  have h₂ := H.germ.comap_eq hϖ H.isMonomialPt₂
  have hN : 1 ≤ e * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := H.one_le_e; omega)
    (by have := H.one_le_n; omega))
  -- no `σ` carries `W₂` onto `W₁`
  have key : ∀ σ : L →+* L, σ x = x → (∀ k : K₀, σ (algebraMap K₀ L k) = algebraMap K₀ L k) →
      (∀ g, g ∈ Wc hW hv₂ ↔ σ g ∈ Wc hW hv₁) → False := fun σ hσx hσK hσ ↦
    _root_.SemistableReduction.not_branch_swap hϖ h₁ h₂ H.β_ne hN H.coord H.residue₁
      H.residue₂.1 he₀ hϖ₀ σ hσK hσx hσ
  have hne : v₁ ≠ v₂ := by
    rintro rfl
    exact key (RingHom.id L) rfl (fun _ ↦ rfl) fun g ↦ Iff.rfl
  refine ⟨v₁, hv₁, v₂, hv₂, hne, hy₁, hy₂, fun w hw hyw ↦ ?_, fun τ σ hj hσx hσK himg ↦ ?_⟩
  · rcases two_components hW hϖ hsplit hloops hy hv₁ hv₂ hw hy₁ hy₂ hyw with h | h | h
    · exact absurd h hne
    · exact .inl h.symm
    · exact .inr h.symm
  · -- `τ` maps the generic point of `v₁` to that of `v₂`
    have hgen : τ (gp hv₁) = gp hv₂ := by
      have h₁' : IsGenericPoint (gp hv₁) v₁ := closure_gp hv₁
      have h₂' : IsGenericPoint (gp hv₂) v₂ := closure_gp hv₂
      have := h₁'.image τ.continuous
      rw [himg, (isClosed_of_mem_components hv₂).closure_eq] at this
      exact this.eq h₂'
    letI : Algebra L L := σ.toAlgebra
    have hc := IsCentre.comap j j τ hj (Wc_spec hW hv₁)
    rw [hgen] at hc
    have heq := centreDetermines_gp hW hϖ hv₂ _ _ hc (Wc_spec hW hv₂)
    exact key σ hσx hσK fun g ↦ by rw [← heq]; rfl

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
