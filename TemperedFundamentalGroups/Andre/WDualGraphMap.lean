/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.DualGraphMap
import TemperedFundamentalGroups.Andre.WHarmonicWeight

/-!
# Morphisms of W-model levels are harmonic maps of dual graphs (Blueprint §11.3, G6.5)

For a morphism `m : X ⟶ Y` of the tempered category and W-model data `D`, `D'` on the levels of
`X` and `Y` (`WData`, e.g. the members of `galW`, `WData.nonempty_of_isW`), the model part
`D.e.inv ≫ m.ψ ≫ D'.e.hom : D.c' ⟶ D'.c'` is a **harmonic map of dual graphs**
(`WData.isHarmonicDualGraphMap`): components to components or points, nodes to nodes or smooth
points on one component, edge lifting along crossing walks, and x-harmonicity. These are the maps
of dual graphs underlying the transition maps of the stage groups (G6.4).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {x : R}

open SemistableReduction ModelCode

/-- **G6.5: the model part of a morphism of W-model levels is a harmonic map of dual graphs.** -/
theorem WData.isHarmonicDualGraphMap (ϖ : O) (hϖ : Irreducible ϖ) {X Y : TempObj O R A}
    (m : X ⟶ Y) (D : WData x X.Lv) (D' : WData x Y.Lv) :
    IsHarmonicDualGraphMap D.O' D'.O' D.ϖ' D'.ϖ' (D.ϖL ϖ) (D'.ϖL ϖ) D.xL D'.xL D.j₁ D'.j₁
      (D.e.inv ≫ m.ψ ≫ D'.e.hom) := by
  have hX := WData.isHarmonicX harmonicXS ϖ hϖ m D D'
  obtain ⟨H0', -⟩ := WData.isHarmonicX harmonicXS ϖ hϖ (𝟙 Y) D' D'
  set ψ' := D.e.inv ≫ m.ψ ≫ D'.e.hom
  have hZ : ∀ y ∈ Z D.c', ψ' y ∈ Z D'.c' := by
    intro y hy
    have h₁ : D.e.inv y ∈ specialFibre X.Lv.c.toSpec := by
      rw [D.mem_Z_iff]
      change (D.e.inv ≫ D.e.hom) y ∈ _
      rwa [Iso.inv_hom_id]
    have h₂ : m.ψ (D.e.inv y) ∈ specialFibre Y.Lv.c.toSpec :=
      mem_Z_of_comp_eq m.ψ m.ψ_toSpec h₁
    exact (D'.mem_Z_iff _).1 h₂
  have hcl : IsClosedMap ψ' := by
    have h₁ : IsClosedMap D.e.inv := (Scheme.homeoOfIso D.e.symm).isClosedMap
    have h₂ : IsClosedMap D'.e.hom := (Scheme.homeoOfIso D'.e).isClosedMap
    have h₃ := isClosedMap_of_comp_eq m.ψ m.ψ_toSpec
    change IsClosedMap (D'.e.hom ∘ m.ψ ∘ D.e.inv)
    exact h₂.comp (h₃.comp h₁)
  refine ⟨⟨hZ, fun v hv ↦ ?_, hX.2.2.2, ?_⟩, hX⟩
  · haveI := noetherianSpace_Z D'.c'
    exact contracted_or_mem_components ψ' hcl hZ
      (topologicalKrullDim_Z_le_one D'.hϖ' D'.semistable) hv
  · intro y' hy' w₁' hw₁' w₂' hw₂' hne hy₁ hy₂ v hv hψv
    obtain ⟨l', hl'⟩ := (H0' y' hy').1
    obtain ⟨w, hw0, hcross, hwk, -⟩ := hX.2.1 y' hy' w₁' hw₁' w₂' hw₂' hne hy₁ hy₂ v hv hψv l' hl'
    exact ⟨w, hw0, hcross, hwk⟩

end

end TemperedFundamentalGroups
