/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XHarmonic
import TemperedFundamentalGroups.SemistableReduction.MonomialUnique

/-!
# `Statement.CrossingX1`: crossing walks over a node of the target (Blueprint §10.3.8, §9.7)

Only a **definition** (targeted, owned by the Theorem B agent). The shared core of (X1) of
`Statement.HarmonicX` (without lengths) and of `HarmonicTate` (Blueprint §10.3.8): for a map
`ψ : c ⟶ c'` of models compatible with the generic points, where the source `c` is a split
unfolded W-model without loops and the target `c'` is **any** projective model, and a
point `y'` of `c'` on two components `w₁' ≠ w₂'` at which the germs of `c'` form a node germ
(`NodeGerm`: `u v = ϖ'ⁿ` exactly, with `u, v` non-units of the germ ring), the generic point
`j'` being dominant, every component of `c` over `w₁'` starts a walk crossing `y'`
(special points over `y'`, inner components contracted to `y'`) to a component over `w₂'`.

The x-line `x ∈ L₁` is only a hypothesis on the source (it need not come from `L₂`); the target has
no x-line (it only enters the lengths of (X1) in `HarmonicX`).

Both the dominance of `j'` and the non-unit condition are necessary (counterexamples, Blueprint
§10.3.8: a target `c' = c ∪ E` with an extra special-fibre line `E` not dominated by `j'`; a
pinched model, where `NodeGerm` with a unit `u` says nothing).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

/-- **Crossing walks over node germs** (targeted, Blueprint §10.3.8). -/
def Statement.CrossingX1 : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    (O₁ : ValuationSubring K₁) (O₂ : ValuationSubring K₂)
    (h₁ : O₁.comap (algebraMap K K₁) = O) (h₂ : O₂.comap (algebraMap K K₂) = O)
    [IsDiscreteValuationRing O₁] [IsDiscreteValuationRing O₂] (ϖ₁ : O₁) (ϖ₂ : O₂)
    (_ : Irreducible ϖ₁) (_ : Irreducible ϖ₂)
    (L₁ L₂ : Type u) [Field L₁] [Field L₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
    [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
    [IsScalarTower K L₂ L₁]
    [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂] [IsScalarTower O₂ K₂ L₂] (x : L₁)
    (c : TemperedFundamentalGroups.ModelCode O₁) (c' : TemperedFundamentalGroups.ModelCode O₂)
    (ψ : c.scheme ⟶ c'.scheme)
    (j : Spec (CommRingCat.of L₁) ⟶ c.scheme) (j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme),
    ModelCode.IsUnfolded O₁ x c j →
    j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j' →
    ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy))) →
    ModelCode.IsSplit ϖ₁ c → ModelCode.NoLoops c →
    Dense (Set.range j'.base) →
    ∀ (y' : c'.scheme) (w₁' w₂' : Set c'.scheme), w₁' ∈ ModelCode.components c' →
      w₂' ∈ ModelCode.components c' → w₁' ≠ w₂' → y' ∈ w₁' → y' ∈ w₂' →
      (∃ (P : Subring L₂) (u v : L₂) (n : ℕ), (P : Set L₂) = ModelCode.germs c' j' y' ∧
        _root_.SemistableReduction.NodeGerm O₂ ϖ₂ P u v n ∧
        (∀ w ∈ P, u * w ≠ 1) ∧ (∀ w ∈ P, v * w ≠ 1)) →
      ∀ v ∈ ModelCode.components c, ψ '' v = w₁' →
        ∃ w : ModelCode.Walk c, w.v 0 = v ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂'

/-- **`CrossingX1` with split nodes only** (`HasSplitNodes` instead of `IsSplit`; the geometric
irreducibility of the components is not used). -/
def Statement.CrossingX1S : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    (O₁ : ValuationSubring K₁) (O₂ : ValuationSubring K₂)
    (h₁ : O₁.comap (algebraMap K K₁) = O) (h₂ : O₂.comap (algebraMap K K₂) = O)
    [IsDiscreteValuationRing O₁] [IsDiscreteValuationRing O₂] (ϖ₁ : O₁) (ϖ₂ : O₂)
    (_ : Irreducible ϖ₁) (_ : Irreducible ϖ₂)
    (L₁ L₂ : Type u) [Field L₁] [Field L₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
    [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
    [IsScalarTower K L₂ L₁]
    [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂] [IsScalarTower O₂ K₂ L₂] (x : L₁)
    (c : TemperedFundamentalGroups.ModelCode O₁) (c' : TemperedFundamentalGroups.ModelCode O₂)
    (ψ : c.scheme ⟶ c'.scheme)
    (j : Spec (CommRingCat.of L₁) ⟶ c.scheme) (j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme),
    ModelCode.IsUnfolded O₁ x c j →
    j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j' →
    ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy))) →
    ModelCode.HasSplitNodes ϖ₁ c → ModelCode.NoLoops c →
    Dense (Set.range j'.base) →
    ∀ (y' : c'.scheme) (w₁' w₂' : Set c'.scheme), w₁' ∈ ModelCode.components c' →
      w₂' ∈ ModelCode.components c' → w₁' ≠ w₂' → y' ∈ w₁' → y' ∈ w₂' →
      (∃ (P : Subring L₂) (u v : L₂) (n : ℕ), (P : Set L₂) = ModelCode.germs c' j' y' ∧
        _root_.SemistableReduction.NodeGerm O₂ ϖ₂ P u v n ∧
        (∀ w ∈ P, u * w ≠ 1) ∧ (∀ w ∈ P, v * w ≠ 1)) →
      ∀ v ∈ ModelCode.components c, ψ '' v = w₁' →
        ∃ w : ModelCode.Walk c, w.v 0 = v ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂'

end TemperedFundamentalGroups.SemistableReduction
