/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChangeComp
import TemperedFundamentalGroups.Tempered.CoverImage
import TemperedFundamentalGroups.Tempered.OrbifoldCover

/-!
# Mixed covers: finite étale covers of orbifold covers (Blueprint §11, F7′ mixed cases)

By F4 (`temperedPi1Map_comp`), injectivity, the open embedding property and finiteness of the
index of the image of `temperedPi1Map` are stable under composition of maps of orbifolds
(`temperedPi1Map_comp_injective`, `isOpenEmbedding_temperedPi1Map_comp`,
`finiteIndex_range_temperedPi1Map_comp`, `range_temperedPi1Map_comp`).

Combining F7 (finite étale covers, scheme case) and F7′ (orbifold covers) we obtain the mixed
case `Spec R' → Spec R → [Spec R / A]`: for an orbifold cover `μ₁ : OrbMap R A R A₁` with `A₁`
trivial (`Y → [Y/A]`) and a finite étale cover `μ₂ : OrbMap R A₁ R' A₂` (`A₂` trivial),
`temperedPi1 O R' A₂` is an open subgroup of finite index of `temperedPi1 O R A`
(`temperedPi1Map_injective_mixed`, `isOpenEmbedding_temperedPi1Map_mixed`,
`finiteIndex_range_temperedPi1Map_mixed`). Since F7 needs trivial groups on both sides and an
orbifold cover with faithful `A''` over a trivial group is an isomorphism of groups, this is the
only composite of F7 and F7′ beyond those which are themselves orbifold covers (F7′ directly).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

section Comp

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R']
  {R'' : Type u} [CommRing R''] [Algebra K R''] [Algebra R' R''] [IsScalarTower K R' R'']
  [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower K R R'']
  {A'' : Type u} [Group A''] [MulSemiringAction A'' R'']
  (μ₁ : OrbMap R A R' A') (μ₂ : OrbMap R' A' R'' A'')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  [Algebra R'' Ω] [IsScalarTower K R'' Ω] [IsScalarTower R' R'' Ω] [IsScalarTower R R'' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- `temperedPi1Map` of a composite, as an equality of monoid homomorphisms (F4). -/
theorem temperedPi1Map_comp_eq :
    temperedPi1Map (O := O) (μ₁.comp μ₂) V hV =
      (temperedPi1Map μ₁ V hV).comp (temperedPi1Map μ₂ V hV) :=
  MonoidHom.ext fun γ => temperedPi1Map_comp μ₁ μ₂ V hV γ

theorem temperedPi1Map_comp_injective
    (h₁ : Function.Injective (temperedPi1Map (O := O) μ₁ V hV))
    (h₂ : Function.Injective (temperedPi1Map (O := O) μ₂ V hV)) :
    Function.Injective (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV) := by
  rw [temperedPi1Map_comp_eq, MonoidHom.coe_comp]
  exact h₁.comp h₂

theorem isOpenEmbedding_temperedPi1Map_comp
    (h₁ : Topology.IsOpenEmbedding (temperedPi1Map (O := O) μ₁ V hV))
    (h₂ : Topology.IsOpenEmbedding (temperedPi1Map (O := O) μ₂ V hV)) :
    Topology.IsOpenEmbedding (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV) := by
  rw [temperedPi1Map_comp_eq, MonoidHom.coe_comp]
  exact h₁.comp h₂

/-- The image of a composite is the image under `temperedPi1Map μ₁` of the image of
`temperedPi1Map μ₂`. -/
theorem range_temperedPi1Map_comp :
    (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV).range =
      (temperedPi1Map μ₂ V hV).range.map (temperedPi1Map μ₁ V hV) := by
  rw [temperedPi1Map_comp_eq, MonoidHom.range_comp]

/-- The index is multiplicative along composites with an injective first factor. -/
theorem index_range_temperedPi1Map_comp
    (h₁ : Function.Injective (temperedPi1Map (O := O) μ₁ V hV)) :
    (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV).range.index =
      (temperedPi1Map (O := O) μ₂ V hV).range.index *
        (temperedPi1Map (O := O) μ₁ V hV).range.index := by
  rw [range_temperedPi1Map_comp, Subgroup.index_map_of_injective _ h₁]

theorem finiteIndex_range_temperedPi1Map_comp
    (h₁ : Function.Injective (temperedPi1Map (O := O) μ₁ V hV))
    [(temperedPi1Map (O := O) μ₁ V hV).range.FiniteIndex]
    [(temperedPi1Map (O := O) μ₂ V hV).range.FiniteIndex] :
    (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV).range.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, index_range_temperedPi1Map_comp μ₁ μ₂ V hV h₁]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

end Comp

section Mixed

/-! ### `Spec R' → Spec R → [Spec R / A]` -/

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R] [Finite A] [IsDomain R] [IsNoetherianRing R]
  {A₁ : Type u} [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R']
  {A₂ : Type u} [Group A₂] [Subsingleton A₂] [MulSemiringAction A₂ R']
  (μ₁ : OrbMap R A R A₁) (μ₂ : OrbMap R A₁ R' A₂)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

private lemma faithful_trivial : FaithfulSMul A₁ R :=
  ⟨fun _ => Subsingleton.elim _ _⟩

private lemma smulComm_trivial : SMulCommClass A₁ K R :=
  ⟨fun a k r => by rw [Subsingleton.elim a 1, one_smul, one_smul]⟩

/-- **Mixed case of F7/F7′: `temperedPi1Map` of `Spec R' → Spec R → [Spec R / A]` is
injective.** -/
theorem temperedPi1Map_injective_mixed :
    Function.Injective (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV) := by
  haveI := faithful_trivial (A₁ := A₁) (R := R)
  haveI := smulComm_trivial (A₁ := A₁) (K := K) (R := R)
  exact temperedPi1Map_comp_injective μ₁ μ₂ V hV (temperedPi1Map_injective_orbifold μ₁ V hV)
    (temperedPi1Map_injective V hV μ₂)

/-- **Mixed case of F7/F7′: `temperedPi1Map` of `Spec R' → Spec R → [Spec R / A]` is an open
embedding.** -/
theorem isOpenEmbedding_temperedPi1Map_mixed :
    Topology.IsOpenEmbedding (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV) := by
  haveI := faithful_trivial (A₁ := A₁) (R := R)
  haveI := smulComm_trivial (A₁ := A₁) (K := K) (R := R)
  exact isOpenEmbedding_temperedPi1Map_comp μ₁ μ₂ V hV
    (isOpenEmbedding_temperedPi1Map_orbifold μ₁ V hV) (isOpenEmbedding_temperedPi1Map V hV μ₂)

/-- **Mixed case of F7/F7′: the image of `temperedPi1Map` of `Spec R' → Spec R → [Spec R / A]`
has finite index**, namely `[Γ_{[Y/A]} : Γ_Y] · [Γ_Y : Γ_{Y'}]`. -/
theorem finiteIndex_range_temperedPi1Map_mixed :
    (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV).range.FiniteIndex := by
  haveI := faithful_trivial (A₁ := A₁) (R := R)
  haveI := smulComm_trivial (A₁ := A₁) (K := K) (R := R)
  haveI := finiteIndex_range_temperedPi1Map_orbifold (O := O) μ₁ V hV
  haveI := finiteIndex_range_temperedPi1Map (O := O) V hV μ₂
  exact finiteIndex_range_temperedPi1Map_comp μ₁ μ₂ V hV
    (temperedPi1Map_injective_orbifold μ₁ V hV)

/-- The image in the mixed case: the image under the orbifold-cover map of the stabilizer of the
base point of `Spec R' → Spec R`. -/
theorem range_temperedPi1Map_mixed :
    (temperedPi1Map (O := O) (μ₁.comp μ₂) V hV).range =
      (temperedPi1Map μ₂ V hV).range.map (temperedPi1Map μ₁ V hV) :=
  range_temperedPi1Map_comp μ₁ μ₂ V hV

end Mixed

end

end TemperedFundamentalGroups
