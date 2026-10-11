/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.FieldChangeComp
import TemperedFundamentalGroups.Tempered.CoverImage

/-!
# The image of the field change map (Blueprint §11, F8)

`temperedPi1 O R A` is the *arithmetic* tempered group: its levels are all finite étale
`R`-algebras, including constant extensions `K'' ⊗_K R`. So for a finite separable extension
`K'/K` and `R' = K' ⊗_K R` the tempered group of `X_{K'}` over `(K', O')` should be the open
subgroup of finite index of that of `X` over `(K, O)` which stabilizes the base point of the
finite étale cover `Spec R' → Spec R`, not the whole group.

Every field change factors as the *pure* field change (same ring `R'`, base `(K', O') → (K, O)`)
followed by `temperedPi1Map μ` over `O` (`temperedPi1FieldMap_eq_comp`, from F4-type comparison
morphisms in `Tempered/FieldChangeComp.lean`). With F7 we obtain, in the scheme case with `R'`
finite étale over `R`:

* `range_temperedPi1FieldMap_le`: the image of `temperedPi1FieldMap hO μ` lies in the image of
  `temperedPi1Map μ`, i.e. (`fixes_coverFibrePt_of_mem_range_temperedPi1FieldMap`) it fixes the
  base point of the cover `Spec R' → Spec R` (unconditional);
* `temperedPi1FieldMap_injective_of_pure`, `isOpenEmbedding_temperedPi1FieldMap_of_pure`,
  `range_temperedPi1FieldMap_of_pure`, `finiteIndex_range_temperedPi1FieldMap_of_pure`: if the pure
  field change `temperedPi1FieldMap hO (OrbMap.id R' A')` is injective (an open embedding,
  surjective), then so is `temperedPi1FieldMap hO μ` onto the stabilizer — an open subgroup of
  finite index.

The pure field change is an isomorphism of topological groups for `O'` finite over `O`
(`temperedPi1FieldEquiv`, `Tempered/FieldChangePure.lean`), which holds for `O` a complete DVR
and `K'/K` finite separable (`valMap_finite`, `Tempered/FieldChangeFinite.lean`); the orbifold
analogues are in `Tempered/FieldChangeOrbifold.lean`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

/-- `μ ∘ id = μ` for maps of orbifolds. -/
lemma OrbMap.comp_id {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]
    {R' : Type u} [CommRing R'] [Algebra R R'] {A' : Type u} [Group A']
    [MulSemiringAction A' R'] (μ : OrbMap R A R' A') : μ.comp (OrbMap.id R' A') = μ := by
  cases μ
  rfl

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {K' : Type u} [Field K'] [Algebra K K'] {O' : ValuationSubring K'}
  (hO : O'.comap (algebraMap K K') = O)
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']
  (μ : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- **Factorization of the field change** through the pure field change (same ring `R'`):
`fc μ = temperedPi1Map μ ∘ fc id`. -/
theorem temperedPi1FieldMap_eq_comp (γ : temperedPi1 O' R' A' V hV') :
    temperedPi1FieldMap hO μ V hV' γ = temperedPi1Map μ V (TempObj.comap_eq hO V hV')
      (temperedPi1FieldMap hO (OrbMap.id R' A') V hV' γ) := by
  have h := temperedPi1FieldMap_comp hO μ (OrbMap.id R' A') V hV' γ
  rwa [OrbMap.comp_id] at h

/-- The factorization as an equality of monoid homomorphisms. -/
theorem temperedPi1FieldMap_eq_comp' :
    temperedPi1FieldMap hO μ V hV' = (temperedPi1Map μ V (TempObj.comap_eq hO V hV')).comp
      (temperedPi1FieldMap hO (OrbMap.id R' A') V hV') :=
  MonoidHom.ext fun γ => temperedPi1FieldMap_eq_comp hO μ V hV' γ

/-- The image of the field change lies in the image of `temperedPi1Map μ`. -/
theorem range_temperedPi1FieldMap_le :
    (temperedPi1FieldMap hO μ V hV').range ≤
      (temperedPi1Map μ V (TempObj.comap_eq hO V hV')).range := by
  rw [temperedPi1FieldMap_eq_comp', MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

section Etale

variable [Subsingleton A] [Subsingleton A'] [SMulCommClass A K R]
  [Algebra.Etale R R'] [Module.Finite R R']

/-- **F8, scheme case: the image of the field change fixes the base point** of the finite étale
cover `Spec R' → Spec R` (e.g. `R' = K' ⊗_K R` for `K'/K` finite separable). -/
theorem fixes_coverFibrePt_of_mem_range_temperedPi1FieldMap
    {γ : temperedPi1 O R A V (TempObj.comap_eq hO V hV')}
    (hγ : γ ∈ (temperedPi1FieldMap hO μ V hV').range) :
    γ.app (coverObj O R A R') (coverFibrePt V (TempObj.comap_eq hO V hV')) =
      coverFibrePt V (TempObj.comap_eq hO V hV') :=
  (mem_range_temperedPi1Map V (TempObj.comap_eq hO V hV') μ γ).1
    (range_temperedPi1FieldMap_le hO μ V hV' hγ)

/-- If the pure field change is injective, so is the field change (scheme case, `R'` finite
étale over `R`). -/
theorem temperedPi1FieldMap_injective_of_pure
    (h : Function.Injective (temperedPi1FieldMap hO (OrbMap.id R' A') V hV')) :
    Function.Injective (temperedPi1FieldMap hO μ V hV') := by
  rw [temperedPi1FieldMap_eq_comp', MonoidHom.coe_comp]
  exact (temperedPi1Map_injective V (TempObj.comap_eq hO V hV') μ).comp h

/-- If the pure field change is an open embedding, so is the field change (scheme case). -/
theorem isOpenEmbedding_temperedPi1FieldMap_of_pure
    (h : Topology.IsOpenEmbedding (temperedPi1FieldMap hO (OrbMap.id R' A') V hV')) :
    Topology.IsOpenEmbedding (temperedPi1FieldMap hO μ V hV') := by
  rw [temperedPi1FieldMap_eq_comp', MonoidHom.coe_comp]
  exact (isOpenEmbedding_temperedPi1Map V (TempObj.comap_eq hO V hV') μ).comp h

/-- If the pure field change is surjective, the image of the field change is the stabilizer of
the base point of `Spec R' → Spec R` (scheme case). -/
theorem range_temperedPi1FieldMap_of_pure
    (h : Function.Surjective (temperedPi1FieldMap hO (OrbMap.id R' A') V hV')) :
    (temperedPi1FieldMap hO μ V hV').range =
      (temperedPi1Map μ V (TempObj.comap_eq hO V hV')).range := by
  rw [temperedPi1FieldMap_eq_comp', MonoidHom.range_comp, MonoidHom.range_eq_top.2 h,
    ← MonoidHom.range_eq_map]

theorem mem_range_temperedPi1FieldMap_of_pure
    (h : Function.Surjective (temperedPi1FieldMap hO (OrbMap.id R' A') V hV'))
    (γ : temperedPi1 O R A V (TempObj.comap_eq hO V hV')) :
    γ ∈ (temperedPi1FieldMap hO μ V hV').range ↔
      γ.app (coverObj O R A R') (coverFibrePt V (TempObj.comap_eq hO V hV')) =
        coverFibrePt V (TempObj.comap_eq hO V hV') := by
  rw [range_temperedPi1FieldMap_of_pure hO μ V hV' h]
  exact mem_range_temperedPi1Map V (TempObj.comap_eq hO V hV') μ γ

/-- If the pure field change is surjective, the image of the field change has finite index
(scheme case). -/
theorem finiteIndex_range_temperedPi1FieldMap_of_pure
    (h : Function.Surjective (temperedPi1FieldMap hO (OrbMap.id R' A') V hV')) :
    (temperedPi1FieldMap hO μ V hV').range.FiniteIndex := by
  rw [range_temperedPi1FieldMap_of_pure hO μ V hV' h]
  exact finiteIndex_range_temperedPi1Map V (TempObj.comap_eq hO V hV') μ

end Etale

end

end TemperedFundamentalGroups
