/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.FieldChangePure
import TemperedFundamentalGroups.Setup.CompleteDVRExtension

/-!
# F8 for finite extensions of complete discretely valued fields (Blueprint §11, F8)

Let `(K, O) → (K', O')` be an extension of valued fields (`O'.comap (algebraMap K K') = O`) with
`O` a **complete discrete valuation ring** and `K'/K` **finite separable** (e.g. `CharZero K`).
Then `O'` is the integral closure of `O` in `K'` and is finite over `O` (`valMap_finite`; the map
`O → O'` is local, `isLocalHom_valMap`, and `Setup/CompleteDVRExtension.lean` shows that the
integral closure of a complete DVR is local and is the unique valuation ring over it).

This discharges the hypothesis `(valMap hO).Finite` of `Tempered/FieldChangePure.lean`, giving
the unconditional F8 statements `temperedPi1FieldEquiv'` (the pure field change is an
isomorphism of topological groups) and, in the scheme case for `R'` finite étale over `R`,
`isOpenEmbedding_temperedPi1FieldMap'`, `range_temperedPi1FieldMap'`,
`mem_range_temperedPi1FieldMap'`, `finiteIndex_range_temperedPi1FieldMap'`.
-/

universe u

open CategoryTheory IsLocalRing Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

section Finite

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {K' : Type u} [Field K'] [Algebra K K'] {O' : ValuationSubring K'}
  (hO : O'.comap (algebraMap K K') = O)

/-- The map of valuation rings `O → O'` of an extension of valued fields is local. -/
lemma isLocalHom_valMap : IsLocalHom (valMap hO) := by
  refine ⟨fun o ho => ?_⟩
  have ho0 : (o : K) ≠ 0 := fun h => by
    have : valMap hO o = 0 := Subtype.ext (by simp [coe_valMap, h])
    rw [this] at ho
    exact not_isUnit_zero ho
  obtain ⟨v, hv⟩ := ho.exists_right_inv
  have hv' : (algebraMap K K' (o : K))⁻¹ = v := by
    have h : algebraMap K K' (o : K) * v = 1 := by
      rw [← coe_valMap hO]; exact congrArg Subtype.val hv
    exact inv_eq_of_mul_eq_one_right h
  have hinv : (o : K)⁻¹ ∈ O'.comap (algebraMap K K') := by
    rw [ValuationSubring.mem_comap, map_inv₀, hv']
    exact v.2
  rw [hO] at hinv
  exact IsUnit.of_mul_eq_one (a := o) ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ho0))

variable [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
  [FiniteDimensional K K'] [Algebra.IsSeparable K K']

/-- **`O'` is finite over `O`** for `K'/K` finite separable and `O` a complete discrete valuation
ring (`O'` is then the integral closure of `O` in `K'`). -/
theorem valMap_finite : (valMap hO).Finite := by
  letI : Algebra O K' := ((algebraMap K K').comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := isLocalHom_valMap hO
  exact finite_of_isLocalHom K O' (valMap hO) (RingHom.ext fun _ => rfl)

end Finite

variable {K : Type u} [Field K] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
  {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra.IsSeparable K K']
  {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O)
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']

section Map

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- **F8, pure case, unconditional**: for `O` a complete DVR and `K'/K` finite separable, the
change of the valued field is an isomorphism of topological groups
`temperedPi1 O' R' A' ≃ₜ* temperedPi1 O R' A'`. -/
def temperedPi1FieldEquiv' :
    temperedPi1 O' R' A' V hV' ≃ₜ* temperedPi1 O R' A' V (TempObj.comap_eq hO V hV') :=
  temperedPi1FieldEquiv hO (valMap_finite hO) V hV'

lemma temperedPi1FieldEquiv'_apply (γ : temperedPi1 O' R' A' V hV') :
    temperedPi1FieldEquiv' hO V hV' γ = temperedPi1FieldMap hO (OrbMap.id R' A') V hV' γ :=
  rfl

theorem bijective_temperedPi1FieldMap_pure' :
    Function.Bijective (temperedPi1FieldMap hO (OrbMap.id R' A') V hV') :=
  bijective_temperedPi1FieldMap_pure hO (valMap_finite hO) V hV'

end Map

section Etale

variable {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [Algebra R R'] [IsScalarTower K R R'] (μ : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')
  [Subsingleton A] [Subsingleton A'] [SMulCommClass A K R]
  [Algebra.Etale R R'] [Module.Finite R R']

/-- **F8 (scheme case, unconditional): the change of the valued field is injective**
(`O` a complete DVR, `K'/K` finite separable, `R'` finite étale over `R`). -/
theorem temperedPi1FieldMap_injective' :
    Function.Injective (temperedPi1FieldMap hO μ V hV') :=
  temperedPi1FieldMap_injective hO (valMap_finite hO) μ V hV'

/-- **F8 (scheme case, unconditional): the change of the valued field is an open embedding.** -/
theorem isOpenEmbedding_temperedPi1FieldMap' :
    Topology.IsOpenEmbedding (temperedPi1FieldMap hO μ V hV') :=
  isOpenEmbedding_temperedPi1FieldMap hO (valMap_finite hO) μ V hV'

/-- **F8 (scheme case, unconditional): the image of the change of the valued field is the
stabilizer** of the base point of the finite étale cover `Spec R' → Spec R`. -/
theorem range_temperedPi1FieldMap' :
    (temperedPi1FieldMap hO μ V hV').range =
      (temperedPi1Map μ V (TempObj.comap_eq hO V hV')).range :=
  range_temperedPi1FieldMap hO (valMap_finite hO) μ V hV'

theorem mem_range_temperedPi1FieldMap' (γ : temperedPi1 O R A V (TempObj.comap_eq hO V hV')) :
    γ ∈ (temperedPi1FieldMap hO μ V hV').range ↔
      γ.app (coverObj O R A R') (coverFibrePt V (TempObj.comap_eq hO V hV')) =
        coverFibrePt V (TempObj.comap_eq hO V hV') :=
  mem_range_temperedPi1FieldMap hO (valMap_finite hO) μ V hV' γ

/-- **F8 (scheme case, unconditional): the image has finite index.** -/
theorem finiteIndex_range_temperedPi1FieldMap' :
    (temperedPi1FieldMap hO μ V hV').range.FiniteIndex :=
  finiteIndex_range_temperedPi1FieldMap hO (valMap_finite hO) μ V hV'

end Etale

end

end TemperedFundamentalGroups
