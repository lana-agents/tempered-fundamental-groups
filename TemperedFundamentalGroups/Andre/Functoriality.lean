/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TheoremAFinal
import TemperedFundamentalGroups.Tempered.BaseChange

/-!
# Functoriality of André's group, compatibly with Theorem A (Blueprint §11, F9)

Base change of tempered coverings along a map of orbifolds `μ : OrbMap R A R' A'`
(`TempObj.bcFunctor`) keeps the model, so it preserves coverings presented through semistable
levels (`isSemistableLevel_baseChange`). Restricting along it gives
`andreGroupMap μ : andreGroup O R' A' V hV →* andreGroup O R A V hV`, and the restriction
`temperedPi1 → andreGroup` of Theorem A intertwines `temperedPi1Map μ` and `andreGroupMap μ`
(`andreRestrict_temperedPi1Map`, `andreEquiv'_temperedPi1Map`).
-/

universe u

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] (μ : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma isSemistableLevel_baseChange {Lv : Level O R A} (h : IsSemistableLevel Lv) :
    IsSemistableLevel (Lv.baseChange μ) := h

/-- Base change on tempered coverings presented through semistable levels. -/
def bcSemistable :
    (semistableObj O R A).FullSubcategory ⥤ (semistableObj O R' A').FullSubcategory :=
  (semistableObj O R' A').lift ((semistableObj O R A).ι ⋙ TempObj.bcFunctor μ)
    fun X => isSemistableLevel_baseChange μ X.2

/-- The fibre functors agree along `bcSemistable`. -/
def bcSemistableFibreIso :
    bcSemistable μ ⋙ (semistableObj O R' A').ι ⋙ tempFibre O R' A' V hV ≅
      (semistableObj O R A).ι ⋙ tempFibre O R A V hV :=
  Functor.isoWhiskerLeft (semistableObj O R A).ι (TempObj.bcFibreIso μ V hV)

/-- **Functoriality of André's group** along a map of orbifolds. -/
def andreGroupMap : andreGroup O R' A' V hV →* andreGroup O R A V hV :=
  FibreAut.restrict (bcSemistable μ) (bcSemistableFibreIso μ V hV)

lemma continuous_andreGroupMap : Continuous (andreGroupMap μ V hV) :=
  FibreAut.continuous_restrict _ _

variable (O R A) in
/-- The restriction `temperedPi1 → andreGroup` (the map of Theorem A). -/
def andreRestrict : temperedPi1 O R A V hV →* andreGroup O R A V hV :=
  FibreAut.restrict (semistableObj O R A).ι (Iso.refl _)

/-- **The restriction to André's group is natural** in maps of orbifolds. -/
theorem andreRestrict_temperedPi1Map (γ : temperedPi1 O R' A' V hV) :
    andreRestrict O R A V hV (temperedPi1Map μ V hV γ) =
      andreGroupMap μ V hV (andreRestrict O R' A' V hV γ) := by
  ext c x
  rfl

section TheoremA

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Algebra.Smooth K R] [SMulCommClass A K R] [Finite A] [IsAlgClosed Ω]

/-- The isomorphism of Theorem A is the restriction `andreRestrict`. -/
lemma andreEquiv'_apply [IsDomain R] [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1) (γ : temperedPi1 O R A V hV) :
    andreEquiv' V hV hp hR γ = andreRestrict O R A V hV γ := by
  ext c x
  rfl

variable [Algebra.Smooth K R'] [SMulCommClass A' K R'] [Finite A']

/-- **Theorem A is natural** in maps of orbifolds: under the identifications of Theorem A,
`temperedPi1Map μ` is `andreGroupMap μ`. -/
theorem andreEquiv'_temperedPi1Map [IsDomain R] [IsDomain R']
    [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1) (hR' : ringKrullDim R' = 1) (γ : temperedPi1 O R' A' V hV) :
    andreEquiv' V hV hp hR (temperedPi1Map μ V hV γ) =
      andreGroupMap μ V hV (andreEquiv' V hV hp hR' γ) := by
  rw [andreEquiv'_apply, andreEquiv'_apply, andreRestrict_temperedPi1Map]

end TheoremA

end

end TemperedFundamentalGroups
