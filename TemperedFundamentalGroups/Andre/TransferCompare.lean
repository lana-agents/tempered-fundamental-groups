/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.Transfer
import TemperedFundamentalGroups.Tempered.BaseChange

/-!
# T1 as a special case of functoriality (Blueprint §11, F6)

For a trivial group `A'` acting on `R`, the map of orbifolds `Spec R → [Spec R / A]` is the
`OrbMap` `toTrivialOrbMap A'` with the identity ring map and the trivial homomorphism
`A' →* A`. We show that the restriction homomorphism `restrictHom` of T1 (§10.3.2) is the
homomorphism `temperedPi1Map (toTrivialOrbMap A')` of §11 (`restrictHom_eq_temperedPi1Map`).

The proof uses the comparison morphism `bc Y ⟶ res Y` (`b ↦ 1 ⊗ b` on coordinate rings,
`H ×_A A' → H⁰` on groups), which is compatible with the two fibre isomorphisms.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  (A' : Type u) [Group A'] [Subsingleton A'] [MulSemiringAction A' R]

/-- The map of orbifolds `Spec R → [Spec R / A]` (`A'` trivial): identity ring map, trivial
homomorphism `A' →* A`. -/
def toTrivialOrbMap : OrbMap R A R A' where
  α := 1
  map_smul a r := by simp [Subsingleton.elim a 1]
  injective := fun _ _ h => h

namespace FiniteLevel

lemma bcPr_trivial_mem_H0 (L : FiniteLevel R A) (g : (L.baseChange (toTrivialOrbMap A')).H) :
    L.bcPr (toTrivialOrbMap A') g ∈ L.H0 := by
  rw [mem_H0, bcPr_a]
  rfl

/-- The comparison morphism of levels `bc L ⟶ res L`. -/
def bcResLevel (L : FiniteLevel R A) : L.baseChange (toTrivialOrbMap A') ⟶ L.res A' where
  f := { L.bcι (toTrivialOrbMap A') with
    commutes' := fun r => by
      change L.bcι (toTrivialOrbMap A') (algebraMap R L.B r) = _
      rw [bcι_algebraMap]
      rfl }
  r := (L.resEquiv A').toMonoidHom.comp
    ((L.bcPr (toTrivialOrbMap A')).codRestrict L.H0 (L.bcPr_trivial_mem_H0 A'))
  r_a _ := Subsingleton.elim _ _
  f_σ g y := (L.bcσ_bcι (toTrivialOrbMap A') g y).symm

end FiniteLevel

namespace TempObj

/-- The comparison morphism `bc Y ⟶ res Y` in the tempered category of `Spec R`. -/
def bcResHom (Y : TempObj O R A) : Y.baseChange (toTrivialOrbMap A') ⟶ Y.res A' where
  φ := Y.Lv.L.bcResLevel A'
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := Category.comp_id _
  h := _root_.id
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act g x := by
    change Y.P.act (Y.Lv.L.bcPr (toTrivialOrbMap A') g) x =
      Y.P.act (((Y.Lv.L.resEquiv A').symm (Y.Lv.L.resEquiv A'
        ⟨Y.Lv.L.bcPr (toTrivialOrbMap A') g, _⟩) : Y.Lv.L.H0) : Y.Lv.L.H) x
    rw [MulEquiv.symm_apply_apply]

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma resFibreEquiv_bcResHom (Y : TempObj O R A)
    (z : Fibre Ω V hV (Y.baseChange (toTrivialOrbMap A'))) :
    resFibreEquiv A' V hV Y (fibreMap V hV (Y.bcResHom A') z) =
      bcFibreEquiv (toTrivialOrbMap A') V hV Y z := by
  induction z using Quotient.inductionOn
  rfl

end TempObj

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **T1 is a special case of functoriality** (Blueprint §11, F6): the restriction
homomorphism `temperedPi1(Y) →* temperedPi1([Y/A])` is `temperedPi1Map` of the orbifold map
`Y → [Y/A]`. -/
theorem restrictHom_eq_temperedPi1Map :
    restrictHom O R A A' V hV = temperedPi1Map (toTrivialOrbMap A') V hV := by
  ext γ Y y
  change (TempObj.resFibreEquiv A' V hV Y) (γ.app (Y.res A')
    ((TempObj.resFibreEquiv A' V hV Y).symm y)) = _
  rw [temperedPi1Map_app]
  set z := (TempObj.bcFibreEquiv (toTrivialOrbMap A') V hV Y).symm y with hz
  have hy : (TempObj.resFibreEquiv A' V hV Y).symm y =
      TempObj.fibreMap V hV (Y.bcResHom A') z := by
    rw [Equiv.symm_apply_eq, TempObj.resFibreEquiv_bcResHom, hz, Equiv.apply_symm_apply]
  rw [hy, show γ.app _ (TempObj.fibreMap V hV (Y.bcResHom A') z) =
    TempObj.fibreMap V hV (Y.bcResHom A') (γ.app _ z) from
      FibreAut.app_naturality γ (Y.bcResHom A') z, TempObj.resFibreEquiv_bcResHom]

end

end TemperedFundamentalGroups
