/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGaloisMid
import TemperedFundamentalGroups.Andre.StageLimit

/-!
# André's group of an orbifold as an inverse limit of stage groups (Blueprint §11.3, G6)

Orbifold case (`A` any finite group acting `K`-linearly on `R`). The orbifold Galois objects
`galO = galClassO O R A Ω Unit₁` (`Andre/OrbGaloisClass.lean`: `Ind_1^S Z̃` over levels induced
from scheme levels Galois over `[Spec R / A]`) satisfy (gal), (dom), (rig) unconditionally
(`galoisLimitData_galO`), so (group form of K1, `GaloisLimit.fibreAutHomeo`)

* `temperedPi1HomeoLimO`: `temperedPi1 ≃ₜ* lim_{(U, g)} Π_U`;
* `andreGroupHomeoLimO`: **`andreGroup ≃ₜ* lim Π_U`** (with Theorem A, `andreEquiv'`);

`Π_U` the stage groups (permutations of the fibre of `U` induced by `Aut U`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open GaloisLimit

namespace OrbGal

/-- The trivial group, acting trivially on `R` (the scheme case inside the orbifold). -/
def Unit₁ : Type u := PUnit.{u + 1}

instance : Group Unit₁.{u} := inferInstanceAs (Group PUnit.{u + 1})

instance : Subsingleton Unit₁.{u} := inferInstanceAs (Subsingleton PUnit.{u + 1})

instance {R : Type u} [CommRing R] : MulSemiringAction Unit₁.{u} R :=
  MulSemiringAction.compHom R (1 : Unit₁.{u} →* RingAut R)

end OrbGal

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

variable (O R A Ω) in
/-- **The orbifold Galois objects.** -/
abbrev galO : ObjectProperty (TempObj O R A) := galClassO O R A Ω OrbGal.Unit₁.{u}

include hp hR in
/-- **(gal), (dom), (rig) for `galO`, unconditionally.** -/
theorem galoisLimitData_galO :
    IsGaloisClass (tempFibre O R A V hV) (galO O R A Ω) ∧
      IsDominating (tempFibre O R A V hV) (galO O R A Ω) ∧
      IsRigid (tempFibre O R A V hV) (galO O R A Ω) :=
  haveI := Algebra.FiniteType.isNoetherianRing K R
  galoisLimitDataO V hV OrbGal.Unit₁ (SemistableReduction.Statement.strongComponentAS_of
    SemistableReduction.Statement.zariskiConnected) hp.choose hp.choose_spec.1
    hp.choose_spec.2 hR

/-- **The inverse limit of the stage groups** of the pointed orbifold Galois objects. -/
abbrev stageLimitO : Subgroup (∀ q : PtGal (tempFibre O R A V hV) (galO O R A Ω),
    stageGroup (tempFibre O R A V hV) q.G) :=
  limGroup (tempFibre O R A V hV) (galO O R A Ω)
    (galoisLimitData_galO (R := R) (A := A) V hV hp hR).1
    (galoisLimitData_galO (R := R) (A := A) V hV hp hR).2.2

/-- **`temperedPi1 ≃ₜ* lim Π_U`** for the orbifold `[Spec R / A]`. -/
def temperedPi1HomeoLimO : temperedPi1 O R A V hV ≃ₜ* stageLimitO (R := R) (A := A) V hV hp hR :=
  fibreAutHomeo _ _ (galoisLimitData_galO (R := R) (A := A) V hV hp hR).2.1

lemma temperedPi1HomeoLimO_apply (γ : temperedPi1 O R A V hV)
    (q : PtGal (tempFibre O R A V hV) (galO O R A Ω)) :
    ((temperedPi1HomeoLimO V hV hp hR γ).1 q).1 q.g = γ⁻¹.app q.G q.g :=
  fibreAutEquiv_apply _ _ _ γ q

/-- **G6, orbifold case: `andreGroup ≃ₜ* lim Π_U`.** -/
def andreGroupHomeoLimO :
    andreGroup O R A V hV ≃ₜ* stageLimitO (R := R) (A := A) V hV hp hR :=
  (andreEquiv' V hV hp hR).symm.trans (temperedPi1HomeoLimO (A := A) V hV hp hR)

end

end TemperedFundamentalGroups
