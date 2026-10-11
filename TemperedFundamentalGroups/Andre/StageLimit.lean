/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.GaloisGroupLimit
import TemperedFundamentalGroups.Andre.GaloisDomW
import TemperedFundamentalGroups.Andre.TheoremAFinal
import TemperedFundamentalGroups.SemistableReduction.ZariskiConnectedProof
import TemperedFundamentalGroups.SemistableReduction.W10MainComponent

/-!
# André's group as an inverse limit of stage groups (Blueprint §11.2, G6.2)

Scheme case. The Galois objects over W-model levels (`galClassW`, `Andre/GaloisDomW.lean`) satisfy
(gal), (dom), (rig) unconditionally (`galoisLimitDataW` with `Statement.strongComponentAS_of
Statement.zariskiConnected`). Their stage groups (`GaloisLimit.stageGroup`: the permutations of the
fibre `Φ(U_Lv)` induced by automorphisms of `U_Lv = (Lv, Ind Z̃)`, `Z̃` the tree covering of the
special fibre) form an inverse system along pointed morphisms, and

* `temperedPi1EquivLim`: `temperedPi1 ≃* lim_{(U_Lv, g)} Π_Lv`;
* `andreGroupEquivLim`: **`andreGroup ≃* lim Π_Lv`** (with Theorem A, `andreEquiv'`);
  `temperedPi1HomeoLim`, `andreGroupHomeoLim`: the same as isomorphisms of topological groups.

The description of each `Π_Lv` as an extension of the Galois group of the level by the deck group
of the tree covering is G6.3 (`Andre/StageGroup.lean`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open GaloisLimit

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

variable (O R A Ω) in
/-- **The Galois objects over W-model levels** on the x-line chosen from `hR`. -/
abbrev galW (hR : ringKrullDim R = 1) : ObjectProperty (TempObj O R A) :=
  galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)

include hp in
/-- **(gal), (dom), (rig) for `galW`, unconditionally.** -/
theorem galoisLimitData_galW :
    IsGaloisClass (tempFibre O R A V hV) (galW O R A Ω hR) ∧
      IsDominating (tempFibre O R A V hV) (galW O R A Ω hR) ∧
      IsRigid (tempFibre O R A V hV) (galW O R A Ω hR) :=
  galoisLimitDataW V hV (SemistableReduction.Statement.strongComponentAS_of
    SemistableReduction.Statement.zariskiConnected) hp.choose hp.choose_spec.1
    hp.choose_spec.2 hR

/-- **The inverse limit of the stage groups `Π_Lv`** of the pointed Galois objects over W-model
levels. -/
abbrev stageLimit : Subgroup (∀ p : PtGal (tempFibre O R A V hV) (galW O R A Ω hR),
    stageGroup (tempFibre O R A V hV) p.G) :=
  limGroup (tempFibre O R A V hV) (galW O R A Ω hR)
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2

/-- **`temperedPi1 ≃* lim Π_Lv`** (group form of K1). -/
def temperedPi1EquivLim : temperedPi1 O R A V hV ≃* stageLimit (R := R) (A := A) V hV hp hR :=
  fibreAutEquiv _ _ (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.1

lemma temperedPi1EquivLim_apply (γ : temperedPi1 O R A V hV)
    (p : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :
    ((temperedPi1EquivLim V hV hp hR γ).1 p).1 p.g = γ⁻¹.app p.G p.g :=
  fibreAutEquiv_apply _ _ _ γ p

/-- **G6: André's group is the inverse limit of the stage groups `Π_Lv`** of the Galois objects
`U_Lv` over semistable (W-model) levels (Theorem A and the group form of K1). -/
def andreGroupEquivLim [Finite A] [SMulCommClass A K R] :
    andreGroup O R A V hV ≃* stageLimit (R := R) (A := A) V hV hp hR :=
  (andreEquiv' V hV hp hR).toMulEquiv.symm.trans (temperedPi1EquivLim (A := A) V hV hp hR)

/-- **`temperedPi1 ≃ₜ* lim Π_Lv`**, `lim Π_Lv` with the inverse-limit topology of the discrete
stage groups. -/
def temperedPi1HomeoLim : temperedPi1 O R A V hV ≃ₜ* stageLimit (R := R) (A := A) V hV hp hR :=
  fibreAutHomeo _ _ (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.1

/-- **G6, topological form: `andreGroup ≃ₜ* lim Π_Lv`.** -/
def andreGroupHomeoLim [Finite A] [SMulCommClass A K R] :
    andreGroup O R A V hV ≃ₜ* stageLimit (R := R) (A := A) V hV hp hR :=
  (andreEquiv' V hV hp hR).symm.trans (temperedPi1HomeoLim (A := A) V hV hp hR)

end

end TemperedFundamentalGroups
