/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Setup.InvariantLine

/-!
# An invariant line under a smooth curve

Blueprint §9.7a (W10 assembly, step 1), in the setting of `Statement.StrongA`: `R` a smooth
`K`-domain of dimension one, `B` finite étale over `R`, a finite group `G` acting compatibly on
`R` and `B`.

* `exists_invariant_line`: a `G`-invariant `x : R` with `K[X] → R`, `X ↦ x`, finite
  (`exists_finite_aeval_invariant`); `x` is transcendental (`aeval_injective`);
* `lineAlgebra x : Algebra K[X] B` (`X ↦ x`); for such `x`: `B` is finite (`finite_line`) and
  torsion-free (`isTorsionFree_line`) over `K[X]`, `IsScalarTower K K[X] B` (`isScalarTower_line`),
  and `B` is smooth over `K` (`smooth_B`);
* `lineAct`: the action of `G` on `B` by `K[X]`-algebra automorphisms
  (`lineAct_restrictScalars`).
-/

universe u

open Polynomial nonZeroDivisors

namespace SemistableReduction

namespace W10Line

variable {K R : Type u} [Field K] [CommRing R] [Algebra K R] (hR : ringKrullDim R = 1)
  {B : Type u} [CommRing B] [Algebra R B]
  {G : Type u} [Group G]

include hR in
/-- A `G`-invariant `x : R` such that `R` is finite over `K[x]`. -/
theorem exists_invariant_line [Algebra.Smooth K R] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G K R] :
    ∃ x : R, (∀ g : G, g • x = x) ∧ (aeval (R := K) x).toRingHom.Finite :=
  exists_finite_aeval_invariant (G := G) hR

include hR in
/-- `x` is transcendental over `K`. -/
theorem aeval_injective [IsDomain R] {x : R} (hfin : (aeval (R := K) x).toRingHom.Finite) :
    Function.Injective (aeval (R := K) x) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have hx : IsIntegral K x := (IsAlgebraic.isIntegral ⟨p, hp0, hp⟩)
  let S := Algebra.adjoin K {x}
  haveI : Module.Finite K S := Algebra.finite_adjoin_simple_of_isIntegral hx
  haveI : Algebra.IsIntegral K S := Algebra.IsIntegral.of_finite K S
  have hxS : x ∈ S := Algebra.self_mem_adjoin_singleton K x
  let φ : K[X] →+* S :=
    ((aeval (R := K) x).toRingHom).codRestrict S.toSubring fun f ↦
      aeval_mem_adjoin_singleton K x
  have h1 : (algebraMap S R).IsIntegral := by
    refine RingHom.IsIntegral.tower_top φ (algebraMap S R) ?_
    have : (algebraMap S R).comp φ = (aeval (R := K) x).toRingHom := rfl
    rw [this]
    exact hfin.to_isIntegral
  haveI : Algebra.IsIntegral S R := ⟨fun r ↦ h1 r⟩
  haveI : Algebra.IsIntegral K R := Algebra.IsIntegral.trans S
  have := TemperedFundamentalGroups.NoetherLine.ringKrullDim_le_of_isIntegral' (A := K) (B := R)
  rw [hR, ringKrullDim_eq_zero_of_field] at this
  exact absurd this (by norm_num)

variable (K) in
/-- `K[X] → B`, `X ↦ x`. -/
@[implicit_reducible]
noncomputable def lineAlgebra (x : R) : Algebra K[X] B :=
  ((algebraMap R B).comp (aeval (R := K) x).toRingHom).toAlgebra

lemma lineAlgebra_algebraMap (x : R) (p : K[X]) :
    letI := lineAlgebra K (B := B) x
    algebraMap K[X] B p = algebraMap R B (aeval x p) := rfl

theorem isScalarTower_line [Algebra K B] [IsScalarTower K R B] (x : R) :
    letI := lineAlgebra K (B := B) x
    IsScalarTower K K[X] B := by
  letI := lineAlgebra K (B := B) x
  refine .of_algebraMap_eq fun k ↦ ?_
  rw [lineAlgebra_algebraMap, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, aeval_C, ← IsScalarTower.algebraMap_apply]

theorem finite_line [Module.Finite R B] {x : R} (hfin : (aeval (R := K) x).toRingHom.Finite) :
    letI := lineAlgebra K (B := B) x
    Module.Finite K[X] B :=
  (RingHom.finite_algebraMap.2 ‹_›).comp hfin

include hR in
theorem isTorsionFree_line [IsDomain R] [Algebra.Etale R B] {x : R}
    (hfin : (aeval (R := K) x).toRingHom.Finite) :
    letI := lineAlgebra K (B := B) x
    Module.IsTorsionFree K[X] B := by
  letI := lineAlgebra K (B := B) x
  haveI : Module.IsTorsionFree R B := ⟨fun r hr ↦
    Module.Flat.isSMulRegular_of_nonZeroDivisors (isRegular_iff_mem_nonZeroDivisors.1 hr)⟩
  refine Module.IsTorsionFree.comap (aeval (R := K) x) (fun p hp ↦ ?_) fun p b ↦ ?_
  · refine IsRegular.of_ne_zero fun h ↦ hp.ne_zero ?_
    exact aeval_injective hR hfin (by rw [h, map_zero])
  · rw [Algebra.smul_def, Algebra.smul_def]
    rfl

/-- `B` is smooth over `K` (étale over smooth). -/
theorem smooth_B [Algebra.Smooth K R] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] :
    Algebra.Smooth K B := Algebra.Smooth.comp K R B

section Action

variable [Algebra K B] [IsScalarTower K R B] [MulSemiringAction G B] [SMulCommClass G K B]
  [MulSemiringAction G R] [SMulCommClass G K R]
  (hequiv : ∀ (g : G) (r : R), g • algebraMap R B r = algebraMap R B (g • r))
  {x : R} (hx : ∀ g : G, g • x = x)

omit [Algebra K B] [IsScalarTower K R B] [SMulCommClass G K B] in
include hequiv hx in
lemma smul_algebraMap_line (g : G) (p : K[X]) :
    letI := lineAlgebra K (B := B) x
    g • algebraMap K[X] B p = algebraMap K[X] B p := by
  rw [lineAlgebra_algebraMap, hequiv]
  congr 1
  change MulSemiringAction.toAlgHom K R g (aeval x p) = _
  rw [← Polynomial.aeval_algHom_apply]
  exact congrArg (fun y ↦ aeval y p) (hx g)

/-- **The action of `G` on `B` by `K[X]`-algebra automorphisms** (`x` is invariant). -/
noncomputable def lineAct :
    letI := lineAlgebra K (B := B) x
    G →* (B ≃ₐ[K[X]] B) :=
  letI := lineAlgebra K (B := B) x
  { toFun := fun g ↦
      { MulSemiringAction.toAlgAut G K B g with
        commutes' := fun p ↦ smul_algebraMap_line (K := K) hequiv hx g p }
    map_one' := AlgEquiv.ext fun b ↦ one_smul G b
    map_mul' := fun g h ↦ AlgEquiv.ext fun b ↦ mul_smul g h b }

omit [IsScalarTower K R B] in
lemma lineAct_apply (g : G) (b : B) :
    letI := lineAlgebra K (B := B) x
    lineAct (K := K) hequiv hx g b = g • b := rfl

/-- `lineAct` is the given action. -/
theorem lineAct_restrictScalars (g : G) :
    letI := lineAlgebra K (B := B) x
    letI := isScalarTower_line (K := K) (B := B) x
    (lineAct (K := K) hequiv hx g).restrictScalars K = MulSemiringAction.toAlgAut G K B g := by
  letI := lineAlgebra K (B := B) x
  letI := isScalarTower_line (K := K) (B := B) x
  ext b
  rfl

end Action

end W10Line

end SemistableReduction
