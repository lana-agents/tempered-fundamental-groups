/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Cont

/-!
# Simultaneous approximation at the extensions of a type-3 point

Blueprint §9.10a (II.2).

* `denseRange_toLocalPi`: `F'` is dense in `∏_g K[X]/(g)` (Chinese remainder theorem for the
  factors of the minimal polynomial over the completion);
* `exists_approx_ext`: for targets `t_ξ` at the extensions `ξ` of a Gauss valuation `w_{0,r}` there
  is `y ∈ F'` with `ξ(y - t_ξ) < ε` for all `ξ`;
* `exists_mul_prod_isIntegral`: every `y ∈ F'` is `a / ∏ (x - zᵢ)` with `a` integral over `C[x]`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace LocalGlobal

variable {F K F' : Type*} [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [hd : Fact (DenseRange (algebraMap F K))]

omit [IsUltrametricDist F] in
/-- **Simultaneous density**: `F'` is dense in `∏_g K[X]/(g)`. -/
theorem denseRange_toLocalPi :
    DenseRange (fun y : F' ↦ fun g : Factor F K F' ↦ toLocal g y) := by
  classical
  set Φ : (Fin (minpolyK F K F').natDegree → K) → ∀ g : Factor F K F', Local K g.1 :=
    fun c g ↦ sumPow (F := F) (K := K) (F' := F') (root g.1) c
  have hΦc : Continuous Φ := continuous_pi fun g ↦ continuous_sumPow _
  have hs : Function.Surjective Φ := by
    intro t
    choose p hp using fun g : Factor F K F' ↦ AdjoinRoot.mk_surjective (t g)
    -- Chinese remainder idempotents
    have hcop : ∀ g : Factor F K F', IsCoprime g.1 (∏ h ∈ Finset.univ.erase g, h.1) := by
      intro g
      refine IsCoprime.prod_right fun h hh ↦ isCoprime_of_mem_factors g.2 h.2 fun he ↦ ?_
      exact (Finset.mem_erase.1 hh).1 (Subtype.ext he.symm)
    choose A B hAB using hcop
    set E : Factor F K F' → K[X] := fun g ↦ B g * ∏ h ∈ Finset.univ.erase g, h.1
    have hEg : ∀ g, aeval (root g.1) (E g) = 1 := by
      intro g
      have := congrArg (aeval (root g.1)) (hAB g)
      rwa [map_add, map_mul, aeval_root, mul_zero, zero_add, map_one] at this
    have hEh : ∀ g h : Factor F K F', h ≠ g → aeval (root h.1) (E g) = 0 := by
      intro g h hne
      simp only [E, map_mul, map_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, Finset.mem_univ h⟩) (aeval_root h.1),
        mul_zero]
    set q : K[X] := ∑ g, E g * p g
    refine ⟨fun n ↦ (q %ₘ minpolyK F K F').coeff n, funext fun h ↦ ?_⟩
    change sumPow (F := F) (K := K) (F' := F') (root h.1) _ = t h
    rw [sumPow_modByMonic (aeval_root_minpolyK h) q, map_sum,
      Finset.sum_eq_single h (fun g _ hgh ↦ by rw [map_mul, hEh g h (Ne.symm hgh), zero_mul])
        (fun hh ↦ absurd (Finset.mem_univ h) hh), map_mul, hEg, one_mul, ← hp h]
    exact AdjoinRoot.aeval_eq (p h)
  have := hs.denseRange.comp denseRange_piMap hΦc
  refine this.mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨∑ n, a n • (pb F F').gen ^ (n : ℕ), funext fun g ↦ toLocal_sum g a⟩

end LocalGlobal

namespace Type3

open LocalGlobal GaussStability GaussFibre

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

omit [IsAlgClosed C] in
/-- **Weak approximation** at the extensions of a Gauss valuation. -/
theorem exists_approx_ext [Algebra.IsSeparable (RatFunc C) F'] {r : ℝ≥0ˣ}
    (t : GaussExtension (0 : C) r F' → F') {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ y : F', ∀ ξ : GaussExtension (0 : C) r F', ξ.1 (y - t ξ) < ε := by
  set K := UniformSpace.Completion (GaussField (0 : C) r)
  set T : ∀ g : Factor (GaussField (0 : C) r) K F', Local K g.1 :=
    fun g ↦ toLocal g (t (factorEquiv g))
  set U : Set (∀ g : Factor (GaussField (0 : C) r) K F', Local K g.1) :=
    ⋂ g, {z | ‖z g - T g‖₊ < ε}
  have hU : IsOpen U := isOpen_iInter_of_finite fun g ↦
    isOpen_lt (continuous_nnnorm.comp ((continuous_apply g).sub continuous_const))
      continuous_const
  obtain ⟨y, hy⟩ := denseRange_toLocalPi.exists_mem_open hU
    ⟨T, Set.mem_iInter.2 fun g ↦ by simpa using hε⟩
  refine ⟨y, fun ξ ↦ ?_⟩
  obtain ⟨g, rfl⟩ := factorEquiv.surjective ξ
  rw [factorEquiv_apply_val, extValuation_apply, map_sub]
  exact Set.mem_iInter.1 hy g

variable [Algebra C F'] [IsScalarTower C (RatFunc C) F']

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
lemma isIntegral_adjoin_xF {f : F'} [Algebra C[X] F'] [IsScalarTower C[X] (RatFunc C) F']
    (hf : IsIntegral C[X] f) : IsIntegral (Algebra.adjoin C {xF C F'}) f := by
  have hrange : Algebra.adjoin C {xF C F'} = (aeval (xF C F') : C[X] →ₐ[C] F').range :=
    Algebra.adjoin_singleton_eq_range_aeval C (xF C F')
  set ψ : C[X] →+* Algebra.adjoin C {xF C F'} :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
      (aeval (xF C F') : C[X] →ₐ[C] F').rangeRestrict.toRingHom
  refine IsIntegral.map_of_comp_eq ψ (RingHom.id F') (RingHom.ext fun P ↦ ?_) hf
  change aeval (xF C F') P = algebraMap C[X] F' P
  rw [aeval_xF, IsScalarTower.algebraMap_apply C[X] (RatFunc C) F']

omit [IsUltrametricDist C] in
/-- Every element is `a / ∏ (x - zᵢ)` with `a` integral over `C[x]`. -/
theorem exists_mul_prod_isIntegral (f : F') : ∃ Z : Multiset C,
    IsIntegral (Algebra.adjoin C {xF C F'})
      (f * (Z.map fun z ↦ xF C F' - algebraMap C F' z).prod) := by
  letI : Algebra C[X] F' := ((algebraMap (RatFunc C) F').comp
    (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples C[X] (RatFunc C) {f}
  have hf := isIntegral_adjoin_xF (hyint f (Finset.mem_singleton_self f))
  refine ⟨y.roots, ?_⟩
  have hsplit : y = Polynomial.C y.leadingCoeff * (y.roots.map fun a ↦ X - Polynomial.C a).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree)).symm
  have hlc : y.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hy0
  have hyf : y • f = algebraMap C F' y.leadingCoeff *
      (f * (y.roots.map fun z ↦ xF C F' - algebraMap C F' z).prod) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply C[X] (RatFunc C) F', ← aeval_xF]
    conv_lhs => rw [hsplit]
    rw [map_mul, aeval_C, map_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, map_sub, aeval_X, aeval_C]
    ring
  have : f * (y.roots.map fun z ↦ xF C F' - algebraMap C F' z).prod =
      algebraMap C F' y.leadingCoeff⁻¹ * (y • f) := by
    rw [hyf, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hlc, map_one, one_mul]
  rw [this]
  refine IsIntegral.mul ?_ hf
  exact isIntegral_algebraMap (x := (⟨_, Subalgebra.algebraMap_mem _ y.leadingCoeff⁻¹⟩ :
    Algebra.adjoin C {xF C F'}))

end Type3

end SemistableReduction
