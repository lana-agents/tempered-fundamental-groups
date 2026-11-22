/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothBaseChange
import TemperedFundamentalGroups.SemistableReduction.CompleteFree

/-!
# Unramified extensions of a discrete valuation ring with prescribed residue field (MR12 S5.7)

Let `O` be a discrete valuation ring with maximal ideal `𝔪` and residue field `k = O ⧸ 𝔪`, and
`f ∈ O[X]` monic whose reduction `f̄ ∈ k[X]` is irreducible. Then `O' = O[X] ⧸ (f)`
(`AdjoinRoot f`) is:

* **`UnramifiedLift.isDomain`**, **`isLocalRing`**, **`maximalIdeal_eq`** (`𝔪_{O'} = 𝔪 O'`),
  **`isDiscreteValuationRing`** (a uniformizer of `O` stays one);
* **`residueEquiv`**: `O' ⧸ 𝔪 O' ≃ₐ[O] k[X] ⧸ (f̄)`, the prescribed residue field;
* **`etale`**: étale over `O` if `f̄` is separable;
* **`isAdicComplete`**: `𝔪 O'`-adically complete if `O` is `𝔪`-adically complete (finite free).

This is the finite unramified base change `O → O'` of the S5.7 route for finite residue fields
(a finite separable `k' / k` is `k[X] ⧸ (f̄)` for the minimal polynomial `f̄` of a primitive
element; any monic lift `f` works).
-/

open Polynomial IsLocalRing

namespace SemistableReduction

namespace UnramifiedLift

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {f : O[X]}

/-- `O' ⧸ 𝔪 O' ≃ k[X] ⧸ (f̄)`. -/
noncomputable def residueEquiv (f : O[X]) :
    (AdjoinRoot f ⧸ (maximalIdeal O).map (AdjoinRoot.of f)) ≃ₐ[O]
      (O ⧸ maximalIdeal O)[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (maximalIdeal O))} :=
  AdjoinRoot.quotEquivQuotMap f (maximalIdeal O)

variable (hf : f.Monic) (hirr : Irreducible (f.map (Ideal.Quotient.mk (maximalIdeal O))))
include hf hirr

omit hf in
/-- `𝔪 O'` is a maximal ideal. -/
theorem isMaximal_map : ((maximalIdeal O).map (AdjoinRoot.of f)).IsMaximal := by
  letI := Ideal.Quotient.field (maximalIdeal O)
  haveI := PrincipalIdealRing.isMaximal_of_irreducible hirr
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField (Ideal.Quotient.field _).toIsField (residueEquiv f).toMulEquiv

/-- `O'` is a domain (`f` is irreducible, hence prime in the factorial ring `O[X]`). -/
theorem isDomain : IsDomain (AdjoinRoot f) := by
  letI := Ideal.Quotient.field (maximalIdeal O)
  have hf' : Irreducible f := Polynomial.Monic.irreducible_of_irreducible_map _ f hf hirr
  exact AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf')

/-- `O'` is local with maximal ideal `𝔪 O'`. -/
theorem isLocalRing : IsLocalRing (AdjoinRoot f) := by
  haveI := isMaximal_map hirr
  haveI : Module.Finite O (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  refine .of_unique_max_ideal ⟨_, isMaximal_map hirr, fun M hM ↦ ?_⟩
  have hc : M.comap (algebraMap O (AdjoinRoot f)) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hle : (maximalIdeal O).map (AdjoinRoot.of f) ≤ M := by
    rw [Ideal.map_le_iff_le_comap, ← hc]
    rfl
  exact ((isMaximal_map hirr).eq_of_le hM.ne_top hle).symm

/-- The maximal ideal of `O'` is `𝔪 O'`. -/
theorem maximalIdeal_eq :
    letI := isLocalRing hf hirr
    maximalIdeal (AdjoinRoot f) = (maximalIdeal O).map (AdjoinRoot.of f) := by
  letI := isLocalRing hf hirr
  exact (IsLocalRing.eq_maximalIdeal (isMaximal_map hirr)).symm

/-- **`O'` is a discrete valuation ring**; a uniformizer of `O` stays a uniformizer. -/
theorem isDiscreteValuationRing :
    letI := isDomain hf hirr
    IsDiscreteValuationRing (AdjoinRoot f) := by
  letI := isDomain hf hirr
  letI := isLocalRing hf hirr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdeg : f.degree ≠ 0 := by
    intro h
    apply hirr.not_isUnit
    rw [Polynomial.eq_one_of_monic_natDegree_zero hf
      (natDegree_eq_zero_iff_degree_le_zero.mpr h.le), Polynomial.map_one]
    exact isUnit_one
  have hinj : Function.Injective (AdjoinRoot.of f) := AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  have hmax : maximalIdeal (AdjoinRoot f) = Ideal.span {AdjoinRoot.of f ϖ} := by
    rw [maximalIdeal_eq hf hirr, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hr0 : AdjoinRoot.of f ϖ ≠ 0 := fun h ↦ hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hpid : IsPrincipalIdealRing (AdjoinRoot f) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (AdjoinRoot f)).out 4 0).mp (by rw [hmax]; exact ⟨_, rfl⟩)
  exact { not_a_field' := by rw [hmax]; simpa using hr0 }

/-- **`O'` is étale over `O`** if `f̄` is separable. -/
theorem etale (hsep : (f.map (Ideal.Quotient.mk (maximalIdeal O))).Separable) :
    Algebra.Etale O (AdjoinRoot f) := by
  letI := isLocalRing hf hirr
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨a', rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective b
  refine etale_of_aeval_eq_zero hf b' a' (AdjoinRoot.aeval_eq f ▸ AdjoinRoot.mk_self) ?_
    (AdjoinRoot.adjoinRoot_eq_top) fun q hq h0 ↦ ?_
  · -- `f' b' + f a' ≡ 1` modulo `𝔪`, so its value at the root is a unit of the local ring `O'`
    have hmem : aeval (AdjoinRoot.root f) (derivative f * b' + f * a') - 1 ∈
        maximalIdeal (AdjoinRoot f) := by
      rw [maximalIdeal_eq hf hirr, AdjoinRoot.aeval_eq, ← map_one (AdjoinRoot.mk f), ← map_sub]
      have h1 : (derivative f * b' + f * a' - 1).map (Ideal.Quotient.mk (maximalIdeal O)) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          Polynomial.map_one]
        rw [Polynomial.derivative_map] at hab
        linear_combination hab
      have hg : derivative f * b' + f * a' - 1 ∈ (maximalIdeal O).map (C : O →+* O[X]) :=
        Ideal.mem_map_C_iff.2 fun n ↦ by
          have := congrArg (fun p ↦ Polynomial.coeff p n) h1
          simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
            Ideal.Quotient.eq_zero_iff_mem] using this
      have := Ideal.mem_map_of_mem (AdjoinRoot.mk f) hg
      rwa [Ideal.map_map] at this
    by_contra hu
    exact (IsLocalRing.maximalIdeal.isMaximal (AdjoinRoot f)).ne_top
      ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hu) hmem
        simp at this))
  · rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h0
    exact Polynomial.eq_zero_of_dvd_of_degree_lt h0 hq

omit hirr in
/-- **`O'` is `𝔪 O'`-adically complete** if `O` is `𝔪`-adically complete. -/
theorem isAdicComplete [IsAdicComplete (maximalIdeal O) O] :
    IsAdicComplete ((maximalIdeal O).map (algebraMap O (AdjoinRoot f))) (AdjoinRoot f) :=
  CompleteFree.isAdicComplete_map (maximalIdeal O) (AdjoinRoot.powerBasis' hf).basis

end UnramifiedLift

end SemistableReduction
