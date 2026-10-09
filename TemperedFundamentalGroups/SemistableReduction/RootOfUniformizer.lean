/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Adjoining a root of a uniformizer

Let `O` be a discrete valuation ring with uniformizer `ϖ` and `0 < e`. The ring
`O[Y] ⧸ (Y ^ e - ϖ) = AdjoinRoot (X ^ e - C ϖ)` (Blueprint §9.2, first step of Abhyankar's lemma)
is a discrete valuation ring with uniformizer `Y` (`RootOfUniformizer.isDiscreteValuationRing`,
`RootOfUniformizer.maximalIdeal_eq`); it is totally ramified of index `e` over `O`: `ϖ = Y ^ e`
and the residue field of `O` maps onto its residue field
(`RootOfUniformizer.residueField_surjective`).

We also record `RootOfUniformizer.ramificationIdx_eq_addVal`: Mathlib's ramification index
`e(𝔓 | O)` of a prime with `B_𝔓` a DVR is the valuation of `ϖ` in `B_𝔓`.

The proof is elementary: every maximal ideal contains `ϖ` (integrality), hence `Y`; and an element
`g(Y) = g(0) + Y h(Y)` outside `(Y)` has `g(0)` a unit, so it lies in no maximal ideal.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

namespace RootOfUniformizer

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} {e : ℕ}

/-- The Eisenstein polynomial `X ^ e - ϖ`. -/
noncomputable abbrev poly (ϖ : O) (e : ℕ) : O[X] := X ^ e - C ϖ

/-- The ring `O[Y] ⧸ (Y ^ e - ϖ)`. -/
abbrev Ring (ϖ : O) (e : ℕ) := AdjoinRoot (poly ϖ e)

omit [IsDomain O] [IsDiscreteValuationRing O] in
lemma poly_monic (he : 0 < e) : (poly ϖ e).Monic := monic_X_pow_sub_C _ he.ne'

omit [IsDiscreteValuationRing O] in
lemma poly_natDegree : (poly ϖ e).natDegree = e := natDegree_X_pow_sub_C

/-- `X ^ e - ϖ` is Eisenstein at the maximal ideal. -/
lemma poly_isEisensteinAt (hϖ : Irreducible ϖ) (he : 0 < e) :
    (poly ϖ e).IsEisensteinAt (maximalIdeal O) := by
  have hmax : maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  refine (poly_monic he).isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal O).ne_top
    (fun {n} hn ↦ ?_) ?_
  · rw [poly_natDegree] at hn
    rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn.ne]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [hmax]
    · simp [hn0]
  · rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_sub, coeff_X_pow,
      coeff_C, if_neg he.ne, if_pos rfl, zero_sub, dvd_neg]
    rintro ⟨c, hc⟩
    apply hϖ.not_isUnit
    refine IsUnit.of_mul_eq_one c (mul_left_cancel₀ hϖ.ne_zero ?_)
    rw [mul_one, ← mul_assoc, ← sq, ← hc]

lemma poly_irreducible (hϖ : Irreducible ϖ) (he : 0 < e) : Irreducible (poly ϖ e) :=
  (poly_isEisensteinAt hϖ he).irreducible (maximalIdeal.isMaximal O).isPrime
    (poly_monic he).isPrimitive (by rw [poly_natDegree]; exact he)

/-- `O[Y] ⧸ (Y ^ e - ϖ)` is a domain. -/
theorem isDomain (hϖ : Irreducible ϖ) (he : 0 < e) : IsDomain (Ring ϖ e) :=
  AdjoinRoot.isDomain_of_prime (poly_irreducible hϖ he).prime

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- `Y ^ e = ϖ` in `O[Y] ⧸ (Y ^ e - ϖ)`. -/
lemma root_pow (ϖ : O) (e : ℕ) :
    AdjoinRoot.root (poly ϖ e) ^ e = algebraMap O (Ring ϖ e) ϖ := by
  have := AdjoinRoot.eval₂_root (poly ϖ e)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
  rw [this, AdjoinRoot.algebraMap_eq]

variable (ϖ e) in
omit [IsDiscreteValuationRing O] in
lemma algebraMap_injective (he : 0 < e) : Function.Injective (algebraMap O (Ring ϖ e)) := by
  rw [AdjoinRoot.algebraMap_eq]
  refine AdjoinRoot.of.injective_of_degree_ne_zero ?_
  rw [degree_X_pow_sub_C he]
  exact_mod_cast he.ne'

omit [IsDomain O] [IsDiscreteValuationRing O] in
lemma finite (he : 0 < e) : Module.Finite O (Ring ϖ e) := (poly_monic he).finite_adjoinRoot

/-- Every maximal ideal of `O[Y] ⧸ (Y ^ e - ϖ)` contains `Y`. -/
lemma root_mem_of_isMaximal (hϖ : Irreducible ϖ) (he : 0 < e) (M : Ideal (Ring ϖ e))
    [M.IsMaximal] : AdjoinRoot.root (poly ϖ e) ∈ M := by
  have := finite (ϖ := ϖ) he
  have hM : M.comap (algebraMap O (Ring ϖ e)) = maximalIdeal O :=
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) M
    eq_maximalIdeal this
  have hϖM : algebraMap O (Ring ϖ e) ϖ ∈ M := by
    rw [← Ideal.mem_comap, hM, mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ.not_isUnit
  rw [← root_pow] at hϖM
  exact (inferInstance : M.IsMaximal).isPrime.mem_of_pow_mem e hϖM

/-- An element of `O[Y] ⧸ (Y ^ e - ϖ)` is a non-unit iff it is divisible by `Y`. -/
lemma not_isUnit_iff_mem_span (hϖ : Irreducible ϖ) (he : 0 < e) (x : Ring ϖ e) :
    ¬ IsUnit x ↔ x ∈ Ideal.span {AdjoinRoot.root (poly ϖ e)} := by
  have := isDomain hϖ he
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨h, hh⟩ := X_dvd_sub_C (p := g)
    have hg : AdjoinRoot.mk (poly ϖ e) g = algebraMap O (Ring ϖ e) (g.coeff 0) +
        AdjoinRoot.root (poly ϖ e) * AdjoinRoot.mk (poly ϖ e) h := by
      rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X, ← map_mul, ← map_add,
        ← hh, add_sub_cancel]
    by_cases h0 : IsUnit (g.coeff 0)
    · exfalso
      obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits hx
      have hr := root_mem_of_isMaximal hϖ he M
      rw [hg] at hxM
      have : algebraMap O (Ring ϖ e) (g.coeff 0) ∈ M := by
        have := M.sub_mem hxM (M.mul_mem_right (AdjoinRoot.mk (poly ϖ e) h) hr)
        rwa [add_sub_cancel_right] at this
      exact hM.ne_top (M.eq_top_of_isUnit_mem this (h0.map _))
    · have hmax : maximalIdeal O = Ideal.span {ϖ} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
      have : g.coeff 0 ∈ Ideal.span {ϖ} := by rw [← hmax]; exact h0
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 this
      rw [hg, hc, map_mul, ← root_pow, Ideal.mem_span_singleton]
      refine ⟨AdjoinRoot.root (poly ϖ e) ^ (e - 1) * algebraMap O (Ring ϖ e) c +
        AdjoinRoot.mk (poly ϖ e) h, ?_⟩
      rw [mul_add, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]
  · intro hx hu
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (Ring ϖ e)
    have hr := root_mem_of_isMaximal hϖ he M
    have : x ∈ M := (Ideal.span_singleton_le_iff_mem M).2 hr hx
    exact hM.ne_top (M.eq_top_of_isUnit_mem this hu)

/-- `O[Y] ⧸ (Y ^ e - ϖ)` is a local ring. -/
theorem isLocalRing (hϖ : Irreducible ϖ) (he : 0 < e) : IsLocalRing (Ring ϖ e) := by
  have := isDomain hϖ he
  refine .of_nonunits_add fun a b ha hb ↦ ?_
  rw [mem_nonunits_iff, not_isUnit_iff_mem_span hϖ he] at ha hb ⊢
  exact Ideal.add_mem _ ha hb

/-- **Adjoining a root of a uniformizer.** `O[Y] ⧸ (Y ^ e - ϖ)` is a discrete valuation ring. -/
theorem isDiscreteValuationRing (hϖ : Irreducible ϖ) (he : 0 < e) :
    letI := isDomain hϖ he
    IsDiscreteValuationRing (Ring ϖ e) := by
  letI := isDomain hϖ he
  letI := isLocalRing hϖ he
  have hmax : maximalIdeal (Ring ϖ e) = Ideal.span {AdjoinRoot.root (poly ϖ e)} := by
    ext x
    rw [mem_maximalIdeal, mem_nonunits_iff, not_isUnit_iff_mem_span hϖ he]
  have hr0 : AdjoinRoot.root (poly ϖ e) ≠ 0 := by
    intro h
    have h1 := root_pow ϖ e
    rw [h, zero_pow he.ne', eq_comm, map_eq_zero_iff _ (algebraMap_injective ϖ e he)] at h1
    exact hϖ.ne_zero h1
  have hpid : IsPrincipalIdealRing (Ring ϖ e) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Ring ϖ e)).out 4 0).mp (by rw [hmax]; exact ⟨_, rfl⟩)
  exact { not_a_field' := by rw [hmax]; simpa using hr0 }

/-- The maximal ideal of `O[Y] ⧸ (Y ^ e - ϖ)` is generated by `Y`. -/
theorem maximalIdeal_eq (hϖ : Irreducible ϖ) (he : 0 < e) :
    letI := isLocalRing hϖ he
    maximalIdeal (Ring ϖ e) = Ideal.span {AdjoinRoot.root (poly ϖ e)} := by
  letI := isLocalRing hϖ he
  ext x
  rw [mem_maximalIdeal, mem_nonunits_iff, not_isUnit_iff_mem_span hϖ he]

/-- `Y` is a uniformizer of `O[Y] ⧸ (Y ^ e - ϖ)`. -/
theorem irreducible_root (hϖ : Irreducible ϖ) (he : 0 < e) :
    Irreducible (AdjoinRoot.root (poly ϖ e)) := by
  letI := isDomain hϖ he
  letI := isDiscreteValuationRing hϖ he
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  exact maximalIdeal_eq hϖ he

omit [IsDiscreteValuationRing O] in
/-- `O → O[Y] ⧸ (Y ^ e - ϖ)` is a local homomorphism (it is finite and injective). -/
theorem isLocalHom (he : 0 < e) : IsLocalHom (algebraMap O (Ring ϖ e)) := by
  have := finite (ϖ := ϖ) he
  have := (faithfulSMul_iff_algebraMap_injective O (Ring ϖ e)).2 (algebraMap_injective ϖ e he)
  exact Algebra.IsIntegral.isLocalHom _ _

/-- `O[Y] ⧸ (Y ^ e - ϖ)` is totally ramified over `O`: the residue field of `O` maps onto its
residue field. -/
theorem residueField_surjective (hϖ : Irreducible ϖ) (he : 0 < e) :
    letI := isLocalRing hϖ he
    haveI := isLocalHom (ϖ := ϖ) he
    Function.Surjective (algebraMap (ResidueField O) (ResidueField (Ring ϖ e))) := by
  letI := isLocalRing hϖ he
  haveI := isLocalHom (ϖ := ϖ) he
  intro x
  obtain ⟨x, rfl⟩ := residue_surjective x
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨h, hh⟩ := X_dvd_sub_C (p := g)
  refine ⟨residue O (g.coeff 0), ?_⟩
  rw [ResidueField.algebraMap_residue, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    maximalIdeal_eq hϖ he, Ideal.mem_span_singleton, AdjoinRoot.algebraMap_eq,
    ← AdjoinRoot.mk_C, ← map_sub, hh, map_mul, AdjoinRoot.mk_X]
  exact dvd_mul_right _ _

/-- For a prime `𝔓` of an `O`-algebra `B` lying over the maximal ideal of `O`, with `B_𝔓` a DVR,
the ramification index `e(𝔓 | O)` (Mathlib's `Ideal.ramificationIdx`, the length of
`B_𝔓 ⧸ ϖ B_𝔓`) is the valuation of `ϖ` in `B_𝔓`. -/
theorem ramificationIdx_eq_addVal {B : Type*} [CommRing B] [Algebra O B] (𝔓 : Ideal B)
    [𝔓.IsPrime] [IsDomain (Localization.AtPrime 𝔓)]
    [IsDiscreteValuationRing (Localization.AtPrime 𝔓)]
    (hϖ : Irreducible ϖ) (h𝔓 : 𝔓.under O = maximalIdeal O)
    (h0 : algebraMap O (Localization.AtPrime 𝔓) ϖ ≠ 0) :
    (𝔓.ramificationIdx O : ℕ∞) =
      IsDiscreteValuationRing.addVal (Localization.AtPrime 𝔓) (algebraMap O _ ϖ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔓)
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  rw [hk, IsDiscreteValuationRing.addVal_def' u hπ k, Ideal.ramificationIdx_def, h𝔓,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
    Set.image_singleton, hk, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_coe]

end RootOfUniformizer

end SemistableReduction
