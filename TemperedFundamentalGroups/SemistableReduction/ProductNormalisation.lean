/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Normalisation in a finite product of rings (MR12 S5.7, item 3)

An element of a finite product `Π i, L i` of `T`-algebras is integral over `T` iff all its
components are (`isIntegral_pi_iff`; the `⇐` direction uses that `Pi.single i y` is a root of
`X · p` for a monic `p` with `p(y) = 0`). Hence, if `B` is the integral closure of `T` in `A` and
`A ≃ Π i, L i`, the image of `B` in each factor `L j` is the integral closure of `T` in `L j`
(**`IsIntegralClosure.pi_factor`**), and `B` is the product of these images. For a reduced
artinian `A` (e.g. `O' ⊗_O L`, finite étale over a field) the factors are the residue fields
`A ⧸ m` (**`IsIntegralClosure.quotient_maximal`**, through `IsArtinianRing.equivPi`).

In S5.7 the normalisations `O' ⊗_O B_i` of the base-changed Tate charts `T_i'` in `O' ⊗_O L`
(`TateTwoChart.isIntegralClosure_baseChangeT0/T1`) thus give the normalisations of `T_i'` in
each factor field of `O' ⊗_O L`, to which S5/S6 apply.
-/

open Polynomial

namespace SemistableReduction

section Pi

variable {R : Type*} [CommRing R] {ι : Type*} {L : ι → Type*} [∀ i, CommRing (L i)]
  [∀ i, Algebra R (L i)]

/-- `Pi.single i y` is integral if `y` is: it is a root of `X · p` for `p(y) = 0`. -/
lemma isIntegral_pi_single [DecidableEq ι] {i : ι} {y : L i} (hy : IsIntegral R y) :
    IsIntegral R (Pi.single i y : Π j, L j) := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨X * p, monic_X.mul hp, ?_⟩
  rw [← aeval_def, map_mul, aeval_X]
  funext j
  have key : (aeval (Pi.single i y : Π j, L j) p) j = aeval ((Pi.single i y : Π j, L j) j) p :=
    (aeval_algHom_apply (Pi.evalAlgHom R L j) _ p).symm
  rw [Pi.mul_apply, key, Pi.zero_apply]
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, aeval_def, hpy, mul_zero]
  · rw [Pi.single_eq_of_ne hj, zero_mul]

/-- **Integrality in a finite product is componentwise.** -/
theorem isIntegral_pi_iff [Finite ι] {x : Π i, L i} :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  classical
  haveI := Fintype.ofFinite ι
  refine ⟨fun h i ↦ h.map (Pi.evalAlgHom R L i), fun h ↦ ?_⟩
  rw [← Finset.univ_sum_single x]
  exact IsIntegral.sum _ fun i _ ↦ isIntegral_pi_single (h i)

end Pi

namespace IsIntegralClosure

variable {T B A : Type*} [CommRing T] [CommRing B] [CommRing A] [Algebra T B] [Algebra T A]
  [Algebra B A] [IsScalarTower T B A]

/-- The image of `B` in the `j`-th factor of `A ≃ Π i, L i`, as a `T`-subalgebra. -/
abbrev factorRange {ι : Type*} {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra T (L i)]
    (e : A ≃ₐ[T] Π i, L i) (j : ι) : Subalgebra T (L j) :=
  (((Pi.evalAlgHom T L j).comp e.toAlgHom).comp (IsScalarTower.toAlgHom T B A)).range

/-- **The normalisation in a factor of a finite product**: if `B` is the integral closure of `T`
in `A ≃ Π i, L i`, then the image of `B` in `L j` is the integral closure of `T` in `L j`. -/
theorem factorRange_eq [IsIntegralClosure B T A] {ι : Type*} [Finite ι] {L : ι → Type*}
    [∀ i, CommRing (L i)] [∀ i, Algebra T (L i)] (e : A ≃ₐ[T] Π i, L i) (j : ι) :
    factorRange (B := B) e j = integralClosure T (L j) := by
  classical
  ext x
  rw [mem_integralClosure_iff]
  constructor
  · rintro ⟨b, rfl⟩
    exact (((IsIntegralClosure.isIntegral_iff (A := B)).2 ⟨b, rfl⟩).map e.toAlgHom).map
      (Pi.evalAlgHom T L j)
  · intro hx
    have h1 : IsIntegral T (e.symm (Pi.single j x)) :=
      (isIntegral_pi_single (R := T) (L := L) hx).map e.symm.toAlgHom
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).1 h1
    refine ⟨b, ?_⟩
    change (e (algebraMap B A b)) j = x
    rw [hb, AlgEquiv.apply_symm_apply, Pi.single_eq_same]

/-- **`IsIntegralClosure` of a factor**: the image of `B` in `L j` is the integral closure of `T`
in `L j`. -/
theorem pi_factor [IsIntegralClosure B T A] {ι : Type*} [Finite ι] {L : ι → Type*}
    [∀ i, CommRing (L i)] [∀ i, Algebra T (L i)] (e : A ≃ₐ[T] Π i, L i) (j : ι) :
    IsIntegralClosure (factorRange (B := B) e j) T (L j) := by
  rw [factorRange_eq e j]
  infer_instance

/-- The image of `B` in a residue field `A ⧸ m`, as a `T`-subalgebra. -/
abbrev quotientRange (m : Ideal A) : Subalgebra T (A ⧸ m) :=
  ((Ideal.Quotient.mkₐ T m).comp (IsScalarTower.toAlgHom T B A)).range

/-- **The normalisation in a residue field of a reduced artinian ring**: if `B` is the integral
closure of `T` in a reduced artinian ring `A` (e.g. a finite étale algebra over a field), then
the image of `B` in `A ⧸ m` (`m` maximal) is the integral closure of `T` in `A ⧸ m`. -/
theorem quotientRange_eq [IsIntegralClosure B T A] [IsArtinianRing A] [IsReduced A]
    (m : MaximalSpectrum A) :
    quotientRange (B := B) (T := T) m.asIdeal = integralClosure T (A ⧸ m.asIdeal) := by
  rw [← factorRange_eq (B := B) ((IsArtinianRing.equivPi A).restrictScalars T) m]
  rfl

/-- **`IsIntegralClosure` of a residue field of a reduced artinian ring.** -/
theorem quotient_maximal [IsIntegralClosure B T A] [IsArtinianRing A] [IsReduced A]
    (m : MaximalSpectrum A) :
    IsIntegralClosure (quotientRange (B := B) (T := T) m.asIdeal) T (A ⧸ m.asIdeal) := by
  rw [quotientRange_eq m]
  infer_instance

/-- **The normalisation in a field quotient of a reduced artinian ring**: if `B` is the integral
closure of `T` in a reduced artinian ring `A` and `f : A → F` is a surjective map onto a field,
then the image of `B` in `F` is the integral closure of `T` in `F`. -/
theorem range_eq_of_surjective [IsIntegralClosure B T A] [IsArtinianRing A] [IsReduced A]
    {F : Type*} [Field F] [Algebra T F] (f : A →ₐ[T] F) (hf : Function.Surjective f) :
    (f.comp (IsScalarTower.toAlgHom T B A)).range = integralClosure T F := by
  have hm : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let g : (A ⧸ RingHom.ker f) ≃ₐ[T] F := Ideal.quotientKerAlgEquivOfSurjective hf
  have h := quotientRange_eq (B := B) (T := T) ⟨RingHom.ker f, hm⟩
  rw [← integralClosure_map_algEquiv g, ← h, quotientRange, ← AlgHom.range_comp]
  rfl

/-- **`IsIntegralClosure` of a field quotient of a reduced artinian ring.** -/
theorem of_surjective [IsIntegralClosure B T A] [IsArtinianRing A] [IsReduced A]
    {F : Type*} [Field F] [Algebra T F] (f : A →ₐ[T] F) (hf : Function.Surjective f) :
    IsIntegralClosure (f.comp (IsScalarTower.toAlgHom T B A)).range T F := by
  rw [range_eq_of_surjective f hf]
  infer_instance

end IsIntegralClosure

/-- **Normalisation in a field quotient of a reduced artinian ring** (no normalisation `B`
needed): the image of the integral closure of `T` in `A` under a surjection `f : A → F` onto a
field is the integral closure of `T` in `F`. -/
theorem map_integralClosure_eq_of_surjective {T A : Type*} [CommRing T] [CommRing A]
    [Algebra T A] [IsArtinianRing A] [IsReduced A] {F : Type*} [Field F] [Algebra T F]
    (f : A →ₐ[T] F) (hf : Function.Surjective f) :
    (integralClosure T A).map f = integralClosure T F := by
  rw [← IsIntegralClosure.range_eq_of_surjective (B := integralClosure T A) f hf,
    AlgHom.range_comp]
  congr 1
  exact (Subalgebra.range_val _).symm

end SemistableReduction
