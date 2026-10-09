/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Local rings of étale algebras over normal domains are domains (W7, S9)

Blueprint §9.9, S9. Let `R` be an integrally closed domain with fraction field `K` and `A` an
étale `R`-algebra. Then every local ring `A_Q` is a domain (`isDomain_localization_of_etale`).

Proof. Put `D = A_Q`. Smooth base change commutes with integral closure (Mathlib,
`TensorProduct.toIntegralClosure_bijective_of_smooth`, and its localization and tower forms), so
the integral closure of `D` in `D ⊗_R K` is `D ⊗_R (integralClosure R K) = D ⊗_R R = D`. Hence
every idempotent of `D ⊗_R K` comes from an idempotent of the local ring `D` (`D → D ⊗_R K` is
injective, `D` being `R`-flat), so it is `0` or `1`. On the other hand `K ⊗_R D` is formally
unramified and essentially of finite type over the field `K`, hence reduced and finite, hence
artinian and reduced, i.e. a finite product of fields; with only trivial idempotents it is a
field. So `D ⊆ K ⊗_R D` is a domain.
-/

open Algebra TensorProduct

namespace SemistableReduction

/-- An artinian reduced ring without nontrivial idempotents is a field. -/
theorem isField_of_isArtinianRing_of_isReduced {T : Type*} [CommRing T] [Nontrivial T]
    [IsArtinianRing T] [IsReduced T] (h : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField T := by
  have hloc : IsLocalRing T := by
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨m, hm⟩ := Ideal.exists_maximal T
    refine ⟨m, hm, fun m' hm' ↦ ?_⟩
    by_contra hne
    classical
    let φ := IsArtinianRing.equivPi T
    let e : T := φ.symm (Pi.single ⟨m, hm⟩ 1)
    have he : IsIdempotentElem e := by
      change e * e = e
      rw [← map_mul]
      congr 1
      rw [← Pi.single_mul, one_mul]
    have hne' : (⟨m', hm'⟩ : MaximalSpectrum T) ≠ ⟨m, hm⟩ := fun h ↦ hne (congrArg (·.1) h)
    have h₁ : φ e ⟨m, hm⟩ = 1 := by simp [e]
    have h₂ : φ e ⟨m', hm'⟩ = 0 := by simp [e, hne']
    rcases h e he with h0 | h1
    · rw [h0, map_zero] at h₁
      exact zero_ne_one (α := T ⧸ m) h₁
    · rw [h1, map_one] at h₂
      haveI : Nontrivial (T ⧸ m') := Ideal.Quotient.nontrivial_iff.mpr hm'.ne_top
      exact one_ne_zero (α := T ⧸ m') h₂
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing T

/-- Idempotents of a local ring are trivial. -/
theorem eq_zero_or_one_of_isIdempotentElem {T : Type*} [CommRing T] [IsLocalRing T] {e : T}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    obtain ⟨u, rfl⟩ := h
    have : (u : T) * u = u * 1 := by rw [mul_one]; exact he.eq
    exact u.isUnit.mul_left_cancel this
  · left
    have : (1 - e) * e = (1 - e) * 0 := by rw [mul_zero, sub_mul, one_mul, he.eq, sub_self]
    exact h.mul_left_cancel this

variable {R A : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A]
  [Algebra R A] [Algebra.Etale R A] (Q : Ideal A) [Q.IsPrime]

local notation "D" => Localization.AtPrime Q
local notation "K" => FractionRing R

omit [IsDomain R] in
/-- Elements of `D ⊗_R K` integral over `D` come from `D`. -/
theorem exists_eq_tmul_one_of_isIntegral {e : D ⊗[R] K} (he : IsIntegral D e) :
    ∃ d : D, d ⊗ₜ[R] (1 : K) = e := by
  have H : Function.Bijective (TensorProduct.toIntegralClosure R A K) :=
    TensorProduct.toIntegralClosure_bijective_of_smooth
  have H' : Function.Bijective (TensorProduct.toIntegralClosure A D (A ⊗[R] K)) :=
    TensorProduct.toIntegralClosure_bijective_of_isLocalization Q.primeCompl
  have Hb := TensorProduct.toIntegralClosure_bijective_of_tower (B := K) H H'
  obtain ⟨t, ht⟩ := Hb.2 ⟨e, he⟩
  have ht' : (Algebra.TensorProduct.map (AlgHom.id D D) (integralClosure R K).val) t = e :=
    congrArg Subtype.val ht
  rw [← ht']
  clear ht ht' Hb H H'
  induction t with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add]⟩
  | tmul d k =>
    have hk : (k : K) ∈ (⊥ : Subalgebra R K) := by
      rw [← IsIntegrallyClosed.integralClosure_eq_bot R K]
      exact k.2
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hk
    refine ⟨r • d, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

omit [IsDomain R] [IsIntegrallyClosed R] in
lemma includeLeft_injective_fractionRing [IsDomain R] :
    Function.Injective (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] K) :=
  Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R K)

variable (R) in
include R in
/-- **The generic fibre of a local ring of an étale algebra over a normal domain is a field**:
`D ⊗_R K` is a field. -/
theorem isField_tensor_fractionRing : IsField (D ⊗[R] K) := by
  have hinj := includeLeft_injective_fractionRing (R := R) Q
  -- idempotents of `D ⊗_R K` are trivial
  have hidem : ∀ e : D ⊗[R] K, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    have hint : IsIntegral D e := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub (by simp)
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, sq, Polynomial.eval₂_mul]
        rw [he.eq, sub_self]
    obtain ⟨d, rfl⟩ := exists_eq_tmul_one_of_isIntegral Q hint
    have hd : IsIdempotentElem d := by
      apply hinj
      change (d * d) ⊗ₜ[R] (1 : K) = d ⊗ₜ[R] (1 : K)
      rw [← he.eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rcases eq_zero_or_one_of_isIdempotentElem hd with h | h
    · left; rw [h, TensorProduct.zero_tmul]
    · right; rw [h]; rfl
  -- transport to `K ⊗_R D`, a `K`-algebra
  let φ : D ⊗[R] K ≃ₐ[R] K ⊗[R] D := Algebra.TensorProduct.comm R D K
  have hidem' : ∀ e : K ⊗[R] D, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    rcases hidem (φ.symm e) (he.map φ.symm) with h | h
    · left; simpa using congrArg φ h
    · right; simpa using congrArg φ h
  haveI : IsReduced (K ⊗[R] D) := Algebra.FormallyUnramified.isReduced_of_field K _
  haveI : Module.Finite K (K ⊗[R] D) := by
    haveI : Module.Free K (K ⊗[R] D) := Module.Free.of_divisionRing K _
    exact Algebra.FormallyUnramified.finite_of_free K _
  haveI : IsArtinianRing (K ⊗[R] D) := IsArtinianRing.of_finite K _
  haveI : Nontrivial (K ⊗[R] D) := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have := congrArg φ.symm h
    rw [map_zero, map_one] at this
    exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact this))
  exact MulEquiv.isField (isField_of_isArtinianRing_of_isReduced hidem') φ.toRingEquiv.toMulEquiv

variable (R) in
include R in
/-- **Local rings of étale algebras over normal domains are domains.** -/
theorem isDomain_localization_of_etale : IsDomain (Localization.AtPrime Q) := by
  letI := (isField_tensor_fractionRing R Q).toField
  exact (includeLeft_injective_fractionRing (R := R) Q).isDomain _

variable (R) in
include R in
/-- **Every nonzero element of `D` divides a nonzero constant.** -/
theorem exists_dvd_algebraMap {a : D} (ha : a ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ a ∣ algebraMap R D r := by
  have hinj := includeLeft_injective_fractionRing (R := R) Q
  have hF := isField_tensor_fractionRing R Q
  have ha' : algebraMap D (D ⊗[R] K) a ≠ 0 := fun h ↦ ha (hinj (by
    rw [map_zero]; exact h))
  obtain ⟨z, hz⟩ := hF.mul_inv_cancel ha'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D (nonZeroDivisors R)) (D ⊗[R] K) :=
    IsLocalization.tensor (S := D) K (nonZeroDivisors R)
  obtain ⟨⟨d, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid D (nonZeroDivisors R)) z
  obtain ⟨r, hr, hrs⟩ := s.2
  refine ⟨r, nonZeroDivisors.ne_zero hr, d, hinj ?_⟩
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, one_mul] at hz
  change algebraMap D (D ⊗[R] K) _ = algebraMap D (D ⊗[R] K) _
  rw [hz, ← hrs, ← IsScalarTower.algebraMap_apply]

end SemistableReduction
