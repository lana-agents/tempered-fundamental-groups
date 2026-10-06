/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Smooth algebras over a field are normal and reduced

Let `S` be a smooth algebra over a field `k`.

* `SmoothNormal.dvd_of_smooth`: if `m ∈ S` is a nonzerodivisor and `a ∈ S` satisfies
  `a ^ n + ∑_{i < n} s_i a ^ i m ^ (n - i) = 0`, then `m ∣ a`;
* `SmoothNormal.isIntegrallyClosedIn_of_smooth`: `S` is integrally closed in every localization at
  nonzerodivisors (e.g. its total ring of fractions);
* `SmoothNormal.isIntegrallyClosed_of_smooth`: a smooth domain over a field is integrally closed;
* `SmoothNormal.isReduced_of_smooth`: `S` is reduced.

## Proof

For `T` étale over a normal domain `P` with fraction field `K`, `T' = T ⊗[P] K` is a localization
of `T` at nonzerodivisors (flatness), a finite product of fields (étale over `K`), hence every
nonzerodivisor of `T'` is a unit and `T'` is reduced; and `T` is integrally closed in `T'`
(`TensorProduct.toIntegralClosure_bijective_of_smooth`, since `P` is integrally closed in `K`).
Then `a / m ∈ T'` is integral over `T`, hence in `T` (`dvd_of_etale`), and `T ⊆ T'` is reduced
(`isReduced_of_etale`). In general, `S` is covered by `S_f` standard étale over `k[x₁, …, xₙ]`
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`).
-/

open Polynomial TensorProduct nonZeroDivisors

namespace TemperedFundamentalGroups.SmoothNormal

section Abstract

variable {T T' : Type*} [CommRing T] [CommRing T'] [Algebra T T']

/-- If `T` is integrally closed in `T'` and `m` becomes a unit in `T'`, then every `a` with
`a ^ n + ∑_{i < n} s_i a ^ i m ^ (n - i) = 0` is divisible by `m`. -/
theorem dvd_of_isIntegrallyClosedIn (hT : IsIntegrallyClosedIn T T') {m a : T}
    (hm : IsUnit (algebraMap T T' m)) {n : ℕ} (s : Fin n → T)
    (h : a ^ n + ∑ i : Fin n, s i * a ^ (i : ℕ) * m ^ (n - i) = 0) : m ∣ a := by
  obtain ⟨u, hu⟩ := hm
  set y : T' := algebraMap T T' a * ↑u⁻¹ with hy
  set p : T[X] := X ^ n + ∑ i : Fin n, C (s i) * X ^ (i : ℕ)
  have hp : p.Monic := monic_X_pow_add (degree_sum_fin_lt s)
  have hpy : aeval y p = 0 := by
    have key : aeval y p * (u : T') ^ n = algebraMap T T'
        (a ^ n + ∑ i : Fin n, s i * a ^ (i : ℕ) * m ^ (n - i)) := by
      simp only [p, map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, add_mul, Finset.sum_mul]
      congr 1
      · rw [← mul_pow, mul_assoc, Units.inv_mul, mul_one]
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← hu, ← pow_mul_pow_sub (u : T') i.2.le, hy, mul_pow]
        have : (↑u⁻¹ : T') ^ (i : ℕ) * (u : T') ^ (i : ℕ) = 1 := by
          rw [← mul_pow, Units.inv_mul, one_pow]
        linear_combination (algebraMap T T' (s i) * algebraMap T T' a ^ (i : ℕ) *
          (u : T') ^ (n - i)) * this
    rw [h, map_zero] at key
    exact (u.isUnit.pow n).mul_left_eq_zero.1 key
  obtain ⟨t, ht⟩ := (isIntegrallyClosedIn_iff.1 hT).2 ⟨p, hp, hpy⟩
  refine ⟨t, (isIntegrallyClosedIn_iff.1 hT).1 ?_⟩
  rw [map_mul, ht, hy, ← hu, mul_left_comm, Units.mul_inv, mul_one]

end Abstract

section Etale

variable {P T : Type*} [CommRing P] [IsDomain P] [CommRing T] [Algebra P T]

local notation "K" => FractionRing P

omit [IsDomain P] in
/-- The image of a nonzerodivisor of `P` in a flat `P`-algebra is a nonzerodivisor. -/
lemma algebraMapSubmonoid_le_nonZeroDivisors [Module.Flat P T] :
    Algebra.algebraMapSubmonoid T P⁰ ≤ T⁰ := by
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := T) hp
  simp only [Algebra.smul_def]
  rw [mul_comm, hx, mul_zero]

omit [IsDomain P] in
variable (P T) in
lemma injective_algebraMap_tensor [Module.Flat P T] :
    Function.Injective (algebraMap T (T ⊗[P] K)) :=
  IsLocalization.injective (M := Algebra.algebraMapSubmonoid T P⁰) _
    algebraMapSubmonoid_le_nonZeroDivisors

/-- `T ⊗[P] K` is étale over `K`, so its nonzerodivisors are units. -/
lemma isUnit_of_mem_nonZeroDivisors_tensor [Algebra.Etale P T] {x : T ⊗[P] K}
    (hx : x ∈ (T ⊗[P] K)⁰) : IsUnit x := by
  let e := Algebra.TensorProduct.comm P T K
  haveI : Module.Finite K (K ⊗[P] T) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[P] T)
  haveI : IsArtinianRing (K ⊗[P] T) := IsArtinianRing.of_finite K (K ⊗[P] T)
  have hex : e x ∈ (K ⊗[P] T)⁰ := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have h0 : e.symm y * x = 0 := by
      rw [← e.symm_apply_apply x, ← map_mul, hy, map_zero]
    have := (mem_nonZeroDivisors_iff_right.1 hx) (e.symm y) h0
    rw [← e.apply_symm_apply y, this, map_zero]
  have := (IsArtinianRing.isUnit_of_mem_nonZeroDivisors hex).map e.symm
  rwa [AlgEquiv.symm_apply_apply] at this

variable (P T) in
/-- `T ⊗[P] K` is étale over `K`, hence reduced. -/
lemma isReduced_tensor [Algebra.Etale P T] : IsReduced (T ⊗[P] K) := by
  haveI : IsReduced (K ⊗[P] T) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.TensorProduct.comm P T K) (AlgEquiv.injective _)

omit [IsDomain P] in
variable (P T) in
/-- A smooth algebra over an integrally closed domain `P` is integrally closed in its base change
to the fraction field of `P`. -/
lemma isIntegrallyClosedIn_tensor [IsIntegrallyClosed P] [Algebra.Smooth P T] :
    IsIntegrallyClosedIn T (T ⊗[P] K) := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨injective_algebraMap_tensor P T, fun {x} hx ↦ ?_⟩
  obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := T)
    (B := K)).2 ⟨x, hx⟩
  have hx' : x = (TensorProduct.toIntegralClosure P T K z).val := by rw [hz]
  rw [hx']
  clear hz hx' hx x
  induction z with
  | zero => exact ⟨0, by simp⟩
  | tmul t k =>
    obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.1 k.2
    refine ⟨p • t, ?_⟩
    simp only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val, ← hp,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add, Subalgebra.coe_add]⟩

/-- **The étale case.** For `T` étale over an integrally closed domain, a nonzerodivisor `m`
divides every `a` with `a ^ n + ∑_{i < n} s_i a ^ i m ^ (n - i) = 0`. -/
theorem dvd_of_etale [IsIntegrallyClosed P] [Algebra.Etale P T] {m a : T} (hm : m ∈ T⁰) {n : ℕ}
    (s : Fin n → T) (h : a ^ n + ∑ i : Fin n, s i * a ^ (i : ℕ) * m ^ (n - i) = 0) : m ∣ a :=
  dvd_of_isIntegrallyClosedIn (isIntegrallyClosedIn_tensor P T)
    (isUnit_of_mem_nonZeroDivisors_tensor
      (IsLocalization.nonZeroDivisors_le_comap (Algebra.algebraMapSubmonoid T P⁰) _ hm)) s h

variable (P T) in
/-- An étale algebra over a domain is reduced. -/
theorem isReduced_of_etale [Algebra.Etale P T] : IsReduced T :=
  haveI := isReduced_tensor P T
  isReduced_of_injective (algebraMap T (T ⊗[P] K)) (injective_algebraMap_tensor P T)

end Etale

section Smooth

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.Smooth k S]

variable (k) in
/-- Every maximal ideal of `S` avoids some `f` such that `S[1/f]` is étale over a polynomial ring
over `k`. -/
lemma exists_etale_away (𝔪 : Ideal S) [𝔪.IsMaximal] :
    ∃ f ∉ 𝔪, ∃ (n : ℕ) (_ : Algebra (MvPolynomial (Fin n) k) (Localization.Away f)),
      Algebra.Etale (MvPolynomial (Fin n) k) (Localization.Away f) := by
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k)
    (p := 𝔪)
  exact ⟨f, hf, n, _, inferInstance⟩

/-- An ideal containing a power of an element outside each maximal ideal is the unit ideal. -/
lemma eq_top_of_forall_maximal (I : Ideal S)
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → ∃ f ∉ 𝔪, ∃ j : ℕ, f ^ j ∈ I) : I = ⊤ := by
  by_contra hI
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨f, hf, j, hj⟩ := h 𝔪 h𝔪
  exact hf (h𝔪.isPrime.mem_of_pow_mem j (hI𝔪 hj))

variable (k) in
include k in
/-- **Smooth algebras over a field are normal.** If `m ∈ S` is a nonzerodivisor and
`a ^ n + ∑_{i < n} s_i a ^ i m ^ (n - i) = 0`, then `m ∣ a`. -/
theorem dvd_of_smooth {m a : S} (hm : m ∈ S⁰) {n : ℕ} (s : Fin n → S)
    (h : a ^ n + ∑ i : Fin n, s i * a ^ (i : ℕ) * m ^ (n - i) = 0) : m ∣ a := by
  have key : (Ideal.span {m}).colon (Ideal.span {a}) = ⊤ := by
    refine eq_top_of_forall_maximal _ fun 𝔪 _ ↦ ?_
    obtain ⟨f, hf, d, _, _⟩ := exists_etale_away k 𝔪
    have hm' : algebraMap S (Localization.Away f) m ∈ (Localization.Away f)⁰ :=
      IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers f) _ hm
    have h' : algebraMap S (Localization.Away f) a ^ n + ∑ i : Fin n,
        algebraMap S (Localization.Away f) (s i) * algebraMap S (Localization.Away f) a ^ (i : ℕ) *
          algebraMap S (Localization.Away f) m ^ (n - i) = 0 := by
      simpa using congrArg (algebraMap S (Localization.Away f)) h
    obtain ⟨x, hx⟩ := dvd_of_etale (P := MvPolynomial (Fin d) k) hm' _ h'
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
    simp only at hbc
    subst hbc
    have h2 : algebraMap S (Localization.Away f) (a * c) =
        algebraMap S (Localization.Away f) (m * b) := by
      rw [map_mul, map_mul, hx, mul_assoc, IsLocalization.mk'_spec]
    rw [IsLocalization.eq_iff_exists (Submonoid.powers f)] at h2
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := h2
    obtain ⟨_, l, rfl⟩ := c
    refine ⟨f, hf, j + l, ?_⟩
    rw [Submodule.mem_colon_span_singleton, Ideal.mem_span_singleton', smul_eq_mul]
    refine ⟨f ^ j * b, ?_⟩
    simp only at hj
    rw [pow_add]
    linear_combination -hj
  have h1 : (1 : S) ∈ (Ideal.span {m}).colon (Ideal.span {a}) := by rw [key]; trivial
  rw [Submodule.mem_colon_span_singleton, one_smul, Ideal.mem_span_singleton] at h1
  exact h1

variable (k S) in
include k in
/-- **Smooth algebras over a field are reduced.** -/
theorem isReduced_of_smooth : IsReduced S := by
  refine ⟨fun x hx ↦ ?_⟩
  have key : (⊥ : Ideal S).colon (Ideal.span {x}) = ⊤ := by
    refine eq_top_of_forall_maximal _ fun 𝔪 _ ↦ ?_
    obtain ⟨f, hf, d, _, _⟩ := exists_etale_away k 𝔪
    haveI := isReduced_of_etale (MvPolynomial (Fin d) k) (Localization.Away f)
    have h0 : algebraMap S (Localization.Away f) x = 0 := (hx.map _).eq_zero
    rw [← map_zero (algebraMap S (Localization.Away f)),
      IsLocalization.eq_iff_exists (Submonoid.powers f)] at h0
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := h0
    refine ⟨f, hf, j, ?_⟩
    rw [Submodule.mem_colon_span_singleton, smul_eq_mul, Ideal.mem_bot]
    simpa [mul_comm] using hj
  have h1 : (1 : S) ∈ (⊥ : Ideal S).colon (Ideal.span {x}) := by rw [key]; trivial
  rwa [Submodule.mem_colon_span_singleton, one_smul, Ideal.mem_bot] at h1

variable (k) in
include k in
/-- **Smooth algebras over a field are integrally closed in their localizations at
nonzerodivisors** (e.g. the total ring of fractions). -/
theorem isIntegrallyClosedIn_of_smooth {A : Type*} [CommRing A] [Algebra S A] (M : Submonoid S)
    [IsLocalization M A] (hM : M ≤ S⁰) : IsIntegrallyClosedIn S A := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨IsLocalization.injective A hM, fun {x} ⟨p, hp, hpx⟩ ↦ ?_⟩
  obtain ⟨⟨a, c⟩, hac⟩ := IsLocalization.mk'_surjective M x
  simp only at hac
  subst hac
  set n := p.natDegree
  set c' := algebraMap S A c
  have hy : IsLocalization.mk' A a c * c' = algebraMap S A a := IsLocalization.mk'_spec A a c
  -- clearing denominators: `a ^ n + ∑ p_i a ^ i c ^ (n - i) = 0` in `S`
  have h : a ^ n + ∑ i : Fin n, p.coeff i * a ^ (i : ℕ) * (c : S) ^ (n - i) = 0 := by
    apply IsLocalization.injective A hM
    have h1 : (aeval (IsLocalization.mk' A a c) p) * c' ^ n = algebraMap S A
        (a ^ n + ∑ i : Fin n, p.coeff i * a ^ (i : ℕ) * (c : S) ^ (n - i)) := by
      conv_lhs => rw [hp.as_sum]
      simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, add_mul, Finset.sum_mul]
      congr 1
      · rw [← mul_pow, hy]
      · rw [← Fin.sum_univ_eq_sum_range (fun i ↦ algebraMap S A (p.coeff i) *
          IsLocalization.mk' A a c ^ i * c' ^ n)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← pow_mul_pow_sub c' i.2.le, ← hy, mul_pow]
        ring
    rw [map_zero, ← h1, aeval_def, hpx, zero_mul]
  obtain ⟨t, ht⟩ := dvd_of_smooth k (hM c.2) _ h
  refine ⟨t, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ht, map_mul, mul_comm]

variable (k S) in
include k in
/-- **A smooth domain over a field is integrally closed.** -/
theorem isIntegrallyClosed_of_smooth [IsDomain S] : IsIntegrallyClosed S := by
  rw [isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S)]
  exact isIntegrallyClosedIn_of_smooth k S⁰ le_rfl

end Smooth

end TemperedFundamentalGroups.SmoothNormal
