/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# A local criterion for integral closedness

* **`isIntegrallyClosed_of_prime_of_mul_mem`**: a domain `B` with a prime element `x` is
  integrally closed if every element `f` of the fraction field integral over `B` has a multiple
  `xⁿ f ∈ B`. (If `g` is integral with `x g = b ∈ B`, then `b` is a root of the monic
  `scaleRoots p x`, which is `Xᵈ` modulo `x`, so `x ∣ b` and `g ∈ B`; induct on `n`.)
* **`isIntegrallyClosed_atPrime_of_away`**: for a domain `A`, a prime `P`, `x ≠ 0` with
  `A[1/x]` integrally closed and `x ∉ P` or `x` prime in `A_P`, the local ring `A_P` is
  integrally closed.
* **`isIntegrallyClosed_of_cover`**: a domain `A` is integrally closed if at every maximal
  ideal `P` there is such an `x`.
-/

open Polynomial
open scoped nonZeroDivisors

namespace SemistableReduction

namespace NormalLocal

section Prime

variable {B : Type*} [CommRing B] {K : Type*} [Field K] [Algebra B K]
  [IsFractionRing B K]

/-- If `g` is integral over `B`, `x` is prime and `x g ∈ B`, then `g ∈ B`. -/
lemma exists_eq_of_prime_mul_eq {x : B} (hx : Prime x) {g : K} (hg : IsIntegral B g) {b : B}
    (hb : algebraMap B K x * g = algebraMap B K b) : ∃ c : B, algebraMap B K c = g := by
  obtain ⟨p, hpm, hp⟩ := hg
  have h1 : aeval (algebraMap B K x * g) (p.scaleRoots x) = 0 :=
    scaleRoots_aeval_eq_zero (p := p) (a := g) (r := x) (by rwa [aeval_def])
  rw [hb, aeval_algebraMap_apply_eq_algebraMap_eval] at h1
  have h2 : (p.scaleRoots x).eval b = 0 := IsFractionRing.injective B K (by rw [h1, map_zero])
  let I := Ideal.span {x}
  haveI : I.IsPrime := (Ideal.span_singleton_prime hx.ne_zero).mpr hx
  have hmk : Ideal.Quotient.mk I x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have h3 : (p.scaleRoots x).map (Ideal.Quotient.mk I) =
      X ^ (p.map (Ideal.Quotient.mk I)).natDegree := by
    rw [map_scaleRoots _ _ _ (by rw [hpm.leadingCoeff, map_one]; exact one_ne_zero), hmk,
      scaleRoots_zero, (hpm.map _).leadingCoeff, one_smul]
  have h4 : Ideal.Quotient.mk I b ^ (p.map (Ideal.Quotient.mk I)).natDegree = 0 := by
    have := congrArg (Ideal.Quotient.mk I) h2
    rw [map_zero, ← eval₂_hom, ← eval_map, h3, eval_pow, eval_X] at this
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (pow_eq_zero_iff'.mp h4).1)
  refine ⟨c, ?_⟩
  have hx0 : algebraMap B K x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hx.ne_zero
  apply mul_left_cancel₀ hx0
  rw [hb, ← hc, map_mul, mul_comm]

/-- **A domain with a prime element `x` is integrally closed if every integral element `f` of
the fraction field has a multiple `xⁿ f ∈ B`.** -/
theorem isIntegrallyClosed_of_prime_of_mul_mem {x : B} (hx : Prime x)
    (h : ∀ f : K, IsIntegral B f → ∃ n : ℕ, ∃ b : B,
      algebraMap B K (x ^ n) * f = algebraMap B K b) :
    IsIntegrallyClosed B := by
  rw [isIntegrallyClosed_iff K]
  intro f hf
  obtain ⟨n, b, hb⟩ := h f hf
  induction n generalizing b with
  | zero => exact ⟨b, by rw [← hb, pow_zero, map_one, one_mul]⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := exists_eq_of_prime_mul_eq hx
      ((isIntegral_algebraMap (x := x ^ n)).mul hf) (b := b)
      (by rw [← hb, pow_succ', map_mul, mul_assoc])
    exact ih c hc.symm

end Prime

section Local

variable {A : Type*} [CommRing A] [IsDomain A]

/-- If a localization `S = M⁻¹ A` (`M` without zero) is integrally closed, every element of a
fraction field integral over `A` has a multiple by an element of `M` in `A`. -/
lemma exists_mul_eq_of_isLocalization (M : Submonoid A) (hM : M ≤ A⁰) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization M S] [IsIntegrallyClosed S] {K : Type*} [Field K] [Algebra A K]
    [IsFractionRing A K] {f : K} (hf : IsIntegral A f) :
    ∃ m ∈ M, ∃ r : A, algebraMap A K m * f = algebraMap A K r := by
  let g : S →+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  letI := g.toAlgebra
  have : IsScalarTower A S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp ‹_› (hf.tower_top (A := S))
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  refine ⟨m, m.2, r, ?_⟩
  rw [← hy, RingHom.algebraMap_toAlgebra]
  simp only [g, IsLocalization.map_mk', RingHom.id_apply]
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, map_mul]
  exact mul_comm _ _

/-- **Local criterion at a prime**: if `x ≠ 0`, `A[1/x]` is integrally closed and either
`x ∉ P` or `x` is prime in `A_P`, then `A_P` is integrally closed. -/
theorem isIntegrallyClosed_atPrime_of_away (P : Ideal A) [P.IsPrime] {x : A} (hx0 : x ≠ 0)
    (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.Away x R] [IsIntegrallyClosed R]
    (hx : x ∉ P ∨ Prime (algebraMap A (Localization.AtPrime P) x)) :
    IsIntegrallyClosed (Localization.AtPrime P) := by
  let L := Localization.AtPrime P
  let K := FractionRing A
  have hinj := IsFractionRing.injective A K
  have key : ∀ f : K, IsIntegral L f → ∃ s ∈ P.primeCompl, ∃ n : ℕ, ∃ r : A,
      algebraMap A K (x ^ n * s) * f = algebraMap A K r := by
    intro f hf
    obtain ⟨⟨s, hs⟩, hsf⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      P.primeCompl (Rₘ := L) f hf
    obtain ⟨_, ⟨n, rfl⟩, r, hr⟩ := exists_mul_eq_of_isLocalization (Submonoid.powers x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx0) R hsf
    refine ⟨s, hs, n, r, ?_⟩
    rw [← hr, Submonoid.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  have hne : ∀ s ∈ P.primeCompl, ∀ n : ℕ, algebraMap A K (x ^ n * s) ≠ 0 := fun s hs n ↦
    (map_ne_zero_iff _ hinj).mpr
      (mul_ne_zero (pow_ne_zero n hx0) (fun h0 ↦ hs (h0 ▸ P.zero_mem)))
  rcases hx with hx | hx
  · rw [isIntegrallyClosed_iff K]
    intro f hf
    obtain ⟨s, hs, n, r, h⟩ := key f hf
    have hm : x ^ n * s ∈ P.primeCompl :=
      P.primeCompl.mul_mem (P.primeCompl.pow_mem hx n) hs
    refine ⟨IsLocalization.mk' L r ⟨_, hm⟩, ?_⟩
    apply mul_left_cancel₀ (hne s hs n)
    rw [h, IsScalarTower.algebraMap_apply A L K (x ^ n * s), ← map_mul,
      show algebraMap A L (x ^ n * s) * IsLocalization.mk' L r ⟨_, hm⟩ = algebraMap A L r from
        IsLocalization.mk'_spec' L r ⟨_, hm⟩, ← IsScalarTower.algebraMap_apply]
  · refine isIntegrallyClosed_of_prime_of_mul_mem (K := K) hx fun f hf ↦ ?_
    obtain ⟨s, hs, n, r, h⟩ := key f hf
    refine ⟨n, IsLocalization.mk' L r ⟨s, hs⟩, ?_⟩
    have hs0 : algebraMap A K s ≠ 0 := by simpa using hne s hs 0
    apply mul_left_cancel₀ hs0
    rw [IsScalarTower.algebraMap_apply A L K s, ← map_mul,
      show algebraMap A L s * IsLocalization.mk' L r ⟨s, hs⟩ = algebraMap A L r from
        IsLocalization.mk'_spec' L r ⟨s, hs⟩]
    simp only [map_pow, ← IsScalarTower.algebraMap_apply]
    rw [← h, map_mul, map_pow]
    ring

/-- **Local criterion for integral closedness**: a domain `A` is integrally closed if at every
maximal ideal `P` there is `x ≠ 0` with `A[1/x]` integrally closed and either `x ∉ P` or `x`
prime in `A_P`. -/
theorem isIntegrallyClosed_of_cover
    (h : ∀ (P : Ideal A) [P.IsMaximal], ∃ x : A, x ≠ 0 ∧
      IsIntegrallyClosed (Localization.Away x) ∧
        (x ∉ P ∨ Prime (algebraMap A (Localization.AtPrime P) x))) :
    IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_localization_maximal fun P _ hP ↦ by
    obtain ⟨x, hx0, hR, hx⟩ := h P
    exact isIntegrallyClosed_atPrime_of_away P hx0 (Localization.Away x) hx

end Local

end NormalLocal

end SemistableReduction
