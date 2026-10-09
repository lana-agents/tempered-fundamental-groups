/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeLocalRing
import TemperedFundamentalGroups.SemistableReduction.LocalModel

/-!
# At smooth points `ϖ` is prime (Blueprint §10.3.8, CrossingX1, CX4)

* `isPrime_span_of_etale_polynomial`: if `A` is étale-locally `O[X]` at a prime `𝔭 ∋ ϖ`, then
  `ϖ` generates a prime ideal of `A_𝔭` (`(O ⧸ ϖ)[X]` is a normal domain, so `ϖ` generates a
  prime of the étale local ring, `isPrime_map_localization_of_etale`, and this descends along the
  faithfully flat `A_𝔭 → C_𝔮`);
* `eq_unit_mul_pow_of_prime`: in a domain where `ϖ` is prime, every divisor of a power of `ϖ` is a
  unit times a power of `ϖ`.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

/-- `O[X] ⧸ (ϖ) ≅ (O ⧸ ϖ)[X]` is a normal domain. -/
lemma quotient_polynomial_normal (hϖ : Irreducible ϖ) :
    IsDomain (O[X] ⧸ Ideal.span {C ϖ}) ∧ IsIntegrallyClosed (O[X] ⧸ Ideal.span {C ϖ}) := by
  haveI hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  have hI : (Ideal.span {ϖ}).map (C : O →+* O[X]) = Ideal.span {C ϖ} := by
    rw [Ideal.map_span, Set.image_singleton]
  let e := (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {ϖ})).trans
    (Ideal.quotEquivOfEq hI)
  exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e⟩

/-- **At an étale-local `O[X]` point, `ϖ` is prime.** -/
theorem isPrime_span_of_etale_polynomial (hϖ : Irreducible ϖ) {A : Type u} [CommRing A]
    [Algebra O A] (𝔭 : Ideal A) [𝔭.IsPrime] (hϖ𝔭 : algebraMap O A ϖ ∈ 𝔭)
    (h : IsEtaleLocallyAt O O[X] 𝔭) :
    (Ideal.span {algebraMap O (Localization.AtPrime 𝔭) ϖ}).IsPrime := by
  obtain ⟨C', _, g, f, 𝔮, hg, hf, h𝔮, hc, hO⟩ := h
  letI : Algebra A C' := g.toAlgebra
  letI : Algebra O[X] C' := f.toAlgebra
  haveI : Algebra.Etale A C' := RingHom.etale_algebraMap.mp hg
  haveI : Algebra.Etale O[X] C' := RingHom.etale_algebraMap.mp hf
  haveI := h𝔮
  obtain ⟨hdom, hic⟩ := quotient_polynomial_normal hϖ
  set I : Ideal O[X] := Ideal.span {C ϖ}
  have hfg : f (C ϖ) = g (algebraMap O A ϖ) := by
    have := congrArg (· ϖ) hO
    simpa using this
  have hI : I.map (algebraMap O[X] C') ≤ 𝔮 := by
    rw [Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
    change f (C ϖ) ∈ 𝔮
    rw [hfg, ← Ideal.mem_comap]
    change _ ∈ 𝔮.comap (algebraMap A C')
    rw [show 𝔮.comap (algebraMap A C') = 𝔭 from hc]
    exact hϖ𝔭
  obtain ⟨hprime, -⟩ := isPrime_map_localization_of_etale I 𝔮 hI
  let D := Localization.AtPrime 𝔭
  let E := Localization.AtPrime 𝔮
  have hc' : 𝔭 = 𝔮.comap (algebraMap A C') := hc.symm
  let φ : D →+* E := Localization.localRingHom 𝔭 𝔮 (algebraMap A C') hc'
  letI : Algebra D E := φ.toAlgebra
  haveI : Module.Flat D E := by
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) 𝔮 𝔭 hc'
  haveI : IsLocalHom (algebraMap D E) := Localization.isLocalHom_localRingHom _ _ _ _
  haveI : Module.FaithfullyFlat D E := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hmap : (Ideal.span {algebraMap O D ϖ}).map (algebraMap D E) =
      I.map (algebraMap O[X] E) := by
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    congr 2
    change φ (algebraMap O D ϖ) = algebraMap O[X] E (C ϖ)
    rw [IsScalarTower.algebraMap_apply O A D, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply O[X] C' E]
    change _ = algebraMap C' E (f (C ϖ))
    rw [hfg]
    rfl
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (Ideal.span {algebraMap O D ϖ}) (B := E),
    hmap]
  exact Ideal.comap_isPrime _ _

/-- **Divisors of powers of a prime.** In a domain where `p` is a prime element, every divisor
of `p ^ m` is a unit times a power of `p`. -/
theorem eq_unit_mul_pow_of_prime {R : Type*} [CommRing R] [IsDomain R] {p : R} (hp : Prime p)
    {t r : R} {m : ℕ} (h : t * r = p ^ m) : ∃ (ε : Rˣ) (α : ℕ), t = ε * p ^ α := by
  induction m generalizing t r with
  | zero =>
    rw [pow_zero] at h
    exact ⟨(isUnit_iff_exists_inv.2 ⟨r, h⟩).unit, 0, by simp⟩
  | succ m ih =>
    have hdvd : p ∣ t * r := ⟨p ^ m, by rw [h, pow_succ, mul_comm]⟩
    rcases hp.dvd_or_dvd hdvd with ⟨t', rfl⟩ | ⟨r', rfl⟩
    · have h' : t' * r = p ^ m := by
        apply mul_left_cancel₀ hp.ne_zero
        rw [← mul_assoc, h, pow_succ, mul_comm]
      obtain ⟨ε, α, rfl⟩ := ih h'
      exact ⟨ε, α + 1, by ring⟩
    · have h' : t * r' = p ^ m := by
        apply mul_left_cancel₀ hp.ne_zero
        rw [mul_left_comm, h, pow_succ, mul_comm]
      exact ih h'

end SemistableReduction
