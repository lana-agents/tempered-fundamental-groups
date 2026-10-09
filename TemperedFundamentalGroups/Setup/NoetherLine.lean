/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Noether normalization for one-dimensional algebras

A finitely generated algebra `R` of Krull dimension one over a field `K` is finite over a
polynomial ring in one variable: there is `x : R` such that `K[X] → R`, `X ↦ x` is finite.

The proof combines Mathlib's Noether normalization `exists_finite_inj_algHom_of_fg` with
the invariance of Krull dimension under injective integral extensions (going up and
incomparability), which we prove here in the form needed.
-/

universe u

open Polynomial

namespace TemperedFundamentalGroups.NoetherLine

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]

/-- Going up along an injective integral extension: every chain of primes of `A` lifts to a
chain of primes of `B` of the same length. -/
lemma exists_ltSeries_lift (hinj : Function.Injective (algebraMap A B))
    (l : LTSeries (PrimeSpectrum A)) :
    ∃ L : LTSeries (PrimeSpectrum B), L.length = l.length ∧
      L.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal := by
  induction l using RelSeries.inductionOn' with
  | singleton p =>
    have hbot : (⊥ : Ideal B).comap (algebraMap A B) ≤ p.asIdeal := by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le
    obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal ⊥ hbot
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, hQp⟩
  | snoc l q hlq ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    obtain ⟨Q, hLQ, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral q.asIdeal
      L.last.asIdeal (by rw [hlast]; exact le_of_lt hlq)
    have hlt : L.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hLQ fun h ↦ (ne_of_lt (show l.last < q from hlq)) ?_
      ext1
      rw [← hlast, ← hQq]
      exact congrArg (fun P : PrimeSpectrum B ↦ P.asIdeal.comap (algebraMap A B)) h
    exact ⟨L.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], by simpa using hQq⟩

lemma ringKrullDim_le_of_isIntegral (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim A ≤ ringKrullDim B := by
  refine iSup_le fun l ↦ ?_
  obtain ⟨L, hL, -⟩ := exists_ltSeries_lift hinj l
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

lemma ringKrullDim_le_of_isIntegral' : ringKrullDim B ≤ ringKrullDim A :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) fun _ _ h ↦
    Ideal.IsIntegral.comap_lt_comap (R := A) h

end TemperedFundamentalGroups.NoetherLine

open TemperedFundamentalGroups.NoetherLine in
/-- A finitely generated algebra of Krull dimension one over a field is finite over a polynomial
ring in one variable. -/
theorem exists_finite_aeval {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (hR : ringKrullDim R = 1) :
    ∃ x : R, (Polynomial.aeval (R := K) x).toRingHom.Finite := by
  have : Nontrivial R := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    simp [ringKrullDim_eq_bot_of_subsingleton] at hR
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K R
  algebraize [g.toRingHom]
  have : Module.Finite (MvPolynomial (Fin s) K) R := hfin
  have hint : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := inferInstance
  have h1 := ringKrullDim_le_of_isIntegral (A := MvPolynomial (Fin s) K) (B := R) hinj
  have h2 := ringKrullDim_le_of_isIntegral' (A := MvPolynomial (Fin s) K) (B := R)
  simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add, hR] at h1 h2
  obtain rfl : s = 1 := by
    have a : (s : WithBot ℕ∞) ≤ 1 := h1
    have b : (1 : WithBot ℕ∞) ≤ s := h2
    exact_mod_cast le_antisymm a b
  let e : K[X] ≃ₐ[K] MvPolynomial (Fin 1) K :=
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm
  refine ⟨g (e X), ?_⟩
  have : Polynomial.aeval (R := K) (g (e X)) = g.comp e.toAlgHom :=
    Polynomial.algHom_ext (by simp)
  rw [this]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.surjective)
