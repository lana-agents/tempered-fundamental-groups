/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Reduced special fibre ⇒ integrally closed in the generic fibre (Blueprint §12.8, M2.5)

Let `A` be a commutative ring and `π ∈ A` such that `A ⧸ (π)` is reduced. If `A → L` is injective
and `π` is a nonzerodivisor on `L`, then every `x ∈ L` which is integral over `A` and satisfies
`πᵏ x ∈ A` for some `k` lies in `A` (`ReducedFibreNormal.exists_eq_of_isIntegral`).

Proof: if `π x = a` with `x` integral of degree `n`, scaling the equation of `x` by `πⁿ` gives
`aⁿ ∈ (π)`, so `a = π b` (reducedness), and `x = b` since `π` is regular on `L`; induct on `k`.

Consequences:
* `isIntegrallyClosedIn_of_away`: for `π` a nonzerodivisor of `A` with `A/(π)` reduced, `A` is
  integrally closed in `A[1/π]` — a model over a DVR with reduced special fibre is integrally
  closed in its generic fibre;
* `isIntegralClosure_of_away`: if moreover `A` is integral over `T`, then `A` is the integral
  closure of `T` in `A[1/π]` — the "normalised model" of M2.5 (`T` the chart ring of the base model,
  `A` the chart ring of the covering);
* `isIntegrallyClosedIn_of_isIntegrallyClosedIn_away`: if `A[1/π]` is integrally closed in an
  `A[1/π]`-algebra `K` on which `A` acts injectively and `π` is regular, so is `A`;
  `isIntegrallyClosed_of_away`: for a domain `A`, `π ≠ 0`, `A/(π)` reduced and `A[1/π]` normal,
  `A` is normal (flat model over a DVR, normal generic fibre, reduced special fibre).

For the reducedness of the special fibre: `isReduced_of_away` — a ring on which `f` is a
nonzerodivisor is reduced if its localization away from `f` is (e.g. an admissible covering `C`
of a chart, `f` the equation of the nodes and marked points: `C_f` is étale over the smooth
`R_f`, hence reduced).
-/

open Polynomial

namespace SemistableReduction

namespace ReducedFibreNormal

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra A L] {π : A}

/-- The scaled minimal equation of `π x` reduces to `Xⁿ` modulo `π`. -/
lemma map_scaleRoots_eq {p : A[X]} (hp : p.Monic) :
    (p.scaleRoots π).map (Ideal.Quotient.mk (Ideal.span {π})) = X ^ p.natDegree := by
  ext i
  rw [coeff_map, coeff_scaleRoots, coeff_X_pow, map_mul, map_pow,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π)]
  rcases lt_trichotomy i p.natDegree with h | h | h
  · rw [if_neg h.ne, zero_pow (Nat.sub_ne_zero_of_lt h), mul_zero]
  · subst h
    rw [if_pos rfl, hp.coeff_natDegree, Nat.sub_self, pow_zero, mul_one, map_one]
  · rw [if_neg h.ne', coeff_eq_zero_of_natDegree_lt h, map_zero, zero_mul]

variable (hinj : Function.Injective (algebraMap A L))
  (hπ : ∀ y : L, algebraMap A L π * y = 0 → y = 0) (hred : IsReduced (A ⧸ Ideal.span {π}))
include hinj hπ hred

/-- The step `k = 1`: an integral `x` with `π x ∈ A` lies in `A`. -/
lemma exists_eq_of_isIntegral_of_mul {x : L} (hx : IsIntegral A x) {a : A}
    (ha : algebraMap A L π * x = algebraMap A L a) : ∃ b, algebraMap A L b = x := by
  obtain ⟨p, hp, hpx⟩ := hx
  have h0 : aeval (algebraMap A L a) (p.scaleRoots π) = 0 := by
    rw [← ha]; exact scaleRoots_aeval_eq_zero hpx
  have h1 : eval a (p.scaleRoots π) = 0 := by
    apply hinj
    rw [map_zero, ← h0, aeval_algebraMap_apply, ← coe_aeval_eq_eval]
  have h2 : (Ideal.Quotient.mk (Ideal.span {π}) a) ^ p.natDegree = 0 := by
    have := congrArg (Ideal.Quotient.mk (Ideal.span {π})) h1
    rwa [map_zero, ← eval_map_apply, map_scaleRoots_eq hp, eval_pow, eval_X] at this
  have h3 : Ideal.Quotient.mk (Ideal.span {π}) a = 0 := IsReduced.eq_zero _ ⟨_, h2⟩
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h3)
  refine ⟨b, (sub_eq_zero.1 (hπ _ ?_)).symm⟩
  rw [mul_sub, ha, map_mul, mul_comm, sub_self]

/-- **An integral element `x` with `πᵏ x ∈ A` lies in `A`**, if `A/(π)` is reduced, `A → L` is
injective and `π` is regular on `L`. -/
theorem exists_eq_of_isIntegral {x : L} (hx : IsIntegral A x) :
    ∀ (k : ℕ) (a : A), algebraMap A L π ^ k * x = algebraMap A L a →
      ∃ b, algebraMap A L b = x := by
  intro k
  induction k generalizing x with
  | zero => exact fun a ha ↦ ⟨a, by rw [← ha, pow_zero, one_mul]⟩
  | succ k ih =>
    intro a ha
    have hx' : IsIntegral A (algebraMap A L π ^ k * x) :=
      (isIntegral_algebraMap.pow k).mul hx
    obtain ⟨b, hb⟩ := exists_eq_of_isIntegral_of_mul hinj hπ hred hx'
      (a := a) (by rw [← ha, pow_succ']; ring)
    exact ih hx b hb.symm

end ReducedFibreNormal

open ReducedFibreNormal

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra A L] (π : A)

/-- **A ring with reduced special fibre is integrally closed in its generic fibre**: for `π` a
nonzerodivisor of `A` with `A/(π)` reduced, `A` is integrally closed in `A[1/π]`. -/
theorem isIntegrallyClosedIn_of_away [IsLocalization.Away π L] (hπ : π ∈ nonZeroDivisors A)
    (hred : IsReduced (A ⧸ Ideal.span {π})) : IsIntegrallyClosedIn A L := by
  have hle : Submonoid.powers π ≤ nonZeroDivisors A := Submonoid.powers_le.2 hπ
  have hinj : Function.Injective (algebraMap A L) := IsLocalization.injective L hle
  have hu : IsUnit (algebraMap A L π) := IsLocalization.Away.algebraMap_isUnit π
  have hreg : ∀ y : L, algebraMap A L π * y = 0 → y = 0 := fun y hy ↦ by
    rwa [hu.mul_right_eq_zero] at hy
  refine isIntegrallyClosedIn_iff.2 ⟨hinj, fun {x} hx ↦ ?_⟩
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers π) x
  refine exists_eq_of_isIntegral hinj hreg hred hx k a ?_
  rw [mul_comm, ← map_pow]
  exact h

/-- **The normalised model** (M2.5): if `A` is integral over `T` (e.g. finite over the chart ring
`T` of the base model), `π` is a nonzerodivisor of `A` and `A/(π)` is reduced, then `A` is the
integral closure of `T` in `A[1/π]`. -/
theorem isIntegralClosure_of_away {T : Type*} [CommRing T] [Algebra T A] [Algebra T L]
    [IsScalarTower T A L] [Algebra.IsIntegral T A] [IsLocalization.Away π L]
    (hπ : π ∈ nonZeroDivisors A) (hred : IsReduced (A ⧸ Ideal.span {π})) :
    IsIntegralClosure A T L := by
  have h := isIntegrallyClosedIn_of_away (L := L) π hπ hred
  refine ⟨h.algebraMap_injective, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · exact (isIntegrallyClosedIn_iff.1 h).2 (hx.tower_top (A := A))
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := T) y).map (IsScalarTower.toAlgHom T A L)

/-- **Normality from the generic fibre and a reduced special fibre**: if `A[1/π]` is integrally
closed in `K` (e.g. its total ring of fractions), `A → K` is injective and `π` is regular on `K`,
and `A/(π)` is reduced, then `A` is integrally closed in `K`. -/
theorem isIntegrallyClosedIn_of_isIntegrallyClosedIn_away {K : Type*} [CommRing K] [Algebra A K]
    [Algebra L K] [IsScalarTower A L K] [IsLocalization.Away π L]
    (hinj : Function.Injective (algebraMap A K))
    (hreg : ∀ y : K, algebraMap A K π * y = 0 → y = 0)
    (hred : IsReduced (A ⧸ Ideal.span {π})) (hL : IsIntegrallyClosedIn L K) :
    IsIntegrallyClosedIn A K := by
  refine isIntegrallyClosedIn_iff.2 ⟨hinj, fun {x} hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := (isIntegrallyClosedIn_iff.1 hL).2 (hx.tower_top (A := L))
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers π) y
  refine exists_eq_of_isIntegral hinj hreg hred hx k a ?_
  rw [IsScalarTower.algebraMap_apply A L K, IsScalarTower.algebraMap_apply A L K a, ← map_pow,
    ← map_mul, mul_comm, ← map_pow]
  exact congrArg _ h

/-- **A domain with normal generic fibre and reduced special fibre is normal**: `A` a domain,
`π ≠ 0`, `A/(π)` reduced and `A[1/π]` integrally closed. -/
theorem isIntegrallyClosed_of_away [IsDomain A] [IsLocalization.Away π L] (hπ : π ≠ 0)
    (hred : IsReduced (A ⧸ Ideal.span {π})) [IsIntegrallyClosed L] : IsIntegrallyClosed A := by
  let K := FractionRing A
  have hle : Submonoid.powers π ≤ nonZeroDivisors A :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero hπ)
  let g : L →+* K := IsLocalization.map _ (T := nonZeroDivisors A) (RingHom.id A) hle
  letI := g.toAlgebra
  haveI : IsScalarTower A L K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  haveI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers π) L K
  have hL : IsIntegrallyClosedIn L K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).1 ‹_›
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  refine (isIntegrallyClosed_iff_isIntegrallyClosedIn K).2
    (isIntegrallyClosedIn_of_isIntegrallyClosedIn_away π hinj (fun y hy ↦ ?_) hred hL)
  have hπK : algebraMap A K π ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap A K)]; exact fun h ↦ hπ (hinj h)
  exact (mul_eq_zero.1 hy).resolve_left hπK

/-- **Reducedness away from a nonzerodivisor suffices.** -/
theorem isReduced_of_away {f : A} [IsLocalization.Away f L] (hf : f ∈ nonZeroDivisors A)
    [IsReduced L] : IsReduced A :=
  isReduced_of_injective (algebraMap A L)
    (IsLocalization.injective L (Submonoid.powers_le.2 hf))

end SemistableReduction
