/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Galois extensions of degree prime to the residue characteristic are tame (T2, step S0)

The tameness hypothesis `htame` of Abhyankar's lemma (`SemistableReduction.Abhyankar.etale`:
every prime `𝔓` over the maximal ideal has ramification index dividing `e` and separable residue
field extension) holds for a Galois extension whose group has order prime to the residue
characteristic, with `e = |G|` ([Mzk1] §3.13 uses Abhyankar's lemma for the normalisation in a
covering of degree `d` with `d! ∈ A^×`; for a Galois covering of degree prime to `p` it suffices
that `|G|` is prime to `p`):

* **`Field.isSeparable_of_coprime_finrank`**: a finite extension whose degree is prime to the
  exponential characteristic is separable (the inseparable degree is a power of it and divides
  the degree: `Field.finInsepDegree_eq_pow`, `Field.finSepDegree_mul_finInsepDegree`);
* **`Ideal.ramificationIdx_dvd_card`**, **`Ideal.isSeparable_of_coprime_card`**: in a Galois
  extension `B / A` with group `G` (`IsGaloisGroup G A B`, `B` finite flat over `A`), for a
  maximal ideal `p` of `A` and a prime `P` over it, `e(P/p) ∣ |G|`, and if `|G|` is prime to the
  exponential characteristic of `A/p`, then `B/P` is separable over `A/p` (fundamental identity
  `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`);
* **`Ideal.tame_of_coprime_card`**: over a local `A`, exactly the hypothesis `htame` of
  `Abhyankar.etale` with `e = |G|`, and **`Ideal.isUnit_card_of_coprime`**: `|G|` is a unit in `A`
  (the hypothesis `he`).
-/

open Module

namespace Field

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- **A finite extension of degree prime to the exponential characteristic is separable.** -/
theorem isSeparable_of_coprime_finrank (q : ℕ) [ExpChar F q] (hq : (finrank F E).Coprime q) :
    Algebra.IsSeparable F E := by
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow F E q
  have hd : finInsepDegree F E ∣ finrank F E :=
    ⟨finSepDegree F E, by rw [← finSepDegree_mul_finInsepDegree, mul_comm]⟩
  have h1 : finInsepDegree F E = 1 := by
    rw [hn] at hd ⊢
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n hq.symm) hd
  exact (isSeparable_iff_finInsepDegree_eq_one F E).2 h1

end Field

namespace Ideal

variable {A : Type*} [CommRing A] [IsDomain A]
  (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Flat A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  (P : Ideal B) [P.IsPrime]

include G in
/-- **The ramification index divides the order of the Galois group.** -/
theorem ramificationIdx_dvd_card (p : Ideal A) [p.IsMaximal] [P.LiesOver p] :
    P.ramificationIdx A ∣ Nat.card G := by
  rw [← ramificationIdxIn_eq_ramificationIdx p P G,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]
  exact ⟨(primesOver p B).ncard * inertiaDegIn p B, by ring⟩

include G in
/-- **The inertia degree divides the order of the Galois group.** -/
theorem inertiaDeg_dvd_card (p : Ideal A) [p.IsMaximal] [P.LiesOver p] :
    P.inertiaDeg A ∣ Nat.card G := by
  rw [← inertiaDegIn_eq_inertiaDeg p P G,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]
  exact ⟨(primesOver p B).ncard * ramificationIdxIn p B, by ring⟩

include G in
/-- **Tame Galois extensions have separable residue field extensions**: if `|G|` is prime to the
exponential characteristic `q` of `A/p`, then `B/P` is separable over `A/p`. -/
theorem isSeparable_of_coprime_card (p : Ideal A) [p.IsMaximal] [P.LiesOver p] (q : ℕ)
    [ExpChar (A ⧸ p) q]
    (hq : (Nat.card G).Coprime q) : Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  haveI : FiniteDimensional (A ⧸ p) (B ⧸ P) := inferInstance
  refine Field.isSeparable_of_coprime_finrank (A ⧸ p) (B ⧸ P) q ?_
  have h := inertiaDeg_dvd_card B G P p
  rw [inertiaDeg_eq_of_isMaximal p P] at h
  exact Nat.Coprime.coprime_dvd_left h hq

/-- A positive natural number prime to the exponential characteristic of a field is nonzero
in it. -/
theorem natCast_ne_zero_of_coprime {k : Type*} [Field k] {n : ℕ} (hn : n ≠ 0)
    (hq : n.Coprime (ringExpChar k)) : (n : k) ≠ 0 := by
  intro h
  have hd : ringChar k ∣ n := (CharP.cast_eq_zero_iff k (ringChar k) n).1 h
  rcases Nat.eq_zero_or_pos (ringChar k) with h0 | hpos
  · rw [h0, zero_dvd_iff] at hd
    exact hn hd
  have he : ringExpChar k = ringChar k := max_eq_left hpos
  have h1 : ringChar k ∣ 1 := by
    rw [← hq]
    exact Nat.dvd_gcd hd (he ▸ dvd_rfl)
  exact CharP.ringChar_ne_one (Nat.dvd_one.1 h1)

omit [IsDomain A] [Group G] in
/-- **`|G|` is a unit** in a local ring whose residue field has exponential characteristic prime
to `|G|` (the hypothesis `he` of `Abhyankar.etale` for `e = |G|`). -/
theorem isUnit_card_of_coprime [IsLocalRing A] [Nonempty G]
    (hq : (Nat.card G).Coprime (ringExpChar (IsLocalRing.ResidueField A))) :
    IsUnit ((Nat.card G : ℕ) : A) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
  exact natCast_ne_zero_of_coprime Nat.card_pos.ne' hq

include G in
/-- **The tameness hypothesis of Abhyankar's lemma for a Galois extension of order prime to the
residue characteristic** (`htame` of `Abhyankar.etale` with `e = |G|`). -/
theorem tame_of_coprime_card [IsLocalRing A]
    (hq : (Nat.card G).Coprime (ringExpChar (A ⧸ IsLocalRing.maximalIdeal A))) :
    ∀ (P : Ideal B) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal A)],
      P.ramificationIdx A ∣ Nat.card G ∧
        Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) := fun P _ _ ↦
  ⟨ramificationIdx_dvd_card B G P (IsLocalRing.maximalIdeal A),
    isSeparable_of_coprime_card B G P (IsLocalRing.maximalIdeal A)
      (ringExpChar (A ⧸ IsLocalRing.maximalIdeal A)) hq⟩

end Ideal
