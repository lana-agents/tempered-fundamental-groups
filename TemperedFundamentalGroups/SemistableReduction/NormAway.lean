/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Normalisations and unramifiedness under a localization `A → A[1/a]`

Let `R = A[1/a]` and let `B₁` be the integral closure of `A` in a field `L` (`a ≠ 0` in `L`).

* **`NormAway.isIntegralClosure`**: `B = B₁[1/a]` is the integral closure of `R` in `L`;
* **`NormAway.isUnramifiedAt`**: if `B₁` is unramified over `A` at `Q ∩ B₁`, then `B` is
  unramified over `R` at `Q`;
* **`NormAway.hunr`**: the hypothesis "`B₁` is unramified over `A` at every prime lying over a
  prime strictly inside a maximal ideal containing `x`" passes to `B` over `R` (the hypothesis
  `hunr` of the special-fibre coverings, `TateTwoChartNode.covNR`);
* **`NormAway.quotMap`**, `quotMap_algebraMap`, **`isLocalization_quotMap`**: modulo an ideal
  `I` of `A`, `B/IB = (B₁/IB₁)[1/ā]` (the data `ι₀`, `hι₀`, `hι` of `NodeEtaleGlue.Special`).
-/

universe u

namespace SemistableReduction

namespace NormAway

section IntegralClosure

variable {A R L B₁ B : Type*} [CommRing A] [CommRing R] [Field L] [CommRing B₁] [CommRing B]
  [Algebra A R] [Algebra A L] [Algebra R L] [IsScalarTower A R L]
  [Algebra A B₁] [Algebra B₁ L] [IsScalarTower A B₁ L] [IsIntegralClosure B₁ A L]
  [Algebra B₁ B] [Algebra R B] [Algebra B L] [IsScalarTower B₁ B L] [IsScalarTower R B L]
  (a : A) [IsLocalization.Away a R] [IsLocalization.Away (algebraMap A B₁ a) B]

omit [Algebra R B] [IsScalarTower R B L] in
include a B₁ in
/-- **The normalisation of `A[1/a]` in `L` is the localization of the normalisation of `A`.** -/
theorem isIntegralClosure (ha : algebraMap A L a ≠ 0) : IsIntegralClosure B R L := by
  have hb : ∀ n : ℕ, algebraMap B₁ L (algebraMap A B₁ a ^ n) ≠ 0 := fun n ↦ by
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    exact pow_ne_zero _ ha
  have hinj₁ := IsIntegralClosure.algebraMap_injective B₁ A L
  refine ⟨?_, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A B₁ a)) y
    have h := congrArg (algebraMap B L) (IsLocalization.mk'_spec B b
      (⟨_, n, rfl⟩ : Submonoid.powers (algebraMap A B₁ a)))
    rw [map_mul, hy, zero_mul, ← IsScalarTower.algebraMap_apply,
      ← map_zero (algebraMap B₁ L)] at h
    obtain rfl := hinj₁ h.symm
    exact IsLocalization.mk'_zero _
  · obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers a) (Rₘ := R) x hx
    obtain ⟨b, hbx⟩ := (IsIntegralClosure.isIntegral_iff (A := B₁)).mp hm
    refine ⟨IsLocalization.mk' B b (⟨_, n, rfl⟩ : Submonoid.powers (algebraMap A B₁ a)), ?_⟩
    have h := congrArg (algebraMap B L) (IsLocalization.mk'_spec B b
      (⟨_, n, rfl⟩ : Submonoid.powers (algebraMap A B₁ a)))
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hbx,
      Submonoid.smul_def, Algebra.smul_def, map_pow, map_pow,
      ← IsScalarTower.algebraMap_apply] at h
    have hn : (algebraMap A L a) ^ n ≠ 0 := pow_ne_zero _ ha
    exact mul_right_cancel₀ hn (h.trans (mul_comm _ _))
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A B₁ a)) y
    have hinv : IsIntegral R (algebraMap R L (IsLocalization.Away.invSelf (S := R) a) ^ n) :=
      (isIntegral_algebraMap).pow n
    have hbI : IsIntegral R (algebraMap B₁ L b) :=
      ((IsIntegralClosure.isIntegral A L b).map (IsScalarTower.toAlgHom A B₁ L)).tower_top
    convert hinv.mul hbI using 1
    have h := congrArg (algebraMap B L) (IsLocalization.mk'_spec B b
      (⟨_, n, rfl⟩ : Submonoid.powers (algebraMap A B₁ a)))
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_pow,
      ← IsScalarTower.algebraMap_apply] at h
    have hu : algebraMap R L (IsLocalization.Away.invSelf (S := R) a) * algebraMap A L a = 1 := by
      rw [IsScalarTower.algebraMap_apply A R L, ← map_mul, mul_comm,
        IsLocalization.Away.mul_invSelf, map_one]
    calc algebraMap B L (IsLocalization.mk' B b
          (⟨_, n, rfl⟩ : Submonoid.powers (algebraMap A B₁ a)))
        = algebraMap B L (IsLocalization.mk' B b
          (⟨_, n, rfl⟩ : Submonoid.powers (algebraMap A B₁ a))) *
          (algebraMap R L (IsLocalization.Away.invSelf (S := R) a) * algebraMap A L a) ^ n := by
          rw [hu, one_pow, mul_one]
      _ = _ := by
        linear_combination (algebraMap R L (IsLocalization.Away.invSelf (S := R) a)) ^ n * h

end IntegralClosure

section Unramified

variable {A R B₁ B : Type*} [CommRing A] [CommRing R] [CommRing B₁] [CommRing B]
  [Algebra A R] [Algebra A B₁] [Algebra B₁ B] [Algebra R B] [Algebra A B]
  [IsScalarTower A R B] [IsScalarTower A B₁ B]
  (a : A) [IsLocalization.Away a R] [IsLocalization.Away (algebraMap A B₁ a) B]

omit [IsLocalization.Away a R] in
include a in
/-- **Unramifiedness passes to the localization**: if `B₁` is unramified over `A` at `Q ∩ B₁`,
then `B = B₁[1/a]` is unramified over `R = A[1/a]` at `Q`. -/
theorem isUnramifiedAt (Q : Ideal B) [Q.IsPrime]
    (h : Algebra.IsUnramifiedAt A (Q.comap (algebraMap B₁ B))) : Algebra.IsUnramifiedAt R Q := by
  haveI : IsScalarTower A B₁ (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply A B₁ B]
    rfl
  haveI : IsScalarTower A R (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply A R B, ← IsScalarTower.algebraMap_apply R B]
  haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.powers (algebraMap A B₁ a)) (Localization.AtPrime Q) Q
  let e := IsLocalization.algEquiv (Q.comap (algebraMap B₁ B)).primeCompl
    (Localization.AtPrime (Q.comap (algebraMap B₁ B))) (Localization.AtPrime Q)
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars A)
  exact Algebra.FormallyUnramified.of_restrictScalars A R (Localization.AtPrime Q)

include a B₁ in
/-- **The hypothesis `hunr` passes to the localization.** -/
theorem hunr (x : A)
    (h : ∀ (P : Ideal A) [P.IsMaximal], x ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
      Q.comap (algebraMap A B₁) < P → Algebra.IsUnramifiedAt A Q)
    (P : Ideal R) [P.IsMaximal] (hxP : algebraMap A R x ∈ P) (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R B) < P) : Algebra.IsUnramifiedAt R Q := by
  refine isUnramifiedAt (B₁ := B₁) a Q ?_
  have hP' : (P.comap (algebraMap A R)) ≠ ⊤ := (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›))
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal _ hP'
  refine h M (hPM hxP) _ (lt_of_lt_of_le ?_ hPM)
  have hc : (Q.comap (algebraMap B₁ B)).comap (algebraMap A B₁) =
      (Q.comap (algebraMap R B)).comap (algebraMap A R) := by
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  rw [hc]
  refine lt_of_le_of_ne (Ideal.comap_mono hQ.le) fun heq ↦ hQ.ne ?_
  haveI : (Q.comap (algebraMap R B)).IsPrime := Ideal.comap_isPrime _ _
  rw [← IsLocalization.map_under (Submonoid.powers a) R (Q.comap (algebraMap R B)),
    ← IsLocalization.map_under (Submonoid.powers a) R P]
  exact congrArg _ heq

end Unramified

section Quotient

variable {A R B₁ B : Type*} [CommRing A] [CommRing R] [CommRing B₁] [CommRing B]
  [Algebra A R] [Algebra A B₁] [Algebra B₁ B] [Algebra R B] [Algebra A B]
  [IsScalarTower A R B] [IsScalarTower A B₁ B]
  (I : Ideal A) (I' : Ideal R) (hI : I' = I.map (algebraMap A R))

include hI in
lemma map_le_comap : (I.map (algebraMap A B₁)) ≤
    (I'.map (algebraMap R B)).comap (algebraMap B₁ B) := by
  subst hI
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  exact Ideal.le_comap_map

/-- `B₁/IB₁ → B/IB`. -/
def quotMap : B₁ ⧸ I.map (algebraMap A B₁) →+* B ⧸ I'.map (algebraMap R B) :=
  Ideal.quotientMap _ (algebraMap B₁ B) (map_le_comap I I' hI)

lemma quotMap_mk (b : B₁) :
    quotMap I I' hI (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (algebraMap B₁ B b) :=
  Ideal.quotientMap_mk

include hI in
lemma le_comap_R : I ≤ I'.comap (algebraMap A R) := by
  subst hI; exact Ideal.le_comap_map

/-- `hι₀`: `quotMap` is compatible with the structure maps. -/
lemma quotMap_algebraMap (y : A ⧸ I) :
    quotMap I I' hI (algebraMap (A ⧸ I) (B₁ ⧸ I.map (algebraMap A B₁)) y) =
      algebraMap (R ⧸ I') (B ⧸ I'.map (algebraMap R B))
        (Ideal.quotientMap I' (algebraMap A R) (le_comap_R I I' hI) y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, quotMap_mk, Ideal.quotientMap_mk,
    Ideal.Quotient.algebraMap_quotient_map_quotient, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

variable (a : A) [IsLocalization.Away (algebraMap A B₁ a) B]

include a in
/-- **`B/IB = (B₁/IB₁)[1/ā]`** (`hι`). -/
theorem isLocalization_quotMap : letI := (quotMap (B₁ := B₁) (B := B) I I' hI).toAlgebra
    IsLocalization.Away (algebraMap (A ⧸ I) (B₁ ⧸ I.map (algebraMap A B₁))
      (Ideal.Quotient.mk I a)) (B ⧸ I'.map (algebraMap R B)) := by
  letI := (quotMap (B₁ := B₁) (B := B) I I' hI).toAlgebra
  have hIB : I'.map (algebraMap R B) = (I.map (algebraMap A B₁)).map (algebraMap B₁ B) := by
    rw [hI, Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have h := IsLocalization.of_surjective (M := Submonoid.powers (algebraMap A B₁ a)) (S := B)
    (R' := B₁ ⧸ I.map (algebraMap A B₁)) (S' := B ⧸ I'.map (algebraMap R B))
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
    (RingHom.ext fun x ↦ (quotMap_mk I I' hI x).symm) (by
      rw [Ideal.mk_ker, Ideal.mk_ker, hIB])
  rw [Submonoid.map_powers] at h
  rwa [Ideal.Quotient.algebraMap_quotient_map_quotient]

end Quotient

end NormAway

end SemistableReduction
