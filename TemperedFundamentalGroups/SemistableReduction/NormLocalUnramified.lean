/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Unramifiedness of a normalisation passes to its localisation at a prime

Let `A` be a ring, `L` a field over `A` (with `A → L` injective), `𝔪` a prime of `A` with
localisation `Aₘ = A_𝔪`, `B = integralClosure A L` and `Bₘ = integralClosure Aₘ L`. Then `Bₘ` is the
localisation of `B` at the image of `A ∖ 𝔪` (`NormLocal.isLocalization`, Mathlib's
`IsLocalization.integralClosure`), and (**`NormLocal.isUnramifiedAt`**) if `B` is unramified over
`A` at every prime lying over a prime strictly contained in `𝔪`, then `Bₘ` is unramified over `Aₘ`
on the punctured spectrum of `Aₘ`: the hypothesis `hunr` of the local Kummer theorems
(`TateTwoChartNode.isTameKummerAt_NR`) from a global hypothesis on the normalisation.
-/

universe u

open IsLocalRing

namespace SemistableReduction

namespace NormLocal

noncomputable section

variable {A : Type u} [CommRing A] {L : Type u} [Field L] [Algebra A L]
  (𝔪 : Ideal A) [𝔪.IsPrime]

local notation "Aₘ" => Localization.AtPrime 𝔪

/-- `A_𝔪 → L` for an injective `A → L` into a field. -/
abbrev algAtPrime (hinj : Function.Injective (algebraMap A L)) : Algebra Aₘ L :=
  (IsLocalization.lift (M := 𝔪.primeCompl) (S := Aₘ) (g := algebraMap A L) fun y ↦
    IsUnit.mk0 _ fun h0 ↦ y.2 ((map_eq_zero_iff _ hinj).1 h0 ▸ 𝔪.zero_mem)).toAlgebra

lemma isScalarTower_algAtPrime (hinj : Function.Injective (algebraMap A L)) :
    letI := algAtPrime 𝔪 hinj
    IsScalarTower A Aₘ L :=
  letI := algAtPrime 𝔪 hinj
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

variable [Algebra (Localization.AtPrime 𝔪) L] [IsScalarTower A (Localization.AtPrime 𝔪) L]

/-- `integralClosure A L → integralClosure A_𝔪 L`. -/
def toLoc : integralClosure A L →+* integralClosure Aₘ L :=
  (integralClosure A L).val.toRingHom.codRestrict (integralClosure Aₘ L).toSubring
    fun x ↦ (x.2 : IsIntegral A x.1).tower_top

/-- The algebra structure of `integralClosure A_𝔪 L` over `integralClosure A L`. -/
abbrev algLoc : Algebra (integralClosure A L) (integralClosure Aₘ L) := (toLoc 𝔪).toAlgebra

attribute [local instance] algLoc

instance : IsScalarTower (integralClosure A L) (integralClosure Aₘ L) L :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance : IsScalarTower A (integralClosure A L) (integralClosure Aₘ L) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

omit [Algebra (Localization.AtPrime 𝔪) L] [IsScalarTower A (Localization.AtPrime 𝔪) L] in
lemma isLocalization_self (hinj : Function.Injective (algebraMap A L)) :
    IsLocalization (Algebra.algebraMapSubmonoid L 𝔪.primeCompl) L :=
  IsLocalization.self fun _ ⟨_, hs, hs'⟩ ↦ hs' ▸ (IsUnit.mk0 _ fun h0 ↦ hs
    ((map_eq_zero_iff _ hinj).1 h0 ▸ 𝔪.zero_mem))

variable {𝔪}

/-- **The normalisation of `A_𝔪` is the localisation of the normalisation of `A`.** -/
theorem isLocalization (hinj : Function.Injective (algebraMap A L)) :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) 𝔪.primeCompl)
      (integralClosure Aₘ L) :=
  haveI := isLocalization_self 𝔪 hinj
  IsLocalization.integralClosure (S := L) (Rf := Aₘ) (Sf := L) 𝔪.primeCompl

omit [Algebra (Localization.AtPrime 𝔪) L] [IsScalarTower A (Localization.AtPrime 𝔪) L] in
/-- A prime of `A_𝔪` other than the maximal ideal lies over a prime strictly inside `𝔪`. -/
lemma comap_lt (P : Ideal Aₘ) [P.IsPrime] (hP : P ≠ maximalIdeal Aₘ) :
    P.comap (algebraMap A Aₘ) < 𝔪 := by
  have h1 : P.comap (algebraMap A Aₘ) ≤ 𝔪 := by
    have := Ideal.comap_mono (f := algebraMap A Aₘ)
      (le_maximalIdeal (Ideal.IsPrime.ne_top ‹P.IsPrime›))
    rwa [show Ideal.comap (algebraMap A Aₘ) (maximalIdeal Aₘ) = 𝔪 from
      IsLocalization.AtPrime.under_maximalIdeal Aₘ 𝔪] at this
  refine lt_of_le_of_ne h1 fun h ↦ hP ?_
  calc P = Ideal.map (algebraMap A Aₘ) (P.comap (algebraMap A Aₘ)) :=
        (IsLocalization.map_under (M := 𝔪.primeCompl) (J := P)).symm
    _ = Ideal.map (algebraMap A Aₘ) 𝔪 := by rw [h]
    _ = maximalIdeal Aₘ := IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 Aₘ

/-- **Unramifiedness passes to the localised normalisation.** -/
theorem isUnramifiedAt (hinj : Function.Injective (algebraMap A L))
    (hunr : ∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime],
      Q.comap (algebraMap A (integralClosure A L)) < 𝔪 → Algebra.IsUnramifiedAt A Q)
    (Q : Ideal (integralClosure Aₘ L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap Aₘ (integralClosure Aₘ L)) ≠ maximalIdeal Aₘ) :
    Algebra.IsUnramifiedAt Aₘ Q := by
  haveI := isLocalization hinj (𝔪 := 𝔪)
  have hPA : (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))).comap
      (algebraMap A (integralClosure A L)) < 𝔪 := by
    have := comap_lt (Q.comap (algebraMap Aₘ (integralClosure Aₘ L))) hQ
    rwa [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq A (integralClosure A L) (integralClosure Aₘ L),
      ← Ideal.comap_comap] at this
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime
      (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L)))) := hunr _ hPA
  haveI : IsLocalization.AtPrime (Localization.AtPrime Q)
      (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) 𝔪.primeCompl) (Localization.AtPrime Q) Q
  let e := IsLocalization.algEquiv
    (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))).primeCompl
    (Localization.AtPrime (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))))
    (Localization.AtPrime Q)
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars A)
  exact Algebra.FormallyUnramified.of_restrictScalars A Aₘ (Localization.AtPrime Q)

end

end NormLocal

end SemistableReduction
