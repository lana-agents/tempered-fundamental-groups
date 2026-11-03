/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A DVR in a finite extension with the same residue field (generic; MR13 (f) step 3 (C))

Let `O` be a Dedekind domain with fraction field `K`, `ϖ ∈ O` with `(ϖ)` maximal and residue field
`O/(ϖ)` algebraically closed, and `E / K` a finite separable extension. Then there is a discrete
valuation ring `O'` with `O ⊆ O' ⊆ E` and a uniformizer `ϖ'` such that

* `O → O'/(ϖ')` is **surjective with kernel `(ϖ)`** (no residue field extension: the residue field
  of `O'` is algebraic over the algebraically closed `O/(ϖ)`), and
* `E = O'[1/ϖ']` (`IsLocalization.Away ϖ' E`).

`O'` is the localization of the integral closure of `O` in `E` (a Dedekind domain,
`integralClosure.isDedekindDomain`) at a maximal ideal over `(ϖ)`, realised as a subalgebra of `E`
(`Localization.subalgebra.ofField`). No completeness of `O` is used (with `O` complete, `O'` would
be the whole integral closure, but this is not needed).

This is the input (C) of MR13's (f) step 3: with it, `P1Three.connected_lift_tensor` applies to
every finite extension `E` of `K` (`FiniteExtensionDVR.elim`).
-/

universe u

open nonZeroDivisors

namespace SemistableReduction

namespace FiniteExtensionDVR

/-- A field of fractions of a discrete valuation ring is its localization away from a
uniformizer. -/
theorem isLocalization_away_of_irreducible {R F : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] {π : R}
    (hπ : Irreducible π) : IsLocalization.Away π F := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers π) R⁰ ?_ ?_).2 inferInstance
  · rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hπ.ne_zero)
  · intro x hx
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hx) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, ⟨↑v⁻¹, by rw [hv, mul_comm (v : R), mul_assoc, Units.mul_inv,
      mul_one]⟩⟩

variable {O : Type u} [CommRing O] [IsDedekindDomain O] {ϖ : O}
  {k : Type u} [Field k] [IsAlgClosed k] {θ : O →+* k} (hθ : Function.Surjective θ)
  (hker : RingHom.ker θ = Ideal.span {ϖ})

omit [IsDedekindDomain O] in
/-- The kernel of `O → O'/J` is the preimage of `J`. -/
lemma ker_algebraMap_quot {O' : Type*} [CommRing O'] [Algebra O O'] (J : Ideal O') :
    RingHom.ker (algebraMap O (O' ⧸ J)) = J.comap (algebraMap O O') := by
  rw [IsScalarTower.algebraMap_eq O O' (O' ⧸ J), ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq,
    Ideal.mk_ker]

omit [IsDedekindDomain O] in
include hθ hker in
/-- The localization step of `elim`: `O'` a localization of an integral extension `A` of `O` at a
maximal ideal `Q` over `(ϖ)`, with `A` Dedekind and `Q ≠ 0`. -/
theorem elim_aux (E : Type u) [Field E] [Algebra O E] (motive : Prop)
    (h : ∀ (O' : Type u) [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] [Algebra O O']
      (ϖ' : O'), ϖ' ≠ 0 → ¬IsUnit ϖ' →
      Function.Surjective (algebraMap O (O' ⧸ Ideal.span {ϖ'})) →
      RingHom.ker (algebraMap O (O' ⧸ Ideal.span {ϖ'})) = Ideal.span {ϖ} →
      ∀ [Algebra O' E] [IsScalarTower O O' E] [IsLocalization.Away ϖ' E], motive)
    (A : Type u) [CommRing A] [IsDedekindDomain A] [Algebra O A] [Algebra.IsIntegral O A]
    (Q : Ideal A) [hQmax : Q.IsMaximal] (hQ0 : Q ≠ ⊥)
    (hQ : Q.comap (algebraMap O A) = Ideal.span {ϖ})
    (O' : Type u) [CommRing O'] [IsDomain O'] [Algebra A O'] [Algebra O O'] [IsScalarTower O A O']
    [IsLocalization.AtPrime O' Q] [Algebra O' E] [IsScalarTower O O' E] [IsFractionRing O' E] :
    motive := by
  classical
  haveI : IsDiscreteValuationRing O' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hQ0 O'
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hmax' : Ideal.span {ϖ'} = IsLocalRing.maximalIdeal O' := hϖ'.maximalIdeal_eq.symm
  haveI := isLocalization_away_of_irreducible (F := E) hϖ'
  have hunder : (IsLocalRing.maximalIdeal O').comap (algebraMap A O') = Q :=
    IsLocalization.AtPrime.under_maximalIdeal O' Q
  have hcomp : algebraMap O O' = (algebraMap A O').comp (algebraMap O A) :=
    IsScalarTower.algebraMap_eq O A O'
  have hkerQ : RingHom.ker (algebraMap O (O' ⧸ Ideal.span {ϖ'})) = Ideal.span {ϖ} := by
    rw [ker_algebraMap_quot, hmax', hcomp, ← Ideal.comap_comap, hunder, hQ]
  haveI : Q.LiesOver (Ideal.span {ϖ}) := ⟨hQ.symm⟩
  haveI hmax : (Ideal.span {ϖ}).IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective θ hθ
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  letI := Ideal.Quotient.field Q
  haveI : IsAlgClosed (O ⧸ Ideal.span {ϖ}) := IsAlgClosed.of_ringEquiv k _
    ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hθ)).symm
  have hsurjQ : Function.Surjective (algebraMap (O ⧸ Ideal.span {ϖ}) (A ⧸ Q)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := O ⧸ Ideal.span {ϖ})).2
  have hQm : ((IsLocalRing.maximalIdeal O').comap (algebraMap A O')).IsMaximal := by
    rw [hunder]; exact hQmax
  have hsurjL : Function.Surjective
      (Ideal.quotientMap (IsLocalRing.maximalIdeal O') (algebraMap A O') hunder.ge) :=
    IsLocalization.surjective_quotientMap_of_maximal_of_localization (M := Q.primeCompl)
      (S := O') (H := hunder.ge) hQm
  have hsurjM : Function.Surjective (algebraMap O (O' ⧸ IsLocalRing.maximalIdeal O')) := by
    intro y
    obtain ⟨z, rfl⟩ := hsurjL y
    obtain ⟨w, rfl⟩ := hsurjQ z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨x, ?_⟩
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.quotientMap_mk,
      ← IsScalarTower.algebraMap_apply O A O']
    rfl
  have hsurj : Function.Surjective (algebraMap O (O' ⧸ Ideal.span {ϖ'})) := by
    rw [hmax']; exact hsurjM
  exact h O' ϖ' hϖ'.ne_zero hϖ'.not_isUnit hsurj hkerQ

include hθ hker in
/-- **A discrete valuation ring in a finite separable extension with the same residue field**
(eliminator form): every statement that holds for all `(O', ϖ')` with `O'` a Noetherian domain over
`O`, `ϖ' ∈ O'` a nonzero nonunit, `O → O'/(ϖ')` surjective with kernel `(ϖ)`, and
`E = O'[1/ϖ']`, holds. -/
theorem elim (hϖ0 : ϖ ≠ 0) (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (E : Type u) [Field E] [Algebra K E] [Algebra O E] [IsScalarTower O K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (motive : Prop)
    (h : ∀ (O' : Type u) [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] [Algebra O O']
      (ϖ' : O'), ϖ' ≠ 0 → ¬IsUnit ϖ' →
      Function.Surjective (algebraMap O (O' ⧸ Ideal.span {ϖ'})) →
      RingHom.ker (algebraMap O (O' ⧸ Ideal.span {ϖ'})) = Ideal.span {ϖ} →
      ∀ [Algebra O' E] [IsScalarTower O O' E] [IsLocalization.Away ϖ' E], motive) :
    motive := by
  classical
  haveI : (Ideal.span {ϖ}).IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective θ hθ
  -- the integral closure `A` of `O` in `E`: a Dedekind domain with fraction field `E`
  haveI : IsFractionRing (integralClosure O E) E :=
    integralClosure.isFractionRing_of_finite_extension K E
  haveI : IsDedekindDomain (integralClosure O E) := integralClosure.isDedekindDomain O K E
  -- a maximal ideal `Q` of `A` over `(ϖ)`
  have hinjA : Function.Injective (algebraMap O (integralClosure O E)) := by
    intro x y hxy
    apply IsFractionRing.injective O K
    apply (algebraMap K E).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply O (integralClosure O E) E, hxy,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure O E) (Ideal.span {ϖ}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinjA]
      exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    have : ϖ ∈ (⊥ : Ideal (integralClosure O E)).comap (algebraMap O _) :=
      hQ ▸ Ideal.mem_span_singleton_self ϖ
    exact hϖ0 (hinjA (by simpa using this))
  -- `O' = A_Q` inside `E`
  have hS : Q.primeCompl ≤ (integralClosure O E)⁰ := Ideal.primeCompl_le_nonZeroDivisors Q
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra (integralClosure O E) E,
      S = Localization.subalgebra.ofField E Q.primeCompl hS := ⟨_, rfl⟩
  haveI : IsLocalization.AtPrime S Q := by
    rw [hSdef]; exact Localization.subalgebra.isLocalization_ofField E Q.primeCompl hS
  haveI : IsFractionRing S E := IsFractionRing.isFractionRing_of_isLocalization Q.primeCompl S E hS
  letI : Algebra O S := ((algebraMap (integralClosure O E) S).comp
    (algebraMap O (integralClosure O E))).toAlgebra
  haveI : IsScalarTower O (integralClosure O E) S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower O S E := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply O (integralClosure O E) E x
  exact elim_aux hθ hker E motive h (integralClosure O E) Q hQ0 hQ S

end FiniteExtensionDVR

end SemistableReduction
