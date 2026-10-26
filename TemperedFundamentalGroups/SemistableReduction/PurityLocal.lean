/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.Purity
import TemperedFundamentalGroups.SemistableReduction.NormLocalUnramified
import TemperedFundamentalGroups.SemistableReduction.EtaleSpecialFibre

/-!
# Purity at a regular point of a normal chart

Let `A` be a Noetherian integrally closed domain with fraction field `K`, `L / K` finite
separable, `B = integralClosure A L`, and `P` a maximal ideal of `A` such that `A_P` is regular
of dimension two with parameters `x, y` (`maximalIdeal A_P = (x, y)`, `x` prime, `y ∉ (x)`).

* **`PurityLocal.isEtaleAt`**: if `B` is unramified over `A` at every prime lying over a prime
  strictly inside `P`, then `B` is étale over `A` at every prime over `P` (Zariski–Nagata purity
  `Purity.etale_of_isUnramifiedAt_of_maximalIdeal_eq_span_pair` for `A_P ⊆ integralClosure A_P L`,
  the localisation of `B`, `NormLocal`).
* **`PurityLocal.etale_quot_awayMap`**: if moreover `A/I` is a Jacobson ring and `A` is regular
  at every closed point of `V(I) ∩ D(g)`, with `B` unramified over the punctured spectra of the
  closed points of `V(I) ∩ D(g)`, then `B/IB` is étale over `A/I` on `D(ḡ)` (the `etale` fields
  of the special-fibre coverings, `I = ϖA`).
* `PurityLocal.etale_awayMap`: `A → B_{f}` étale ⇒ `A_f → B_f` étale (the form of the `etale`
  field of `Admissible.Covering`).
-/

universe u

open IsLocalRing

namespace SemistableReduction

namespace PurityLocal

noncomputable section

section Away

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- `A → B_f` étale ⇒ `A_f → B_f` étale. -/
theorem etale_awayMap (f : A) [Algebra.Etale A (Localization.Away (algebraMap A B f))] :
    (Localization.awayMap (algebraMap A B) f).Etale := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A B f)) :=
    (Localization.awayMap (algebraMap A B) f).toAlgebra
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (algebraMap A B f)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = Localization.awayMap (algebraMap A B) f (algebraMap A _ a)
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
        ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.Etale A (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  exact RingHom.etale_algebraMap.mpr
    (Algebra.Etale.of_restrictScalars A (Localization.Away f) _)

end Away

section Transport

variable {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']

/-- Localisations at corresponding primes of isomorphic algebras are isomorphic. -/
def locEquiv (e : B ≃ₐ[A] B') (Q : Ideal B') [Q.IsPrime] :
    Localization.AtPrime (Q.comap e) ≃ₐ[A] Localization.AtPrime Q :=
  AlgEquiv.ofRingEquiv (f := IsLocalization.ringEquivOfRingEquiv (M := (Q.comap e).primeCompl)
    (T := Q.primeCompl) (Localization.AtPrime (Q.comap e)) (Localization.AtPrime Q)
    e.toRingEquiv (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        simpa [Ideal.mem_primeCompl_iff] using hy)) fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B, IsLocalization.ringEquivOfRingEquiv_eq,
      IsScalarTower.algebraMap_apply A B' (Localization.AtPrime Q)]
    simp

lemma isEtaleAt_of_equiv (e : B ≃ₐ[A] B') {Q : Ideal B} {Q' : Ideal B'} [Q.IsPrime] [Q'.IsPrime]
    (hQ : Q = Q'.comap e) (h : Algebra.IsEtaleAt A Q') : Algebra.IsEtaleAt A Q := by
  subst hQ
  exact Algebra.FormallyEtale.of_equiv (locEquiv e Q').symm

lemma isUnramifiedAt_of_equiv (e : B ≃ₐ[A] B') {Q : Ideal B} {Q' : Ideal B'} [Q.IsPrime]
    [Q'.IsPrime] (hQ : Q = Q'.comap e) (h : Algebra.IsUnramifiedAt A Q') :
    Algebra.IsUnramifiedAt A Q := by
  subst hQ
  exact Algebra.FormallyUnramified.of_equiv (locEquiv e Q').symm

end Transport

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K in
/-- **Purity at a regular closed point.** -/
theorem isEtaleAt (P : Ideal A) [P.IsMaximal] {x y : Localization.AtPrime P} (hx : Prime x)
    (hy : y ∉ Ideal.span {x}) (hm : maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (hunr : ∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime],
      Q.comap (algebraMap A (integralClosure A L)) < P → Algebra.IsUnramifiedAt A Q)
    (M : Ideal (integralClosure A L)) [M.IsPrime]
    (hM : M.comap (algebraMap A (integralClosure A L)) = P) :
    Algebra.IsEtaleAt A M := by
  have hle : P.primeCompl ≤ nonZeroDivisors A := P.primeCompl_le_nonZeroDivisors
  letI : Algebra (Localization.AtPrime P) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ K P.primeCompl (nonZeroDivisors A) hle
  haveI : IsScalarTower A (Localization.AtPrime P) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ K _ _ hle
  haveI : IsFractionRing (Localization.AtPrime P) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ K
  letI : Algebra (Localization.AtPrime P) L :=
    ((algebraMap K L).comp (algebraMap (Localization.AtPrime P) K)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime P) K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A (Localization.AtPrime P) L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply (Localization.AtPrime P) K L,
      ← IsScalarTower.algebraMap_apply A (Localization.AtPrime P) K,
      ← IsScalarTower.algebraMap_apply]
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  haveI : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl hle
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  haveI : Algebra.Etale (Localization.AtPrime P) (integralClosure (Localization.AtPrime P) L) :=
    Purity.etale_of_isUnramifiedAt_of_maximalIdeal_eq_span_pair K L hx hy hm
      (NormLocal.isUnramifiedAt hinj hunr)
  -- `M` in the localised normalisation
  letI := NormLocal.algLoc (L := L) P
  haveI := NormLocal.isLocalization hinj (𝔪 := P)
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl :
      Set (integralClosure A L)) M := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haM
    exact ha (hM ▸ (Ideal.mem_comap.2 haM))
  haveI hM' : (M.map (algebraMap (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ M ‹_› hdisj
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
    (integralClosure (Localization.AtPrime P) L) (I := M) ‹_› hdisj
  haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
    (Localization.AtPrime (M.map (algebraMap (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L))))
    (M.map (algebraMap (integralClosure A L) (integralClosure (Localization.AtPrime P) L)))
  haveI : IsLocalization M.primeCompl (Localization.AtPrime (M.map (algebraMap
      (integralClosure A L) (integralClosure (Localization.AtPrime P) L)))) := by
    convert this using 1
    ext z
    simp only [Ideal.mem_primeCompl_iff, hcomap]
  let e := IsLocalization.algEquiv M.primeCompl (Localization.AtPrime M)
    (Localization.AtPrime (M.map (algebraMap (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L))))
  haveI : Algebra.FormallyEtale A (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization P.primeCompl
  haveI : Algebra.FormallyEtale (Localization.AtPrime P)
      (Localization.AtPrime (M.map (algebraMap (integralClosure A L)
        (integralClosure (Localization.AtPrime P) L)))) :=
    Algebra.FormallyEtale.comp _ (integralClosure (Localization.AtPrime P) L) _
  haveI : Algebra.FormallyEtale A (Localization.AtPrime (M.map (algebraMap (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L)))) :=
    Algebra.FormallyEtale.comp A (Localization.AtPrime P) _
  exact Algebra.FormallyEtale.of_equiv (e.symm.restrictScalars A)

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [IsFractionRing A K]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- Unramifiedness over a punctured neighbourhood passes from any normalisation `B` to
`integralClosure A L`. -/
lemma isUnramifiedAt_integralClosure (B : Type u) [CommRing B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L] {P : Ideal A}
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) < P →
      Algebra.IsUnramifiedAt A Q)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A (integralClosure A L)) < P) : Algebra.IsUnramifiedAt A Q := by
  let e : B ≃ₐ[A] integralClosure A L := IsIntegralClosure.equiv A B L (integralClosure A L)
  haveI : (Q.comap e).IsPrime := Ideal.comap_isPrime _ _
  refine isUnramifiedAt_of_equiv e.symm (Q' := Q.comap e) (by ext; simp) (hunr _ ?_)
  convert hQ using 1
  ext a
  simp

include K in
/-- **Purity at a regular closed point**, for any normalisation `B` of `A` in `L`. -/
theorem isEtaleAt' (P : Ideal A) [P.IsMaximal] {x y : Localization.AtPrime P} (hx : Prime x)
    (hy : y ∉ Ideal.span {x}) (hm : maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (B : Type u) [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) < P →
      Algebra.IsUnramifiedAt A Q)
    (M : Ideal B) [M.IsPrime] (hM : M.comap (algebraMap A B) = P) :
    Algebra.IsEtaleAt A M := by
  let e : B ≃ₐ[A] integralClosure A L := IsIntegralClosure.equiv A B L (integralClosure A L)
  refine isEtaleAt_of_equiv e (Q' := M.comap e.symm) (by ext; simp) ?_
  refine isEtaleAt K P hx hy hm (isUnramifiedAt_integralClosure B hunr) _ ?_
  rw [← hM]
  ext a
  simp

include K in
/-- **The fibre of the normalisation over `V(I)` is étale on `D(ḡ)`.** -/
theorem etale_quot_awayMap (I : Ideal A) [IsJacobsonRing (A ⧸ I)]
    (B : Type u) [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] (g : A)
    (hreg : ∀ (P : Ideal A) [P.IsMaximal], I ≤ P → g ∉ P →
      ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (hunr : ∀ (P : Ideal A) [P.IsMaximal], I ≤ P → g ∉ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) < P → Algebra.IsUnramifiedAt A Q) :
    (Localization.awayMap (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)))
      (Ideal.Quotient.mk I g)).Etale := by
  haveI : Module.Finite A B := IsIntegralClosure.finite A K L B
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Module.Finite (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  haveI : Algebra.FinitePresentation (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : IsJacobsonRing (B ⧸ I.map (algebraMap A B)) :=
    isJacobsonRing_of_isIntegral (R := A ⧸ I)
  haveI : Algebra.Etale (A ⧸ I) (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A B))
      (algebraMap A B g))) :=
    EtaleQuot.etale_quot_of_isEtaleAt_maximal I _ fun Q _ hIQ hgQ ↦ by
      haveI : (Q.comap (algebraMap A B)).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
      have hIP : I ≤ Q.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.1 hIQ
      obtain ⟨x, y, hx, hy, hxy⟩ := hreg _ hIP hgQ
      exact isEtaleAt' K (L := L) _ hx hy hxy B (hunr _ hIP hgQ) Q rfl
  haveI : Algebra.Etale (A ⧸ I) (Localization.Away (algebraMap (A ⧸ I)
      (B ⧸ I.map (algebraMap A B)) (Ideal.Quotient.mk I g))) := this
  exact etale_awayMap _

end

end PurityLocal

end SemistableReduction
