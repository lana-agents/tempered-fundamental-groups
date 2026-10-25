/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwo

/-!
# Étale and finite glued algebras (generic commutative algebra)

For a cover of `Spec R` by two basic opens `D(a)`, `D(b)` and pieces `Ba`, `Bb` glued along
`Bab` (`ZariskiTwo.glued`):

* **`ZariskiTwo.isLocalization_snd`**: `Bb = glued[1/b]` (the companion of
  `ZariskiTwo.isLocalization_fst`);
* **`ZariskiTwo.etale_glued`**: if `a, b` generate the unit ideal and `R → Ba`, `R → Bb` are
  étale, the glued algebra is étale over `R` (étaleness is local on the target,
  `RingHom.Etale.ofLocalizationSpanTarget`);
* **`ZariskiTwo.finite_glued'`**: if `Ba`, `Bb` are finite over localizations `Ra = R[1/a]`,
  `Rb = R[1/b]` (any models), the glued algebra is finite over `R`.
-/

universe u

namespace ZariskiTwo

variable {R : Type u} [CommRing R] {a b : R}
  {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab]
  {ρa : Ba →ₐ[R] Bab} {ρb : Bb →ₐ[R] Bab}

section Snd

variable (hb' : IsUnit (algebraMap R Bb b))
  (ha' : letI := ρa.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Ba b) Bab)
include hb' ha'

/-- **`Bb` is the localization of the glued algebra away from `b`.** -/
theorem isLocalization_snd :
    letI := algebraSnd (ρa := ρa) (ρb := ρb)
    IsLocalization.Away (algebraMap R (glued ρa ρb) b) Bb := by
  letI := algebraSnd (ρa := ρa) (ρb := ρb)
  haveI : IsScalarTower R (glued ρa ρb) Bb :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((snd ρa ρb).commutes r).symm
  have h := isLocalizedModule_snd (ρa := ρa) (ρb := ρb) b hb' ha'
  have h' : IsLocalizedModule (Submonoid.powers b)
      (IsScalarTower.toAlgHom R (glued ρa ρb) Bb).toLinearMap := h
  rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid,
    Submonoid.map_powers] at h'
  exact h'

end Snd

/-- An algebra `B` over `S` which is a localization away from `r` gives the same ring map out of
`R` as `Localization.Away r`, up to isomorphism; so étaleness transfers. -/
lemma etale_comp_away {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] (f : R →+* S)
    (r : S) [IsLocalization.Away r B] (h : ((algebraMap S B).comp f).Etale) :
    ((algebraMap S (Localization.Away r)).comp f).Etale := by
  let e : B ≃ₐ[S] Localization.Away r :=
    IsLocalization.algEquiv (Submonoid.powers r) B (Localization.Away r)
  have : (algebraMap S (Localization.Away r)).comp f =
      (e.toRingEquiv.toRingHom).comp ((algebraMap S B).comp f) := by
    ext x
    simp
  rw [this]
  exact RingHom.Etale.respectsIso.1 _ _ h

variable (hab : Ideal.span {a, b} = ⊤)
  (ha : IsUnit (algebraMap R Ba a))
  (hb : letI := ρb.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Bb a) Bab)
  (hb' : IsUnit (algebraMap R Bb b))
  (ha' : letI := ρa.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Ba b) Bab)
include hab ha hb hb' ha'

/-- **The glued algebra of two étale pieces is étale.** -/
theorem etale_glued (hBa : (algebraMap R Ba).Etale) (hBb : (algebraMap R Bb).Etale) :
    Algebra.Etale R (glued ρa ρb) := by
  rw [← RingHom.etale_algebraMap]
  refine RingHom.Etale.ofLocalizationSpanTarget _
    {algebraMap R (glued ρa ρb) a, algebraMap R (glued ρa ρb) b} ?_ ?_
  · have := congrArg (Ideal.map (algebraMap R (glued ρa ρb))) hab
    rwa [Ideal.map_span, Ideal.map_top, Set.image_pair] at this
  · rintro ⟨r, hr⟩
    rcases hr with rfl | hr
    · letI := algebraFst (ρa := ρa) (ρb := ρb)
      haveI := isLocalization_fst (ρa := ρa) (ρb := ρb) a ha hb
      refine etale_comp_away (B := Ba) _ _ ?_
      convert hBa using 1
      ext x
      exact (fst ρa ρb).commutes x
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      letI := algebraSnd (ρa := ρa) (ρb := ρb)
      haveI := isLocalization_snd (ρa := ρa) (ρb := ρb) hb' ha'
      refine etale_comp_away (B := Bb) _ _ ?_
      convert hBb using 1
      ext x
      exact (snd ρa ρb).commutes x

/-- **The glued algebra of two finite pieces is finite**, for pieces finite over any models
`Ra`, `Rb` of the localizations `R[1/a]`, `R[1/b]`. -/
theorem finite_glued' (Ra Rb : Type u) [CommRing Ra] [CommRing Rb] [Algebra R Ra] [Algebra R Rb]
    [IsLocalization.Away a Ra] [IsLocalization.Away b Rb] [Algebra Ra Ba] [Algebra Rb Bb]
    [IsScalarTower R Ra Ba] [IsScalarTower R Rb Bb] [Module.Finite Ra Ba] [Module.Finite Rb Bb] :
    Module.Finite R (glued ρa ρb) := by
  haveI := isLocalizedModule_fst (ρa := ρa) (ρb := ρb) a ha hb
  haveI := isLocalizedModule_snd (ρa := ρa) (ρb := ρb) b hb' ha'
  let ea : Localization.Away a ≃ₐ[R] Ra :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Ra
  let eb : Localization.Away b ≃ₐ[R] Rb :=
    IsLocalization.algEquiv (Submonoid.powers b) (Localization.Away b) Rb
  letI : Algebra (Localization.Away a) Ba := ((algebraMap Ra Ba).comp ea.toRingHom).toAlgebra
  letI : Algebra (Localization.Away b) Bb := ((algebraMap Rb Bb).comp eb.toRingHom).toAlgebra
  haveI : IsScalarTower R (Localization.Away a) Ba := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = algebraMap Ra Ba (ea (algebraMap R _ r))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower R (Localization.Away b) Bb := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = algebraMap Rb Bb (eb (algebraMap R _ r))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have hfa : (algebraMap (Localization.Away a) Ba).Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance)
      (RingHom.Finite.of_surjective _ ea.surjective)
  have hfb : (algebraMap (Localization.Away b) Bb).Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance)
      (RingHom.Finite.of_surjective _ eb.surjective)
  exact finite_glued a b hab (RingHom.finite_algebraMap.1 hfa) (RingHom.finite_algebraMap.1 hfb)

end ZariskiTwo
