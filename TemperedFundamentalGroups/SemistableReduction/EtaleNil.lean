/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import TemperedFundamentalGroups.SemistableReduction.EtaleLiftHom
import TemperedFundamentalGroups.SemistableReduction.CompleteFinite

/-!
# Formally étale algebras over a ring with a nilpotent ideal (Blueprint §12.8, M2.3 (f))

Let `R` be a ring with a nilpotent ideal `J` (`J^m = 0`, e.g. `J = ϖR` for a level
`R = T/ϖⁿ⁺¹T` of a chart). For `R`-algebras `B`, `B'` write `B̄ = B/JB`. Then (Stacks,
Tag 00UQ, in the form of `EtaleLift`):

* `EtaleNil.lift`, `mk_lift`, **`EtaleNil.ext`**: maps `B → B'` out of a formally étale `B` exist
  for, and are determined by, their reductions `B → B̄'`;
* **`EtaleNil.bijective_of_red`**: an `R`-algebra map of formally étale `R`-algebras whose
  reduction `B̄ → B̄'` is bijective is bijective;
* **`EtaleNil.isLocalization_of_red`**: an `R`-algebra map of formally étale `R`-algebras whose
  reduction is a localization away from `r ∈ R` is a localization away from `r`.

These compare the étale pieces of a covering on overlapping basic opens of a level chart: two
étale lifts are identified as soon as their special fibres are.
-/

universe u

namespace SemistableReduction

namespace EtaleNil

noncomputable section

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- The ideal `JB` of an `R`-algebra `B`. -/
abbrev JB (B : Type u) [CommRing B] [Algebra R B] : Ideal B := J.map (algebraMap R B)

variable {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B''] [Algebra R B]
  [Algebra R B'] [Algebra R B'']

lemma JB_pow {m : ℕ} (hJ : J ^ m = ⊥) (B : Type u) [CommRing B] [Algebra R B] :
    JB J B ^ m = ⊥ := by
  rw [← Ideal.map_pow, hJ, Ideal.map_bot]

lemma isAdicComplete {m : ℕ} (hJ : J ^ m = ⊥) (B : Type u) [CommRing B] [Algebra R B] :
    IsAdicComplete (JB J B) B :=
  CompleteFinite.isAdicComplete_of_pow_eq_bot _ (JB_pow J hJ B)

lemma le_comap (φ : B →ₐ[R] B') : JB J B ≤ (JB J B').comap φ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ hx

/-- **The reduction** `B̄ → B̄'` of an `R`-algebra map. -/
def red (φ : B →ₐ[R] B') : B ⧸ JB J B →ₐ[R] B' ⧸ JB J B' :=
  Ideal.quotientMapₐ _ φ (le_comap J φ)

lemma red_mk (φ : B →ₐ[R] B') (x : B) :
    red J φ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (φ x) := rfl

lemma red_comp (φ : B →ₐ[R] B') (ψ : B' →ₐ[R] B'') :
    red J (ψ.comp φ) = (red J ψ).comp (red J φ) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

lemma red_id : red J (AlgHom.id R B) = AlgHom.id R _ := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable {m : ℕ} (hJ : J ^ m = ⊥)

section Etale

variable [Algebra.FormallyEtale R B]

/-- **The lift** `B → B'` of a map `B → B̄'` (`B` formally étale). -/
def lift (φ₀ : B →ₐ[R] B' ⧸ JB J B') : B →ₐ[R] B' :=
  haveI := isAdicComplete J hJ B'
  EtaleLift.lift _ φ₀

lemma mk_lift (φ₀ : B →ₐ[R] B' ⧸ JB J B') (x : B) :
    Ideal.Quotient.mk _ (lift J hJ φ₀ x) = φ₀ x :=
  haveI := isAdicComplete J hJ B'
  congrArg (fun g ↦ g x) (EtaleLift.mkₐ_comp_lift _ φ₀)

include hJ in
/-- **Uniqueness**: maps out of a formally étale algebra agreeing modulo `J` are equal. -/
lemma ext {φ ψ : B →ₐ[R] B'}
    (h : ∀ x, Ideal.Quotient.mk (JB J B') (φ x) = Ideal.Quotient.mk _ (ψ x)) : φ = ψ :=
  haveI := isAdicComplete J hJ B'
  EtaleLift.ext_of_comp_eq _ (AlgHom.ext h)

include hJ in
lemma ext_red {φ ψ : B →ₐ[R] B'} (h : red J φ = red J ψ) : φ = ψ :=
  ext J hJ fun x ↦ by rw [← red_mk, ← red_mk, h]

variable [Algebra.FormallyEtale R B']

include hJ in
/-- **A map of formally étale algebras with bijective reduction is bijective.** -/
theorem bijective_of_red (φ : B →ₐ[R] B') (h : Function.Bijective (red J φ)) :
    Function.Bijective φ := by
  let e := AlgEquiv.ofBijective (red J φ) h
  let ψ : B' →ₐ[R] B := lift J hJ (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R _))
  have h1 : ψ.comp φ = AlgHom.id R B := ext J hJ fun x ↦ by
    rw [AlgHom.comp_apply, mk_lift, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← red_mk]
    exact e.symm_apply_apply (Ideal.Quotient.mk _ x)
  have h2 : φ.comp ψ = AlgHom.id R B' := ext J hJ fun x ↦ by
    rw [AlgHom.comp_apply, ← red_mk, mk_lift]
    exact e.apply_symm_apply _
  exact ⟨Function.LeftInverse.injective (g := ψ) fun x ↦ AlgHom.congr_fun h1 x,
    Function.RightInverse.surjective (g := ψ) fun y ↦ AlgHom.congr_fun h2 y⟩

end Etale

/-! ### Localizations -/

section Loc

variable (r : R)

/-- **Localizations stay localizations modulo `J`**: if `φ : B → B'` is a localization away from
`b`, its reduction `B̄ → B̄'` is a localization away from `b̄`. -/
theorem isLocalization_red [Algebra B B'] [IsScalarTower R B B'] (b : B)
    [IsLocalization.Away b B'] :
    letI := (red J (IsScalarTower.toAlgHom R B B')).toRingHom.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (JB J B) b) (B' ⧸ JB J B') := by
  letI := (red J (IsScalarTower.toAlgHom R B B')).toRingHom.toAlgebra
  have h' := IsLocalization.of_surjective (M := Submonoid.powers b) (S := B')
    (R' := B ⧸ JB J B) (S' := B' ⧸ JB J B') (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    (RingHom.ext fun x ↦ (red_mk J (IsScalarTower.toAlgHom R B B') x).symm)
    (by
      rw [Ideal.mk_ker, Ideal.mk_ker, Ideal.map_map, ← IsScalarTower.algebraMap_eq])
  rwa [Submonoid.map_powers] at h'

variable [Algebra.FormallyEtale R B] [Algebra.FormallyEtale R B']

include hJ in
/-- **A map of formally étale algebras whose reduction is a localization away from `r` is a
localization away from `r`.** -/
theorem isLocalization_of_red (φ : B →ₐ[R] B') (hr : IsUnit (algebraMap R B' r))
    (h : letI := (red J φ).toRingHom.toAlgebra;
      IsLocalization.Away (algebraMap R (B ⧸ JB J B) r) (B' ⧸ JB J B')) :
    letI := φ.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R B r) B' := by
  set L := Localization.Away (algebraMap R B r)
  haveI : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers (algebraMap R B r))
  haveI : Algebra.FormallyEtale R L := Algebra.FormallyEtale.comp R B L
  have hr' : IsUnit (φ (algebraMap R B r)) := by rwa [AlgHom.commutes]
  -- the extension `ψ : B[1/r] → B'`
  let ψ0 : L →+* B' := IsLocalization.Away.lift (algebraMap R B r) (g := (φ : B →+* B')) hr'
  have hψ0 : ∀ x : B, ψ0 (algebraMap B L x) = φ x := fun x ↦
    IsLocalization.Away.lift_eq _ hr' x
  let ψ : L →ₐ[R] B' :=
    { ψ0 with
      commutes' := fun a ↦ by
        change ψ0 (algebraMap R L a) = _
        rw [IsScalarTower.algebraMap_apply R B L, hψ0, AlgHom.commutes] }
  have hψ : ∀ x : B, ψ (algebraMap B L x) = φ x := hψ0
  -- its reduction is bijective: both sides are `B̄[1/r̄]`
  letI := (red J φ).toRingHom.toAlgebra
  let ι : B ⧸ JB J B →ₐ[R] L ⧸ JB J L := red J (IsScalarTower.toAlgHom R B L)
  letI := ι.toRingHom.toAlgebra
  haveI hL : IsLocalization.Away (algebraMap R (B ⧸ JB J B) r) (L ⧸ JB J L) :=
    isLocalization_red J (algebraMap R B r)
  have hcomp : ∀ x : B ⧸ JB J B, red J ψ (ι x) = red J φ x := fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (ψ (algebraMap B L x)) = _
    rw [hψ]
    rfl
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap R (B ⧸ JB J B) r))
    (L ⧸ JB J L) (B' ⧸ JB J B')
  have he : ∀ y, red J ψ y = e y := fun y ↦ by
    have : (red J ψ).toRingHom = e.toRingEquiv.toRingHom := IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap R (B ⧸ JB J B) r)) <| RingHom.ext fun x ↦ by
        simp only [RingHom.comp_apply]
        change red J ψ (ι x) = e (algebraMap _ _ x)
        rw [hcomp, AlgEquiv.commutes]
        rfl
    exact RingHom.congr_fun this y
  have hbij : Function.Bijective (red J ψ) := by
    have : ⇑(red J ψ) = e := funext he
    rw [this]
    exact e.bijective
  letI := φ.toRingHom.toAlgebra
  let E : L ≃ₐ[B] B' :=
    { AlgEquiv.ofBijective ψ (bijective_of_red J hJ ψ hbij) with
      commutes' := fun x ↦ hψ x }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap R B r)) E

end Loc

end

end EtaleNil

end SemistableReduction
