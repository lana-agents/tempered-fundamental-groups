/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapFibre

/-!
# Étale lifts between algebras whose special fibres are localizations of one ring
(Blueprint §12.8, M2.3 (f))

Let `R` be a ring with a nilpotent ideal `J`, `M`, `X` formally étale `R`-algebras and `C` an
`R`-algebra (the special-fibre covering of a chart). Suppose the special fibres are localizations
of `C`: `γM : C → M/JM` away from `s` and `γX : C → X/JX` away from `s · t` (`t ∈ R`). Then:

* **`EtaleNil.liftLoc`**: the `R`-algebra map `M → X` lifting the unique `C`-algebra map
  `M/JM → X/JX` (`red_liftLoc_comp`);
* **`EtaleNil.isLocalization_liftLoc`**: it is a localization away from `t`
  (`EtaleNil.isLocalization_of_red`);
* `EtaleNil.ext_of_comp`: maps `M → X` are determined by their reductions composed with `γM`.

These compare the étale pieces of a covering over overlapping basic opens of a level chart when
all special fibres are described as localizations of the special-fibre covering of one chart.
-/

universe u

namespace SemistableReduction

namespace EtaleNil

noncomputable section

variable {R : Type u} [CommRing R] (J : Ideal R) {m : ℕ} (hJ : J ^ m = ⊥)
  {C M X : Type u} [CommRing C] [CommRing M] [CommRing X] [Algebra R C] [Algebra R M]
  [Algebra R X]
  (γM : C →ₐ[R] M ⧸ JB J M) (γX : C →ₐ[R] X ⧸ JB J X) (s : C) (t : R)
  (hM : letI := γM.toRingHom.toAlgebra; IsLocalization.Away s (M ⧸ JB J M))
  (hX : letI := γX.toRingHom.toAlgebra; IsLocalization.Away (s * algebraMap R C t) (X ⧸ JB J X))

include hX in
lemma isUnit_s : IsUnit (γX s) := by
  letI := γX.toRingHom.toAlgebra
  have h := IsLocalization.Away.algebraMap_isUnit (S := X ⧸ JB J X) (s * algebraMap R C t)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- The `C`-algebra map `M/JM → X/JX` (as an `R`-algebra map). -/
def redLoc : M ⧸ JB J M →ₐ[R] X ⧸ JB J X :=
  letI := γM.toRingHom.toAlgebra
  haveI := hM
  { IsLocalization.Away.lift s (g := (γX : C →+* X ⧸ JB J X)) (isUnit_s J γX s t hX) with
    commutes' := fun r ↦ by
      letI := γM.toRingHom.toAlgebra
      haveI := hM
      have : algebraMap R (M ⧸ JB J M) r = algebraMap C (M ⧸ JB J M) (algebraMap R C r) :=
        (γM.commutes r).symm
      change IsLocalization.Away.lift s _ (algebraMap R (M ⧸ JB J M) r) = _
      rw [this, IsLocalization.Away.lift_eq]
      exact γX.commutes r }

lemma redLoc_comp (c : C) : redLoc J γM γX s t hM hX (γM c) = γX c := by
  letI := γM.toRingHom.toAlgebra
  haveI := hM
  exact IsLocalization.Away.lift_eq s (isUnit_s J γX s t hX) c

include hM hX in
/-- `M/JM → X/JX` is a localization away from `t`. -/
lemma isLocalization_redLoc :
    letI := (redLoc J γM γX s t hM hX).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (M ⧸ JB J M) t) (X ⧸ JB J X) := by
  letI := γM.toRingHom.toAlgebra
  haveI := hM
  letI := γX.toRingHom.toAlgebra
  haveI := hX
  letI := (redLoc J γM γX s t hM hX).toRingHom.toAlgebra
  haveI : IsScalarTower C (M ⧸ JB J M) (X ⧸ JB J X) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (redLoc_comp J γM γX s t hM hX c).symm
  have h := SemistableReduction.OverlapFibre.away_of_mul (R := C) (S := M ⧸ JB J M)
    (T := X ⧸ JB J X) s (algebraMap R C t)
  rwa [show algebraMap C (M ⧸ JB J M) (algebraMap R C t) = algebraMap R (M ⧸ JB J M) t from
    γM.commutes t] at h

variable [Algebra.FormallyEtale R M] [Algebra.FormallyEtale R X]

/-- **The étale lift `M → X`** of the `C`-algebra map of special fibres. -/
def liftLoc : M →ₐ[R] X := lift J hJ ((redLoc J γM γX s t hM hX).comp (Ideal.Quotient.mkₐ R _))

omit [Algebra.FormallyEtale R X] in
lemma red_liftLoc : red J (liftLoc J hJ γM γX s t hM hX) = redLoc J γM γX s t hM hX := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [red_mk]
  exact mk_lift J hJ _ x

omit [Algebra.FormallyEtale R X] in
lemma red_liftLoc_comp (c : C) : red J (liftLoc J hJ γM γX s t hM hX) (γM c) = γX c := by
  rw [red_liftLoc, redLoc_comp]

include hM hX in
/-- **The étale lift is a localization away from `t`.** -/
theorem isLocalization_liftLoc (ht : IsUnit (algebraMap R X t)) :
    letI := (liftLoc J hJ γM γX s t hM hX).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R M t) X := by
  refine isLocalization_of_red J hJ t (liftLoc J hJ γM γX s t hM hX) ht ?_
  rw [red_liftLoc]
  exact isLocalization_redLoc J γM γX s t hM hX

omit [Algebra.FormallyEtale R X] in
include hJ hM in
/-- **Uniqueness**: maps `M → X` are determined by their reductions on `C`. -/
lemma ext_of_comp {φ ψ : M →ₐ[R] X} (h : ∀ c, red J φ (γM c) = red J ψ (γM c)) : φ = ψ := by
  refine ext_red J hJ ?_
  letI := γM.toRingHom.toAlgebra
  haveI := hM
  have : (red J φ : M ⧸ JB J M →+* X ⧸ JB J X) = red J ψ :=
    IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext h)
  exact AlgHom.coe_ringHom_injective this

end

end EtaleNil

end SemistableReduction
