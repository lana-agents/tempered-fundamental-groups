/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import TemperedFundamentalGroups.SemistableReduction.FormalPatchEquiv

/-!
# The isomorphism modulo `J` from the special fibre (Blueprint §12.8, M2.3 (d'))

`FormalPatchLevel.alphaOfEquiv` turns an `R̂`-algebra isomorphism
`Φ : (R̂ ⊗_R P)/J ≃ N_f/J` into the patching datum `α₀`. Here `Φ` is produced from data on the
special fibre:

* `P` is the lift over `D(f)` of the special-fibre covering `C` on the smooth locus:
  `σ : P/JP ≃ C_f` (as from `EtaleLiftExists.exists_finite_etale_lift_of_pow_eq_bot` applied to
  `C_f` over `R_f/J`);
* `κ : R̂ ⊗_R C ≃ N/JN`: the special-fibre covering, completed along the nodes, is the reduction
  of the formal model `N` (for an admissible covering: the Kummer algebra, `Admissible.Covering`).

Then (`FormalPatchLevel.reductionEquiv`, `locEquiv`, `quotLocEquiv`)

  `(R̂ ⊗_R P)/J ≅ R̂ ⊗_R (P/JP) ≅ R̂ ⊗_R C_f ≅ (R̂ ⊗_R C)_f ≅ (N/JN)_f ≅ N_f/J`

(Mathlib `Algebra.TensorProduct.tensorQuotientEquiv`,
`IsLocalization.Away.tensorProductEquivTMulRight`, `IsLocalization.ringEquivOfRingEquiv`, and
localization commuting with quotients), and **`FormalPatchLevel.specialFibreEquiv σ κ`** is the
composite; its `alphaOfEquiv` satisfies the hypotheses `hsurj`, `hinj` of
`FormalPatchLevel.isBaseChange_lift` (`surjective_betaMod_alphaOfEquiv`,
`mem_of_betaMod_alphaOfEquiv_eq_zero`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalPatchLevel

noncomputable section

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R)
  {P : Type u} [CommRing P] [Algebra R P]
  {C : Type u} [CommRing C] [Algebra R C]
  {N : Type u} [CommRing N] [Algebra R N] [Algebra (Hat f) N] [IsScalarTower R (Hat f) N]

omit [Algebra (Hat f) N] [IsScalarTower R (Hat f) N] in
lemma JT_eq : JT f J P = (J.map (algebraMap R P)).map
    (Algebra.TensorProduct.includeRight (R := R) (A := Hat f)) := by
  unfold JT
  rw [show Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := Hat f))
      (J.map (algebraMap R P)) = Ideal.map (Algebra.TensorProduct.includeRight (R := R)
        (A := Hat f)).toRingHom (J.map (algebraMap R P)) from rfl, Ideal.map_map]
  congr 1
  exact (Algebra.TensorProduct.includeRight.comp_algebraMap).symm

/-- `(R̂ ⊗_R P)/J ≅ (R̂ ⊗_R C)_f`, from `σ : P/JP ≅ C_f`. -/
def reductionEquiv
    (σ : (P ⧸ J.map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R C f)) :
    ((Hat f ⊗[R] P) ⧸ JT f J P) ≃ₐ[Hat f]
      Localization.Away ((1 : Hat f) ⊗ₜ[R] algebraMap R C f) :=
  ((Ideal.quotientEquivAlgOfEq (Hat f) (JT_eq f J)).trans
    (Algebra.TensorProduct.tensorQuotientEquiv (Hat f) P (Hat f)
      (J.map (algebraMap R P))).symm).trans
  ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans
    (IsLocalization.Away.tensorProductEquivTMulRight R (Hat f) (algebraMap R C f)
      (Localization.Away (algebraMap R C f))))

variable (N) in
/-- The ideal `JN`. -/
abbrev JN : Ideal N := J.map (algebraMap R N)

lemma one_tmul_algebraMap (κ : (Hat f ⊗[R] C) ≃ₐ[Hat f] (N ⧸ JN J N)) :
    κ ((1 : Hat f) ⊗ₜ[R] algebraMap R C f) = algebraMap R (N ⧸ JN J N) f := by
  have h1 : (1 : Hat f) ⊗ₜ[R] algebraMap R C f =
      algebraMap (Hat f) (Hat f ⊗[R] C) (algebraMap R (Hat f) f) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one (A := Hat f), Algebra.algebraMap_eq_smul_one (A := C),
      TensorProduct.smul_tmul]
  rw [h1, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

/-- `(R̂ ⊗_R C)_f ≅ (N/JN)_f`, from `κ : R̂ ⊗_R C ≅ N/JN`. -/
def locEquiv (κ : (Hat f ⊗[R] C) ≃ₐ[Hat f] (N ⧸ JN J N)) :
    Localization.Away ((1 : Hat f) ⊗ₜ[R] algebraMap R C f) ≃ₐ[Hat f]
      Localization.Away (algebraMap R (N ⧸ JN J N) f) :=
  AlgEquiv.ofRingEquiv
    (f := IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers ((1 : Hat f) ⊗ₜ[R] algebraMap R C f))
      (T := Submonoid.powers (algebraMap R (N ⧸ JN J N) f))
      (Localization.Away ((1 : Hat f) ⊗ₜ[R] algebraMap R C f))
      (Localization.Away (algebraMap R (N ⧸ JN J N) f)) κ.toRingEquiv (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (one_tmul_algebraMap f J κ))) fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (Hat f) (Hat f ⊗[R] C),
      IsLocalization.ringEquivOfRingEquiv_eq, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]

omit [Algebra (Hat f) N] [IsScalarTower R (Hat f) N] in
lemma JNf_eq : JNf f J N = (JN J N).map (algebraMap N (Nf f N)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- Localization commutes with the quotient: `N_f/J ≅ (N/JN)_f`. -/
def quotLocEquiv : (Nf f N ⧸ JNf f J N) ≃ₐ[Hat f]
    Localization.Away (algebraMap R (N ⧸ JN J N) f) :=
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (N ⧸ JN J N)
      (Submonoid.powers (algebraMap R N f))) (Nf f N ⧸ (JN J N).map (algebraMap N (Nf f N))) :=
    inferInstance
  haveI : IsLocalization.Away (algebraMap R (N ⧸ JN J N) f)
      (Nf f N ⧸ (JN J N).map (algebraMap N (Nf f N))) := by
    unfold IsLocalization.Away
    convert this using 1
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, IsScalarTower.algebraMap_apply R N]
  let e : (Nf f N ⧸ (JN J N).map (algebraMap N (Nf f N))) ≃ₐ[N ⧸ JN J N]
      Localization.Away (algebraMap R (N ⧸ JN J N) f) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R (N ⧸ JN J N) f)) _ _
  (Ideal.quotientEquivAlgOfEq (Hat f) (JNf_eq f J)).trans
    (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun x ↦ by
      rw [IsScalarTower.algebraMap_apply (Hat f) N (Nf f N ⧸ _),
        IsScalarTower.algebraMap_apply N (N ⧸ JN J N) (Nf f N ⧸ _)]
      erw [e.commutes]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])

/-- **The isomorphism modulo `J` from the special fibre**:
`(R̂ ⊗_R P)/J ≅ N_f/J` from `σ : P/JP ≅ C_f` and `κ : R̂ ⊗_R C ≅ N/JN`. -/
def specialFibreEquiv
    (σ : (P ⧸ J.map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R C f))
    (κ : (Hat f ⊗[R] C) ≃ₐ[Hat f] (N ⧸ JN J N)) :
    ((Hat f ⊗[R] P) ⧸ JT f J P) ≃ₐ[Hat f] (Nf f N ⧸ JNf f J N) :=
  ((reductionEquiv f J σ).trans (locEquiv f J κ)).trans (quotLocEquiv f J).symm

end

end FormalPatchLevel

end SemistableReduction
