/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeCoverEtaleLocal
import TemperedFundamentalGroups.SemistableReduction.EtaleSplit

/-!
# Covers split over an étale neighbourhood: the embedding into the compositum

Setting of `NodeCoverEtaleLocal`: `R → C` a finite local homomorphism of local domains with
trivial residue field extension, `(R', P)` an étale neighbourhood of the closed point of `R`,
`P₁` the (unique) prime of `C ⊗_R R'` over `P`, and `E = K_R ⊗_R R'_P`, `F = E ⊗_{K_R} K_C`
(fields by `isField_tensor_localization`, `isField_tensor_tensor`).

* `NodeCover.toTensorTensor`: the map `C ⊗_R R' → F`, `c ⊗ r ↦ (1 ⊗ r) ⊗ c`;
* `NodeCover.ker_toTensorTensor_le`: its kernel is contained in `P₁`, so it extends to the local
  ring `(C ⊗_R R')_{P₁}`;
* `NodeCover.exists_algHom_tensorTensor`: if `L₁ ⊇ K_C` is a field whose normalisation `B₁` over
  `C` is finite étale and `L ⊆ L₁` is a subextension over `K_R`, then there are an étale
  neighbourhood `(R', P)` and a `K_R`-embedding `L → F` (`EtaleSplit.exists_etale_section`
  splits `B₁` over `(R' ⊗_R C)_{P₁}`).
-/

open Algebra TensorProduct IsLocalRing

universe u

namespace SemistableReduction.NodeCover

section Generic

variable {R C R' : Type u} [CommRing R] [CommRing C] [CommRing R'] [Algebra R C] [Algebra R R']
  (K_R K_C : Type u) [Field K_R] [Field K_C] [Algebra R K_R] [Algebra C K_C] [Algebra K_R K_C]
  [Algebra R K_C] [IsScalarTower R K_R K_C] [IsScalarTower R C K_C]
  (P : Ideal R') [P.IsPrime]

variable (R C) in
/-- The map `C ⊗_R R' → (K_R ⊗_R R'_P) ⊗_{K_R} K_C`, `c ⊗ r ↦ (1 ⊗ r) ⊗ c`. -/
noncomputable def toTensorTensor :
    C ⊗[R] R' →+* (K_R ⊗[R] Localization.AtPrime P) ⊗[K_R] K_C :=
  (Algebra.TensorProduct.comm K_R K_C (K_R ⊗[R] Localization.AtPrime P)).toAlgHom.toRingHom.comp
    ((Algebra.TensorProduct.cancelBaseChange R K_R K_C K_C
      (Localization.AtPrime P)).symm.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C K_C)
      (IsScalarTower.toAlgHom R R' (Localization.AtPrime P))).toRingHom)

@[simp]
lemma toTensorTensor_tmul (c : C) (r : R') :
    toTensorTensor R C K_R K_C P (c ⊗ₜ r) =
      ((1 : K_R) ⊗ₜ algebraMap R' (Localization.AtPrime P) r) ⊗ₜ algebraMap C K_C c := by
  simp [toTensorTensor, Algebra.TensorProduct.cancelBaseChange_symm_tmul]

end Generic

section Kernel

variable {R C R' : Type u} [CommRing R] [CommRing C] [CommRing R'] [Algebra R C] [Algebra R R']
  [IsLocalRing R] [IsLocalRing C] [Algebra.IsIntegral R C]
  [(maximalIdeal C).LiesOver (maximalIdeal R)]
  (K_R K_C : Type u) [Field K_R] [Field K_C] [Algebra R K_R] [Algebra C K_C] [Algebra K_R K_C]
  [Algebra R K_C] [IsScalarTower R K_R K_C] [IsScalarTower R C K_C]
  (P : Ideal R') [P.IsPrime] [P.LiesOver (maximalIdeal R)]
  (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) (maximalIdeal C)
    (Algebra.ofId R C) ((maximalIdeal C).over_def (maximalIdeal R))))
include hκ

/-- **The kernel of `C ⊗_R R' → F` lies in the prime `P₁` over `P`**, `F` being a field: the
kernel is a prime avoiding the image of `R' ∖ P`, hence contained in a prime over `P`, which is
`P₁` (`eq_of_comap_includeRight_eq`). -/
theorem ker_toTensorTensor_le
    (hF : IsField ((K_R ⊗[R] Localization.AtPrime P) ⊗[K_R] K_C))
    (P₁ : Ideal (C ⊗[R] R')) [P₁.IsPrime]
    (h₁ : P₁.comap (includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P) :
    RingHom.ker (toTensorTensor R C K_R K_C P) ≤ P₁ := by
  have := hF.isDomain
  have : (RingHom.ker (toTensorTensor R C K_R K_C P)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q', hle, hQ', hQ'P⟩ := exists_le_comap_eq P
    (RingHom.ker (toTensorTensor R C K_R K_C P)) (by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hker
    rw [SetLike.mem_coe, RingHom.mem_ker] at hker
    have hu : IsUnit (algebraMap R' (Localization.AtPrime P) r) :=
      IsLocalization.map_units _ (⟨r, hr⟩ : P.primeCompl)
    have : IsUnit (toTensorTensor R C K_R K_C P (includeRight r)) := by
      rw [includeRight_apply, toTensorTensor_tmul, map_one]
      exact (hu.map (includeRight (R := R) (A := K_R))).map
        (includeLeft (R := K_R) (S := K_R) (B := K_C))
    exact this.ne_zero hker)
  rwa [eq_of_comap_includeRight_eq hκ P Q' P₁ hQ'P h₁] at hle

end Kernel

/-- A nonzero element of a ring which is a field is a unit. -/
theorem isUnit_of_isField {A : Type*} [CommRing A] (hA : IsField A) {z : A} (hz : z ≠ 0) :
    IsUnit z := by
  obtain ⟨w, hw⟩ := hA.mul_inv_cancel hz
  exact ⟨⟨z, w, hw, by rw [mul_comm]; exact hw⟩, rfl⟩

section Residue

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] [IsLocalRing R] [IsLocalRing C]

/-- Trivial residue field extension, `Ideal.ResidueField` form. -/
theorem bijective_mapₐ_of_forall_sub_mem [(maximalIdeal C).LiesOver (maximalIdeal R)]
    (h : ∀ c : C, ∃ r : R, c - algebraMap R C r ∈ maximalIdeal C) :
    Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) (maximalIdeal C)
      (Algebra.ofId R C) ((maximalIdeal C).over_def (maximalIdeal R))) := by
  refine ⟨RingHom.injective _, fun y ↦ ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal C) y
  obtain ⟨r, hr⟩ := h c
  refine ⟨algebraMap R _ r, ?_⟩
  rw [Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap, eq_comm, ← sub_eq_zero,
    ← map_sub, Ideal.algebraMap_residueField_eq_zero]
  exact hr

/-- Trivial residue field extension, `IsLocalRing.ResidueField` form. -/
theorem bijective_residueField_map_of_forall_sub_mem [IsLocalHom (algebraMap R C)]
    (h : ∀ c : C, ∃ r : R, c - algebraMap R C r ∈ maximalIdeal C) :
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C)) := by
  refine ⟨RingHom.injective _, fun y ↦ ?_⟩
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := h c
  refine ⟨IsLocalRing.residue R r, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff]
  exact hr

/-- Trivial residue field extension gives congruences `c ≡ r` modulo the maximal ideal. -/
theorem exists_sub_mem_of_bijective [IsLocalHom (algebraMap R C)]
    (hκ' : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C))) :
    ∀ c : C, ∃ r : R, c - algebraMap R C r ∈ maximalIdeal C := by
  intro c
  obtain ⟨r, hr⟩ := hκ'.2 (IsLocalRing.residue C c)
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
  refine ⟨r, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← IsLocalRing.ResidueField.map_residue, hr,
    sub_self]

end Residue

section Main

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C] [IsLocalRing R] [IsLocalRing C]
  [IsDomain C] [IsIntegrallyClosed C] [IsLocalHom (algebraMap R C)] [Module.Finite R C]
  (K_R K_C : Type u) [Field K_R] [Field K_C] [Algebra R K_R]
  [Algebra C K_C] [IsFractionRing C K_C] [Algebra K_R K_C]
  [Algebra R K_C] [IsScalarTower R K_R K_C] [IsScalarTower R C K_C]

/-- **A cover which is finite étale over `C` embeds, over an étale neighbourhood of `R`, into the
compositum.** Let `R → C` be a finite local homomorphism of integrally closed local domains with
trivial residue field extension, `L₁ ⊇ K_C` a field whose normalisation `B₁` over `C` is finite
étale, and `L ⊆ L₁` a subfield over `K_R`. Then there are an étale `R`-algebra `R'`, a prime `P`
of `R'` over the closed point, a prime `P₁` of `C ⊗_R R'` over `P`, and a `K_R`-embedding
`L → (K_R ⊗_R R'_P) ⊗_{K_R} K_C`. -/
theorem exists_algHom_tensorTensor
    (hκ' : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C)))
    (L : Type u) [Field L] [Algebra K_R L]
    (L₁ : Type u) [Field L₁] [Algebra K_C L₁] [Algebra L L₁] [Algebra K_R L₁]
    [IsScalarTower K_R K_C L₁] [IsScalarTower K_R L L₁]
    (B₁ : Type u) [CommRing B₁] [Algebra C B₁] [Algebra B₁ L₁] [Algebra C L₁]
    [IsScalarTower C B₁ L₁] [IsScalarTower C K_C L₁] [IsIntegralClosure B₁ C L₁]
    [IsFractionRing B₁ L₁] [Module.Finite C B₁] [Algebra.Etale C B₁] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver (maximalIdeal R))
      (P₁ : Ideal (C ⊗[R] R')) (_ : P₁.IsPrime)
      (_ : P₁.comap (includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P),
      Nonempty (L →ₐ[K_R] (K_R ⊗[R] Localization.AtPrime P) ⊗[K_R] K_C) := by
  have hCL : Function.Injective (algebraMap C L₁) := by
    rw [IsScalarTower.algebraMap_eq C K_C L₁]
    exact (algebraMap K_C L₁).injective.comp (IsFractionRing.injective C K_C)
  have hCB : Function.Injective (algebraMap C B₁) := by
    refine fun x y hxy ↦ hCL ?_
    rw [IsScalarTower.algebraMap_apply C B₁ L₁, hxy, ← IsScalarTower.algebraMap_apply]
  have : IsDomain B₁ := (IsIntegralClosure.algebraMap_injective B₁ C L₁).isDomain _
  have : Algebra.IsIntegral C B₁ := IsIntegralClosure.isIntegral_algebra C L₁
  have : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have hκ := bijective_mapₐ_of_forall_sub_mem (exists_sub_mem_of_bijective hκ')
  -- a prime of `B₁` over the closed point of `C`
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B₁)
    (maximalIdeal C) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hCB]
      exact bot_le)
  have : Q.LiesOver (maximalIdeal C) := ⟨hQo.symm⟩
  letI : Algebra R B₁ := ((algebraMap C B₁).comp (algebraMap R C)).toAlgebra
  have : IsScalarTower R C B₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨R', _, _, _, P, _, _, P₁', _, hP₁', ψ, hψ⟩ :=
    EtaleSplit.exists_etale_section (R := R) (C := C) (B := B₁) hκ' Q
  -- the prime of `C ⊗_R R'` over `P`
  let σ : C ⊗[R] R' ≃ₐ[R] R' ⊗[R] C := Algebra.TensorProduct.comm R C R'
  set P₁ : Ideal (C ⊗[R] R') := P₁'.comap σ.toRingEquiv.toRingHom
  have : P₁.IsPrime := Ideal.comap_isPrime _ _
  have h₁ : P₁.comap (includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P := by
    rw [Ideal.comap_comap]
    have : σ.toRingEquiv.toRingHom.comp (includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom =
        algebraMap R' (R' ⊗[R] C) := by
      ext r
      simp [σ]
    rw [this]
    exact hP₁'.over.symm
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance, inferInstance, P₁,
    inferInstance, h₁, ?_⟩
  have hF := isField_tensor_tensor K_R K_C P hκ P₁ h₁
  have := hF.isDomain
  set F := (K_R ⊗[R] Localization.AtPrime P) ⊗[K_R] K_C
  -- the map from the local ring `(R' ⊗_R C)_{P₁'}`
  let γ : R' ⊗[R] C →+* F := (toTensorTensor R C K_R K_C P).comp σ.symm.toRingEquiv.toRingHom
  have hγ : ∀ y : P₁'.primeCompl, IsUnit (γ y) := by
    rintro ⟨y, hy⟩
    refine isUnit_of_isField hF fun h0 ↦ hy ?_
    have : σ.symm y ∈ P₁ :=
      ker_toTensorTensor_le K_R K_C P hκ hF P₁ h₁ (RingHom.mem_ker.mpr h0)
    simpa [P₁] using this
  let β : Localization.AtPrime P₁' →+* F := IsLocalization.lift hγ
  let θ : B₁ →+* F := β.comp ψ
  have hθC : ∀ c : C, θ (algebraMap C B₁ c) = includeRight (algebraMap C K_C c) := by
    intro c
    have h1 : ψ (algebraMap C B₁ c) = algebraMap (R' ⊗[R] C) (Localization.AtPrime P₁')
        (includeRight c) := congr($hψ c)
    simp only [θ, RingHom.comp_apply, h1, β, IsLocalization.lift_eq, γ]
    simp [σ]
    rfl
  -- `θ` is injective
  have hθ : Function.Injective θ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    have : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime _
    refine Ideal.eq_bot_of_comap_eq_bot (R := C) ?_
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker, hθC] at hc
    have h2 : algebraMap C K_C c = 0 := (includeRight : K_C →ₐ[K_R] F).toRingHom.injective
      (by simpa using hc)
    exact (Submodule.mem_bot C).mpr ((IsFractionRing.injective C K_C) (by simpa using h2))
  let lam : L₁ →+* F := IsLocalization.lift (M := nonZeroDivisors B₁) (S := L₁) (g := θ)
    fun y ↦ isUnit_of_isField hF fun h0 ↦ nonZeroDivisors.ne_zero y.2 (hθ (by rw [h0, map_zero]))
  have hlamC : lam.comp (algebraMap K_C L₁) = (includeRight : K_C →ₐ[K_R] F).toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors C) (RingHom.ext fun c ↦ ?_)
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply C B₁ L₁]
    simp only [lam, IsLocalization.lift_eq, hθC]
    rfl
  refine ⟨{ lam.comp (algebraMap L L₁) with commutes' := fun k ↦ ?_ }⟩
  change lam (algebraMap L L₁ (algebraMap K_R L k)) = algebraMap K_R F k
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K_R K_C L₁,
    ← RingHom.comp_apply lam, hlamC]
  exact (includeRight : K_C →ₐ[K_R] F).commutes k

end Main

end SemistableReduction.NodeCover
