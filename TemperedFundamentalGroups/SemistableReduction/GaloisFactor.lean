/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Factors of the base change of a Galois extension (MR12 S5.7, item 3)

Let `L / K` be a finite Galois extension and `K'` an extension of `K`. A factor `F` of
`K' ⊗_K L` (a field receiving `K'` and `L` and generated over `K'` by the image of `L`) is
again Galois over `K'`, and its degree divides `[L : K]`: restriction to the image of `L` embeds
`Gal(F / K')` into `Gal(L / K)`.

* **`GaloisFactor.isGalois`**: `F / K'` is Galois;
* **`GaloisFactor.finrank_dvd`**: `[F : K'] ∣ [L : K]`;
* **`GaloisFactor.adjoin_eq_top_of_surjective`**: the hypothesis for a field `F` which is a
  quotient (`f : A →ₐ[K'] F` surjective) of a `K'`-algebra `A` generated as a `K'`-algebra by the
  image of `L` (e.g. `F = A ⧸ m`, `A = K' ⊗_K L`).

In S5.7 this is applied to `A = O' ⊗_O L` over `K' = O' ⊗_O K`: the S5 hypotheses `IsGalois`,
`[L : K]` prime to `q` and `[L : K] ∣ e` pass to every factor.
-/

open Module IntermediateField

namespace SemistableReduction

namespace GaloisFactor

variable {K L K' F : Type*} [Field K] [Field L] [Field K'] [Field F] [Algebra K L]
  [Algebra K K'] [Algebra K' F] [Algebra K F] [IsScalarTower K K' F]

/-- If `F` is generated over `K'` by the image of `ι : L → F`, then so is it by the image of a
primitive element of `L / K`. -/
lemma adjoin_simple_eq_top [FiniteDimensional K L] [Algebra.IsSeparable K L] (ι : L →ₐ[K] F)
    (h : adjoin K' (Set.range ι) = ⊤) {α : L} (hα : K⟮α⟯ = ⊤) : K'⟮ι α⟯ = ⊤ := by
  refine eq_top_iff.2 (h.symm.le.trans (adjoin_le_iff.2 ?_))
  rintro _ ⟨x, rfl⟩
  have hx : ι x ∈ (K⟮α⟯.map ι : IntermediateField K F) := ⟨x, by rw [hα]; trivial, rfl⟩
  rw [adjoin_map, Set.image_singleton] at hx
  have hle : K⟮ι α⟯ ≤ (K'⟮ι α⟯).restrictScalars K :=
    adjoin_le_iff.2 (by simp)
  exact hle hx

/-- A factor `F` of the base change of a Galois extension is the splitting field over `K'` of
the minimal polynomial of a primitive element `α` of `L / K`. -/
theorem isSplittingField [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] F)
    (h : adjoin K' (Set.range ι) = ⊤) {α : L} (hα : K⟮α⟯ = ⊤) :
    ((minpoly K α).map (algebraMap K K')).IsSplittingField K' F := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  set p := (minpoly K α).map (algebraMap K K')
  have hsplitL : ((minpoly K α).map (algebraMap K L)).Splits := Normal.splits' α
  have hsplit : (p.map (algebraMap K' F)).Splits := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      show algebraMap K F = (ι : L →+* F).comp (algebraMap K L) from (ι.comp_algebraMap).symm,
      ← Polynomial.map_map]
    exact hsplitL.map _
  have hroot : ι α ∈ p.rootSet F := by
    rw [Polynomial.mem_rootSet, Polynomial.aeval_map_algebraMap]
    refine ⟨(minpoly.monic hint).map _ |>.ne_zero, ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  rw [isSplittingField_iff_intermediateField]
  refine ⟨hsplit, eq_top_iff.2 ?_⟩
  rw [← adjoin_simple_eq_top ι h hα]
  exact adjoin_le_iff.2 (Set.singleton_subset_iff.2 (subset_adjoin _ _ hroot))

/-- A factor of the base change of a finite Galois extension is finite. -/
theorem finiteDimensional [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] F)
    (h : adjoin K' (Set.range ι) = ⊤) : FiniteDimensional K' F := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  haveI := isSplittingField ι h hα
  exact Polynomial.IsSplittingField.finiteDimensional F ((minpoly K α).map (algebraMap K K'))

/-- **A factor of the base change of a Galois extension is Galois.** -/
theorem isGalois [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] F)
    (h : adjoin K' (Set.range ι) = ⊤) : IsGalois K' F := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  haveI := isSplittingField ι h hα
  haveI := finiteDimensional ι h
  exact IsGalois.of_separable_splitting_field (p := (minpoly K α).map (algebraMap K K'))
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K α))

/-- **The degree of a factor of the base change of a Galois extension divides `[L : K]`**:
restriction to the image of `L` embeds `Gal(F / K')` into `Gal(L / K)`. -/
theorem finrank_dvd [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] F)
    (h : adjoin K' (Set.range ι) = ⊤) : finrank K' F ∣ finrank K L := by
  haveI := isGalois ι h
  haveI := finiteDimensional ι h
  set E : IntermediateField K F := ι.fieldRange
  let eE : L ≃ₐ[K] E := AlgEquiv.ofInjectiveField ι
  haveI : IsGalois K E := IsGalois.of_algEquiv eE
  haveI : FiniteDimensional K E := Module.Finite.equiv eE.toLinearEquiv
  let f : Gal(F/K') →* Gal(E/K) :=
    (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : ∀ x ∈ E, σ x = x := (AlgEquiv.restrictNormal_eq_one_iff E _).1 hσ
    have : (σ : F →ₐ[K'] F) = AlgHom.id K' F :=
      AlgHom.ext_of_adjoin_eq_top ((adjoin_eq_top_iff (F := K')).1 h) fun x hx ↦ by
        obtain ⟨l, rfl⟩ := hx
        exact h1 _ ⟨l, rfl⟩
    exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun this x
  have := Subgroup.card_dvd_of_injective f hf
  rwa [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    ← eE.toLinearEquiv.finrank_eq] at this

/-- **The generation hypothesis for a quotient**: if `A` is generated as a `K'`-algebra by the
image of `ι : L → A` and `f : A → F` is surjective, then `F` is generated over `K'` (as a field) by
the image of `f ∘ ι`. -/
theorem adjoin_eq_top_of_surjective {A : Type*} [CommRing A] [Algebra K' A] [Algebra K A]
    [IsScalarTower K K' A] (ι : L →ₐ[K] A) (hA : Algebra.adjoin K' (Set.range ι) = ⊤)
    (f : A →ₐ[K'] F) (hf : Function.Surjective f) :
    adjoin K' (Set.range ((f.restrictScalars K).comp ι)) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ algebra_adjoin_le_adjoin K' _ ?_
  obtain ⟨a, rfl⟩ := hf x
  have ha : a ∈ Algebra.adjoin K' (Set.range ι) := hA ▸ Algebra.mem_top
  have : f a ∈ (Algebra.adjoin K' (Set.range ι)).map f := ⟨a, ha, rfl⟩
  rwa [AlgHom.map_adjoin, ← Set.range_comp] at this

open TensorProduct in
/-- `K' ⊗_K L` is generated as a `K'`-algebra by the image of `L`. -/
lemma adjoin_range_includeRight :
    Algebra.adjoin K' (Set.range (Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L)) = ⊤ := by
  have h := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := K') (R := K) (Set.univ : Set L)
    (Algebra.adjoin_univ K L)
  rwa [Set.image_univ] at h

open TensorProduct in
/-- **The factors of `K' ⊗_K L` are Galois over `K'`, of degree dividing `[L : K]`**: for a
field `F` and a surjective `K'`-algebra map `f : K' ⊗_K L → F` (e.g. `F = (K' ⊗_K L) ⧸ m`). -/
theorem isGalois_finrank_dvd_tensor [FiniteDimensional K L] [IsGalois K L]
    (f : K' ⊗[K] L →ₐ[K'] F) (hf : Function.Surjective f) :
    IsGalois K' F ∧ Module.finrank K' F ∣ Module.finrank K L := by
  have h := adjoin_eq_top_of_surjective (K := K) (K' := K') (F := F) (A := K' ⊗[K] L)
    Algebra.TensorProduct.includeRight adjoin_range_includeRight f hf
  exact ⟨isGalois _ h, finrank_dvd _ h⟩

open TensorProduct in
/-- `K' ⊗_K L` (`L / K` finite separable) is artinian. -/
instance isArtinianRing_tensor [FiniteDimensional K L] : IsArtinianRing (K' ⊗[K] L) :=
  isArtinian_of_tower K' inferInstance

open TensorProduct in
/-- `K' ⊗_K L` (`L / K` finite separable) is reduced (it is étale over `K'`). -/
instance isReduced_tensor [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsReduced (K' ⊗[K] L) := by
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  exact Algebra.FormallyUnramified.isReduced_of_field K' _

end GaloisFactor

end SemistableReduction
