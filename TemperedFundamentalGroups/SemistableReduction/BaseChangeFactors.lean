/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.IntegralClosureBaseChange
import TemperedFundamentalGroups.SemistableReduction.ProductNormalisation
import TemperedFundamentalGroups.SemistableReduction.GaloisFactor

/-!
# The product-of-fields reduction for the base change `O → O'` (MR12 S5.7, item 3)

Let `O → O'` be finite étale and faithfully flat, `R` an `O`-algebra which is a domain with
fraction field `K`, and `L / K` a finite Galois extension. After the base change:

* **`isLocalization_baseChange`**: `O' ⊗_O K` is the localization of `O' ⊗_O R` at the image of
  `M` (for `K` the localization of `R` at `M`), through `(O' ⊗_O R) ⊗_R K ≃ O' ⊗_O K`;
* **`isFractionRing_baseChange`**, **`isField_baseChange`**: if `O' ⊗_O R` is a domain (for the
  Tate charts: `TateTwoChart.isDomain_T1` over `O'`), then `O' ⊗_O K` is a field, the fraction
  field of `O' ⊗_O R` (it is a domain, being a localization at non-zero elements, and artinian,
  being finite over `K`);
* **`isArtinianRing_baseChange`**, **`isReduced_baseChange`**: `O' ⊗_O L` is reduced artinian
  (finite étale over the field `L`), hence the finite product of its residue fields;
* **`isGalois_finrank_dvd_factor`**: every field factor `F` of `O' ⊗_O L` (a surjection
  `f : O' ⊗_O L → F`), viewed over any field `K'` between `O'` (resp. `K`) and `F`, e.g.
  `K' = O' ⊗_O K`, is Galois over `K'` of degree dividing `[L : K]`: it is generated over `O'`
  by the image of `L` (`GaloisFactor`);
* **`isFractionRing_baseChange_of_equiv`**: the same for `T' ≃ O' ⊗_O R` a domain;
* **`factorNorm`**, **`isIntegralClosure_factor`**, **`mem_factorNorm`**: for a field factor
  `f : O' ⊗_O L → F` and `T'` an `O'`-algebra with `O' ⊗_O R ≃ T'`, the image of the integral
  closure of `T'` in `O' ⊗_O L` is the normalisation of `T'` in `F`; if `B` is the normalisation
  of `R` in `L`, its elements are the images of `O' ⊗_O B`
  (`isIntegralClosure_baseChange_of_equiv` and `map_integralClosure_eq_of_surjective`);
* **`TateTwoChart.isIntegralClosure_factorT0/T1`**,
  **`TateTwoChart.isFractionRing_baseChangeT0/T1`**: the Tate charts.

So the S5 hypotheses (`L` a field, finite Galois over the function field, `[L : K]` prime to `q`
and dividing `e`, `B_i` the normalisations of the charts) hold for each factor of `O' ⊗_O L`
over the base-changed Tate model, with `B_i` replaced by the images of `O' ⊗_O B_i`.
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

namespace BaseChangeFactors

variable (O O' : Type u) [CommRing O] [CommRing O'] [Algebra O O']

section Localization

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R : Type u) [CommRing R] [Algebra O R] (K : Type*) [Field K] [Algebra O K]
  [Algebra R K] [IsScalarTower O R K]

/-- `(O' ⊗_O R) ⊗_R K ≃ O' ⊗_O K` as `O' ⊗_O R`-algebras (`O' ⊗_O K` through
`baseChangeAlgebra`). -/
def cancelEquiv :
    @AlgEquiv (O' ⊗[O] R) ((O' ⊗[O] R) ⊗[R] K) (O' ⊗[O] K) _ _ _ _
      (baseChangeAlgebra O O' R K) :=
  letI := baseChangeAlgebra O O' R K
  AlgEquiv.ofRingEquiv (f := (Algebra.IsPushout.cancelBaseChangeAlg O O' R (O' ⊗[O] R) K
    ).toRingEquiv) fun x ↦ by
      refine Eq.trans ?_ (AlgEquiv.apply_symm_apply
        (Algebra.IsPushout.cancelBaseChangeAlg O O' R (O' ⊗[O] R) K) (baseChangeMap O O' R K x))
      rw [cancelBaseChangeAlg_symm_baseChangeMap]
      rfl

/-- **Localization commutes with base change**: if `K` is the localization of `R` at `M`, then
`O' ⊗_O K` is the localization of `O' ⊗_O R` at the image of `M`. -/
theorem isLocalization_baseChange (M : Submonoid R) [IsLocalization M K] :
    @IsLocalization (O' ⊗[O] R) _ (Algebra.algebraMapSubmonoid (O' ⊗[O] R) M) (O' ⊗[O] K) _
      (baseChangeAlgebra O O' R K) := by
  letI := baseChangeAlgebra O O' R K
  exact IsLocalization.isLocalization_of_algEquiv _ (cancelEquiv O O' R K)

variable [Module.FaithfullyFlat O O'] [IsDomain R] [IsDomain (O' ⊗[O] R)]

omit [IsDomain R] [IsDomain (O' ⊗[O] R)] in
/-- The image of `R` in `O' ⊗_O R` (`O'` faithfully flat over `O`) is injective. -/
lemma includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := O) (B := O') R

/-- The image of the non-zero elements of `R` consists of non-zero divisors of `O' ⊗_O R`. -/
lemma algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (O' ⊗[O] R) (nonZeroDivisors R) ≤
      nonZeroDivisors (O' ⊗[O] R) := by
  rintro _ ⟨r, hr, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.coe_ne_zero ⟨r, hr⟩ ?_
  exact includeRight_injective O O' R (h.trans (map_zero _).symm)

variable [Module.Finite O O'] [IsFractionRing R K]

omit [Module.Finite O O'] in
include R in
/-- `O' ⊗_O K` is a domain: a localization of the domain `O' ⊗_O R` at non-zero elements. -/
theorem isDomain_baseChange : IsDomain (O' ⊗[O] K) := by
  letI := baseChangeAlgebra O O' R K
  haveI := isLocalization_baseChange O O' R K (nonZeroDivisors R)
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (O' ⊗[O] K) (algebraMapSubmonoid_le O O' R)

include R in
/-- **`O' ⊗_O K` is a field**: a domain, finite over the field `K`. -/
theorem isField_baseChange : IsField (O' ⊗[O] K) := by
  haveI := isDomain_baseChange O O' R K
  haveI : IsArtinianRing (K ⊗[O] O') := isArtinian_of_tower K inferInstance
  haveI : IsArtinianRing (O' ⊗[O] K) :=
    RingEquiv.isArtinianRing (Algebra.TensorProduct.comm O K O').toRingEquiv
  exact IsArtinianRing.isField_of_isDomain _

/-- **`O' ⊗_O K` is the fraction field of `O' ⊗_O R`.** -/
theorem isFractionRing_baseChange :
    @IsFractionRing (O' ⊗[O] R) _ (O' ⊗[O] K) _ (baseChangeAlgebra O O' R K) := by
  letI := baseChangeAlgebra O O' R K
  haveI := isLocalization_baseChange O O' R K (nonZeroDivisors R)
  have hM := algebraMapSubmonoid_le O O' R
  have hF := isField_baseChange O O' R K
  refine IsLocalization.of_le _ _ hM fun d hd ↦ ?_
  have hne : algebraMap (O' ⊗[O] R) (O' ⊗[O] K) d ≠ 0 := fun h ↦
    nonZeroDivisors.coe_ne_zero ⟨d, hd⟩
      (IsLocalization.injective (O' ⊗[O] K) hM (h.trans (map_zero _).symm))
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
  exact IsUnit.of_mul_eq_one _ hy

omit [IsDomain (O' ⊗[O] R)] in
/-- **`O' ⊗_O K` is the fraction field of `T'`** for `e : O' ⊗_O R ≃ T'` and `T'` a domain
(`T'` acting through `baseChangeAlgebraOfEquiv`). -/
theorem isFractionRing_baseChange_of_equiv {T' : Type*} [CommRing T'] [Algebra O' T']
    [IsDomain T'] (e : O' ⊗[O] R ≃ₐ[O'] T') :
    @IsFractionRing T' _ (O' ⊗[O] K) _ (baseChangeAlgebraOfEquiv O O' e K) := by
  haveI : IsDomain (O' ⊗[O] R) := e.toRingEquiv.toMulEquiv.isDomain
  letI := baseChangeAlgebra O O' R K
  haveI := isFractionRing_baseChange O O' R K
  exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (O' ⊗[O] K) e.toRingEquiv).1
    inferInstance

end Localization

section Factors

variable (L : Type u) [Field L] [Algebra O L]

/-- `O' ⊗_O L` is artinian (`O'` finite over `O`, `L` a field). -/
theorem isArtinianRing_baseChange [Module.Finite O O'] : IsArtinianRing (O' ⊗[O] L) :=
  haveI : IsArtinianRing (L ⊗[O] O') := isArtinian_of_tower L inferInstance
  RingEquiv.isArtinianRing (Algebra.TensorProduct.comm O L O').toRingEquiv

/-- `O' ⊗_O L` is reduced (`O'` finite étale over `O`, `L` a field). -/
theorem isReduced_baseChange [Module.Finite O O'] (hO : (algebraMap O O').Etale) :
    IsReduced (O' ⊗[O] L) := by
  haveI : Algebra.Etale O O' := RingHom.etale_algebraMap.mp hO
  haveI : IsReduced (L ⊗[O] O') := Algebra.FormallyUnramified.isReduced_of_field L _
  exact isReduced_of_injective (Algebra.TensorProduct.comm O O' L).toRingHom
    (Algebra.TensorProduct.comm O O' L).injective

/-- `O' ⊗_O L` is generated as an `O'`-algebra by the image of `L`. -/
lemma adjoin_range_includeRight :
    Algebra.adjoin O' (Set.range (Algebra.TensorProduct.includeRight : L →ₐ[O] O' ⊗[O] L)) =
      ⊤ := by
  have h := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := O') (R := O)
    (Set.univ : Set L) (Algebra.adjoin_univ O L)
  rwa [Set.image_univ] at h

variable {O O' L}

/-- **The field factors of `O' ⊗_O L` are Galois of degree dividing `[L : K]`**: let `F` be a
field with a surjection `f : O' ⊗_O L → F` of `O'`-algebras, and `K'` a field with
`O' → K' → F` and `K → K' → F`, compatible with `K → L → F`. Then `F / K'` is Galois and
`[F : K'] ∣ [L : K]`. -/
theorem isGalois_finrank_dvd_factor {K : Type*} [Field K] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] {F K' : Type*} [Field F] [Field K'] [Algebra O' F] [Algebra O' K']
    [Algebra K' F] [IsScalarTower O' K' F] [Algebra K K'] [Algebra K F] [IsScalarTower K K' F]
    (f : O' ⊗[O] L →ₐ[O'] F) (hf : Function.Surjective f)
    (hK : ∀ c : K, f (1 ⊗ₜ algebraMap K L c) = algebraMap K F c) :
    IsGalois K' F ∧ Module.finrank K' F ∣ Module.finrank K L := by
  let ι : L →ₐ[K] F :=
    { toRingHom := f.toRingHom.comp (Algebra.TensorProduct.includeRight : L →ₐ[O] _).toRingHom
      commutes' := hK }
  have hι : ∀ l, ι l = f (1 ⊗ₜ l) := fun _ ↦ rfl
  set S : Set (O' ⊗[O] L) := Set.range (Algebra.TensorProduct.includeRight : L →ₐ[O] O' ⊗[O] L)
  have hS : Algebra.adjoin O' S = ⊤ := adjoin_range_includeRight O O' L
  have h2 : Algebra.adjoin O' (f '' S) ≤ (Algebra.adjoin K' (Set.range ι)).restrictScalars O' := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨l, hι l⟩
  have h : IntermediateField.adjoin K' (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ IntermediateField.algebra_adjoin_le_adjoin K' _ ?_
    obtain ⟨a, rfl⟩ := hf x
    have ha : a ∈ Algebra.adjoin O' S := by rw [hS]; exact Algebra.mem_top
    have h1 : f a ∈ (Algebra.adjoin O' S).map f := ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    exact h2 h1
  exact ⟨GaloisFactor.isGalois ι h, GaloisFactor.finrank_dvd ι h⟩


end Factors

section Norm

variable (T : Type u) [CommRing T] [Algebra O T] (L : Type u) [Field L] [Algebra O L]
  [Algebra T L] [IsScalarTower O T L] {T' : Type*} [CommRing T'] [Algebra O' T']
  (e : O' ⊗[O] T ≃ₐ[O'] T') {F : Type*} [Field F] [Algebra T' F]

/-- **The normalisation of `T'` in a field factor `F` of `O' ⊗_O L`**: the image under
`f : O' ⊗_O L → F` of the integral closure of `T'` in `O' ⊗_O L` (`T'` acting through
`e : O' ⊗_O T ≃ T'`). -/
def factorNorm (f : @AlgHom T' (O' ⊗[O] L) F _ _ _ (baseChangeAlgebraOfEquiv O O' e L) _) :
    Subalgebra T' F :=
  letI := baseChangeAlgebraOfEquiv O O' e L
  (integralClosure T' (O' ⊗[O] L)).map f

variable {T L e}

/-- **The normalisation in a factor is the integral closure**: for `O → O'` finite étale and a
surjection `f : O' ⊗_O L → F` onto a field, `factorNorm e f` is the integral closure of `T'` in
`F`. -/
theorem isIntegralClosure_factor [Module.Finite O O'] (hO : (algebraMap O O').Etale)
    (f : @AlgHom T' (O' ⊗[O] L) F _ _ _ (baseChangeAlgebraOfEquiv O O' e L) _)
    (hf : Function.Surjective f) : IsIntegralClosure (factorNorm O O' T L e f) T' F := by
  letI := baseChangeAlgebraOfEquiv O O' e L
  haveI := isArtinianRing_baseChange O O' L
  haveI := isReduced_baseChange O O' L hO
  have h : factorNorm O O' T L e f = integralClosure T' F :=
    map_integralClosure_eq_of_surjective f hf
  rw [h]
  infer_instance

/-- **The normalisation in a factor is the image of `O' ⊗_O B`**: if `B` is the integral closure
of `T` in `L` and `O → O'` is étale, the elements of `factorNorm e f` are the images of
`O' ⊗_O B`. -/
theorem mem_factorNorm (hO : (algebraMap O O').Etale) (B : Type*) [CommRing B] [Algebra O B]
    [Algebra T B] [Algebra B L] [IsScalarTower O T B] [IsScalarTower O B L] [IsScalarTower T B L]
    [IsIntegralClosure B T L]
    (f : @AlgHom T' (O' ⊗[O] L) F _ _ _ (baseChangeAlgebraOfEquiv O O' e L) _) (x : F) :
    x ∈ factorNorm O O' T L e f ↔ ∃ b : O' ⊗[O] B, f (baseChangeMap O O' B L b) = x := by
  letI := baseChangeAlgebraOfEquiv O O' e L
  letI := baseChangeAlgebra O O' B L
  have hB : IsIntegralClosure (O' ⊗[O] B) T' (O' ⊗[O] L) :=
    isIntegralClosure_baseChange_of_equiv O O' T L B hO e
  change x ∈ (integralClosure T' (O' ⊗[O] L)).map f ↔ _
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := (hB.isIntegral_iff (R := T')).1 hy
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨_, (hB.isIntegral_iff (R := T')).2 ⟨b, rfl⟩, rfl⟩

end Norm

end BaseChangeFactors

namespace TateTwoChart

open BaseChangeFactors

variable {O : Type u} [CommRing O] (π b₄ t κ : O) (O' : Type u) [CommRing O'] [Algebra O O']
  (L : Type u) [Field L] [Algebra O L] {F : Type*} [Field F]

/-- **The normalisation of `T0'` in a field factor of `O' ⊗_O L`** is the integral closure
(`factorNorm`, `T0'` acting through `baseChangeT0`). -/
theorem isIntegralClosure_factorT0 [Module.Finite O O'] (hO : (algebraMap O O').Etale)
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower O (T0 π b₄ t κ) L]
    [Algebra (T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
      (algebraMap O O' κ)) F]
    (f : @AlgHom (T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
      (algebraMap O O' κ)) (O' ⊗[O] L) F _ _ _
      (baseChangeAlgebraOfEquiv O O' (baseChangeT0 π b₄ t κ O') L) _)
    (hf : Function.Surjective f) :
    IsIntegralClosure (factorNorm O O' (T0 π b₄ t κ) L (baseChangeT0 π b₄ t κ O') f)
      (T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ)) F :=
  isIntegralClosure_factor O O' hO f hf

/-- **The normalisation of `T1'` in a field factor of `O' ⊗_O L`** is the integral closure
(`factorNorm`, `T1'` acting through `baseChangeT1`). -/
theorem isIntegralClosure_factorT1 [Module.Finite O O'] (hO : (algebraMap O O').Etale)
    [Algebra (T1 π b₄ t κ) L] [IsScalarTower O (T1 π b₄ t κ) L]
    [Algebra (T1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
      (algebraMap O O' κ)) F]
    (f : @AlgHom (T1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
      (algebraMap O O' κ)) (O' ⊗[O] L) F _ _ _
      (baseChangeAlgebraOfEquiv O O' (baseChangeT1 π b₄ t κ O') L) _)
    (hf : Function.Surjective f) :
    IsIntegralClosure (factorNorm O O' (T1 π b₄ t κ) L (baseChangeT1 π b₄ t κ O') f)
      (T1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ)) F :=
  isIntegralClosure_factor O O' hO f hf

/-- **The function field after base change**: if `T1'` (the chart over `O'`) is a domain and
`K` is the fraction field of `T1`, then `O' ⊗_O K` is the fraction field of `T1'`. -/
theorem isFractionRing_baseChangeT1 [Module.FaithfullyFlat O O'] [Module.Finite O O']
    [IsDomain (T1 π b₄ t κ)]
    [IsDomain (T1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
      (algebraMap O O' κ))]
    (K : Type*) [Field K] [Algebra O K] [Algebra (T1 π b₄ t κ) K]
    [IsScalarTower O (T1 π b₄ t κ) K] [IsFractionRing (T1 π b₄ t κ) K] :
    @IsFractionRing
      (T1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ)) _
      (O' ⊗[O] K) _ (baseChangeAlgebraOfEquiv O O' (baseChangeT1 π b₄ t κ O') K) :=
  isFractionRing_baseChange_of_equiv O O' _ K _

/-- **The function field after base change**, chart `T0`. -/
theorem isFractionRing_baseChangeT0 [Module.FaithfullyFlat O O'] [Module.Finite O O']
    [IsDomain (T0 π b₄ t κ)]
    [IsDomain (T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
      (algebraMap O O' κ))]
    (K : Type*) [Field K] [Algebra O K] [Algebra (T0 π b₄ t κ) K]
    [IsScalarTower O (T0 π b₄ t κ) K] [IsFractionRing (T0 π b₄ t κ) K] :
    @IsFractionRing
      (T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ)) _
      (O' ⊗[O] K) _ (baseChangeAlgebraOfEquiv O O' (baseChangeT0 π b₄ t κ O') K) :=
  isFractionRing_baseChange_of_equiv O O' _ K _

end TateTwoChart

end

end SemistableReduction
