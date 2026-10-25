/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeCoverSplitNode
import TemperedFundamentalGroups.SemistableReduction.Purity
import TemperedFundamentalGroups.SemistableReduction.TameChart

/-!
# Auxiliary lemmas for "S4-local" over local rings étale over the node

* `EtaleNbhd.isDomain_localization`, `EtaleNbhd.isIntegrallyClosed_localization`,
  `EtaleNbhd.isNoetherianRing_localization`: a local localization `T = B_S` of an étale algebra
  `B` over a (Noetherian) integrally closed domain `A` is a (Noetherian) integrally closed domain,
  with fraction field `T ⊗_A Frac A`.
* `EtaleNbhd.maximalIdeal_eq_span_pair`, `EtaleNbhd.prime_algebraMap`,
  `EtaleNbhd.algebraMap_notMem_span`: if moreover `A` is local with `m_A = (x, y)`, `x` prime,
  `y ∉ (x)`, and `A → T` is local, the same holds in `T`.
-/

open Algebra TensorProduct IsLocalRing

namespace SemistableReduction.NodeCover.EtaleNbhd

/-- A localization of a domain which is a field is a fraction field of the domain (a copy of
`SemistableReduction.isFractionRing_of_isLocalization_of_isField`, which lives in a file not
imported here). -/
theorem isFractionRing_of_isField {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (hB : IsField B) :
    IsFractionRing A B := by
  letI := hB.toField
  have hS : S ≤ nonZeroDivisors A := fun x hx ↦ mem_nonZeroDivisors_of_ne_zero fun h0 ↦ by
    have hu : IsUnit (algebraMap A B x) := IsLocalization.map_units B ⟨x, hx⟩
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  have hinj := IsLocalization.injective B hS
  refine IsLocalization.of_le S _ hS fun r hr ↦ IsUnit.mk0 _ fun h ↦
    nonZeroDivisors.ne_zero hr (hinj ?_)
  rw [h, map_zero]

section Domain

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
  [Algebra A B] [Algebra.Etale A B] (S : Submonoid B) [IsLocalRing (Localization S)]

local notation "T" => Localization S
local notation "K" => FractionRing A

omit [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing (Localization S)] in
lemma includeLeft_injective :
    Function.Injective (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] K) :=
  Algebra.TensorProduct.includeLeft_injective (S := A) (IsFractionRing.injective A K)

variable (A) in
include A in
/-- A local localization of an étale algebra over an integrally closed domain is a domain. -/
theorem isDomain_localization : IsDomain T := by
  letI := (isField_tensor_of_isLocalization A S K).toField
  exact (includeLeft_injective (A := A) S).isDomain _

variable (A) in
include A in
/-- Its generic fibre `T ⊗_A Frac A` is a fraction field of `T`. -/
theorem isFractionRing_tensor : IsFractionRing T (T ⊗[A] K) := by
  have := isDomain_localization A S
  haveI : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors A)) (T ⊗[A] K) :=
    IsLocalization.tensor (S := T) K (nonZeroDivisors A)
  exact isFractionRing_of_isField (Algebra.algebraMapSubmonoid T (nonZeroDivisors A))
    (isField_tensor_of_isLocalization A S K)

variable (A) in
include A in
/-- A local localization of an étale algebra over an integrally closed domain is integrally
closed. -/
theorem isIntegrallyClosed_localization : IsIntegrallyClosed T := by
  have := isDomain_localization A S
  have := isFractionRing_tensor A S
  refine (isIntegrallyClosed_iff (T ⊗[A] K)).mpr fun {e} he ↦ ?_
  obtain ⟨d, hd⟩ := exists_eq_tmul_one_of_isIntegral' S K he
  exact ⟨d, hd⟩

variable (A) in
include A in
/-- `A → T` is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap A T) := by
  letI := (isField_tensor_of_isLocalization A S K).toField
  intro a b h
  apply IsFractionRing.injective A K
  apply (Algebra.TensorProduct.includeRight : K →ₐ[A] T ⊗[A] K).toRingHom.injective
  have h' := congrArg (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] K) h
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] using h'

omit [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing (Localization S)] in
/-- A localization of an étale algebra over a Noetherian ring is Noetherian. -/
theorem isNoetherianRing_localization [IsNoetherianRing A] : IsNoetherianRing T := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact IsLocalization.isNoetherianRing S T inferInstance

end Domain

section Regular

open RingTheory.Sequence

/-- **A regular pair stays regular under flat base change** (elementwise form): if `x` is prime
in the domain `A`, `y ∉ (x)` and `T` is flat over `A`, then `y t ∈ x T` implies `t ∈ x T`. -/
theorem mem_span_of_mul_mem {A T : Type*} [CommRing A] [IsDomain A] [CommRing T] [Algebra A T]
    [Module.Flat A T] {x y : A} (hx : Prime x) (hy : y ∉ Ideal.span {x}) {t : T}
    (ht : algebraMap A T y * t ∈ Ideal.span {algebraMap A T x}) :
    t ∈ Ideal.span {algebraMap A T x} := by
  have h1 : IsWeaklyRegular A ([x, y] : List A) := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
    refine ⟨fun a b hab ↦ mul_left_cancel₀ hx.ne_zero hab, fun a b hab ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    simp only at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      ← smul_sub, Submodule.mem_smul_pointwise_iff_exists] at hab
    rw [Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
    obtain ⟨w, -, hw⟩ := hab
    have hdvd : x ∣ y * (a - b) := ⟨w, by simpa only [smul_eq_mul] using hw.symm⟩
    rcases hx.dvd_or_dvd hdvd with h | ⟨c, hc⟩
    · exact absurd (Ideal.mem_span_singleton.mpr h) hy
    · exact ⟨c, Submodule.mem_top, by rw [hc, smul_eq_mul]⟩
  have h2 : IsWeaklyRegular (A ⊗[A] T) ([x, y] : List A) := h1.isWeaklyRegular_rTensor
  have h3 : IsWeaklyRegular T ([x, y] : List A) :=
    (LinearEquiv.isWeaklyRegular_congr (TensorProduct.lid A T) _).mp h2
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h3
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp ht
  have key : y • (Submodule.Quotient.mk t : QuotSMulTop x T) =
      y • (Submodule.Quotient.mk 0 : QuotSMulTop x T) := by
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      smul_zero, sub_zero, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨w, Submodule.mem_top, by rw [Algebra.smul_def, Algebra.smul_def, mul_comm, hw]⟩
  have := h3.2 key
  rw [Submodule.Quotient.eq, sub_zero, Submodule.mem_smul_pointwise_iff_exists] at this
  obtain ⟨c, -, hc⟩ := this
  exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [← hc, Algebra.smul_def, mul_comm]⟩

variable {A T : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
  [Algebra A T] [Module.Flat A T] [IsLocalHom (algebraMap A T)]
  {x y : A} (hx : Prime x) (hy : y ∉ Ideal.span {x}) (hm : maximalIdeal A = Ideal.span {x, y})

include hm in
omit [IsDomain A] [Module.Flat A T] in
/-- **The maximal ideal of an unramified local extension** of a local ring with
`m = (x, y)` is generated by the images of `x` and `y`. -/
theorem maximalIdeal_eq_span_pair [Algebra.FormallyUnramified A T] [Algebra.EssFiniteType A T] :
    maximalIdeal T = Ideal.span {algebraMap A T x, algebraMap A T y} := by
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A), hm, Ideal.map_span,
    Set.image_pair]

include hm in
omit [IsDomain A] [Module.Flat A T] in
lemma algebraMap_mem_maximalIdeal : algebraMap A T x ∈ maximalIdeal T :=
  map_nonunit (algebraMap A T) x ((mem_maximalIdeal x).mp (hm ▸ Ideal.subset_span (by simp)))

include hm in
omit [IsDomain A] [Module.Flat A T] in
lemma span_ne_top : Ideal.span {algebraMap A T x} ≠ ⊤ := fun h ↦
  (maximalIdeal.isMaximal T).ne_top (top_le_iff.mp
    (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr (algebraMap_mem_maximalIdeal hm)))

include hx hy hm in
/-- `y ∉ x T`. -/
theorem algebraMap_notMem_span : algebraMap A T y ∉ Ideal.span {algebraMap A T x} := fun h ↦
  span_ne_top hm ((Ideal.eq_top_iff_one _).mpr
    (mem_span_of_mul_mem (T := T) hx hy (by rwa [mul_one])))

include hx hy hm in
/-- `x T` is a prime ideal: `T / x T` is a Noetherian local ring whose maximal ideal is generated
by the non-zero-divisor `y`, hence a domain. -/
theorem isPrime_span [IsNoetherianRing T] [Algebra.FormallyUnramified A T]
    [Algebra.EssFiniteType A T] : (Ideal.span {algebraMap A T x}).IsPrime := by
  set I := Ideal.span {algebraMap A T x}
  haveI : Nontrivial (T ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (span_ne_top hm)
  haveI : IsLocalRing (T ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hc : (maximalIdeal (T ⧸ I)).comap (Ideal.Quotient.mk I) = maximalIdeal T :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hx0 : Ideal.Quotient.mk I (algebraMap A T x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hmQ : maximalIdeal (T ⧸ I) = Ideal.span {Ideal.Quotient.mk I (algebraMap A T y)} := by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective (maximalIdeal (T ⧸ I)),
      hc, maximalIdeal_eq_span_pair hm, Ideal.map_span, Set.image_pair, hx0,
      Ideal.span_insert_zero]
  have hreg : IsSMulRegular (T ⧸ I) (Ideal.Quotient.mk I (algebraMap A T y)) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [smul_eq_mul, ← map_mul] at hab
    rw [Ideal.Quotient.eq] at hab ⊢
    rw [← mul_sub] at hab
    exact mem_span_of_mul_mem hx hy hab
  have := IsLocalRing.isDomain_of_maximalIdeal_eq_span hmQ hreg
  exact (Ideal.Quotient.isDomain_iff_prime I).mp this

include hx hy hm in
/-- `x` stays prime in `T` (given that `A → T` is injective). -/
theorem prime_algebraMap [IsNoetherianRing T] [Algebra.FormallyUnramified A T]
    [Algebra.EssFiniteType A T] (hinj : Function.Injective (algebraMap A T)) :
    Prime (algebraMap A T x) := by
  have h0 : algebraMap A T x ≠ 0 := fun h ↦ hx.ne_zero (hinj (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime h0).mp (isPrime_span hx hy hm)

end Regular

section Transfer

variable {T C : Type*} [CommRing T] [CommRing C] [IsLocalRing T] [IsLocalRing C]

/-- The maximal ideal is transported along ring isomorphisms of local rings. -/
theorem maximalIdeal_eq_map (f : T ≃+* C) :
    maximalIdeal C = (maximalIdeal T).map (f : T →+* C) := by
  have h : (maximalIdeal C).comap (f : T →+* C) = maximalIdeal T :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ f.surjective)
  rw [← h]
  exact (Ideal.map_comap_of_surjective _ f.surjective _).symm

/-- "Regular of dimension two" data are transported along ring isomorphisms. -/
theorem regularPair_of_ringEquiv (f : T ≃+* C) {x y : T} (hx : Prime x)
    (hy : y ∉ Ideal.span {x}) (hm : maximalIdeal T = Ideal.span {x, y}) :
    Prime (f x) ∧ f y ∉ Ideal.span {f x} ∧ maximalIdeal C = Ideal.span {f x, f y} := by
  refine ⟨(MulEquiv.prime_iff f.toMulEquiv).mpr hx, fun h ↦ hy ?_, ?_⟩
  · rw [Ideal.mem_span_singleton] at h ⊢
    simpa using map_dvd (f.symm : C →+* T) h
  · rw [maximalIdeal_eq_map f, hm, Ideal.map_span, Set.image_pair]
    rfl

end Transfer

section Height

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]

omit [CommRing R] [Algebra R C] in
/-- In a Noetherian local ring with maximal ideal `(x, y)`, a prime other than the maximal ideal
has height at most one. -/
theorem height_le_one_of_ne {x y : C} [IsLocalRing C] [IsNoetherianRing C]
    (hm : maximalIdeal C = Ideal.span {x, y}) (P₀ : Ideal C) [P₀.IsPrime]
    (hP₀ : P₀ ≠ maximalIdeal C) : P₀.height ≤ 1 := by
  classical
  have h2 : (maximalIdeal C).height ≤ 2 := by
    have hmin : maximalIdeal C ∈ (Ideal.span (({x, y} : Finset C) : Set C)).minimalPrimes := by
      rw [Finset.coe_insert, Finset.coe_singleton, ← hm]
      rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _
    exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans
      (by exact_mod_cast Finset.card_le_two)
  have hlt : P₀ < maximalIdeal C :=
    lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hP₀
  have h3 := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans h2
  exact (ENat.add_le_add_iff_right (k := 1) (by simp)).mp (h3.trans (by norm_num))

omit [CommRing R] [Algebra R C] in
theorem comap_ne_maximalIdeal [CommRing R] [Algebra R C] [IsLocalRing R] [IsLocalRing C]
    [Algebra.IsIntegral R C] (P₀ : Ideal C) [P₀.IsPrime] (hP₀ : P₀ ≠ maximalIdeal C) :
    P₀.comap (algebraMap R C) ≠ maximalIdeal R := fun h ↦ by
  have : P₀.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [h]; infer_instance)
  exact hP₀ (IsLocalRing.eq_maximalIdeal this)

/-- **Height bound by going down**: if `R ⊆ C` is integral, `R` an integrally closed domain,
`C` a Noetherian local domain with maximal ideal `(x, y)`, then a prime `P₀ ≠ m_C` contracts to
a prime of height at most one. -/
theorem height_comap_le_one [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [IsDomain C]
    [IsLocalRing C] [IsNoetherianRing C] [FaithfulSMul R C] [Algebra.IsIntegral R C] {x y : C}
    (hm : maximalIdeal C = Ideal.span {x, y}) (P₀ : Ideal C) [P₀.IsPrime]
    (hP₀ : P₀ ≠ maximalIdeal C) : (P₀.comap (algebraMap R C)).height ≤ 1 := by
  have : P₀.LiesOver (P₀.comap (algebraMap R C)) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (P₀.comap (algebraMap R C)) P₀
  exact le_trans (h ▸ le_self_add) (height_le_one_of_ne hm P₀ hP₀)

end Height

section Etale

/-- **Purity and base change** (the hypothesis `hEt` of
`NodeCover.exists_etale_tensor_algEquiv_pi_of_etale`, for a general integral extension of the
base): let `A ⊆ A'` be an integral extension of Noetherian integrally closed local domains, with
`m_{A'} = (x, y)`, `x` prime, `y ∉ (x)`, `L / Frac A` finite separable whose normalisation `B`
over `A` is unramified over the punctured spectrum of `A`, and `L₁` a field generated by `L` and
`Frac A'`, finite separable over `Frac A'`. Then the normalisation of `A'` in `L₁` is étale
over `A'`. -/
theorem etale_integralClosure_of_baseChange
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsLocalRing A]
    {A' : Type*} [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A']
    [IsIntegrallyClosed A'] [Algebra A A'] [Algebra.IsIntegral A A'] [FaithfulSMul A A']
    {x y : A'} (hx : Prime x) (hy : y ∉ Ideal.span {x}) (hm : maximalIdeal A' = Ideal.span {x, y})
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type*) [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K'] [IsScalarTower A A' K']
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type*) [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsUnramifiedAt A Q)
    (L₁ : Type*) [Field L₁] [Algebra K L₁] [Algebra K' L₁] [Algebra L L₁]
    [IsScalarTower K K' L₁] [IsScalarTower K L L₁] [Algebra A' L₁]
    [IsScalarTower A' K' L₁] [FiniteDimensional K' L₁] [Algebra.IsSeparable K' L₁]
    (hgen : Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom K L L₁) (IsScalarTower.toAlgHom K K' L₁))) :
    Algebra.Etale A' (integralClosure A' L₁) := by
  refine Purity.etale_of_isUnramifiedAt_of_maximalIdeal_eq_span_pair K' L₁ hx hy hm
    fun Q₁ _ hQ₁ ↦ ?_
  set P₀ := Q₁.comap (algebraMap A' (integralClosure A' L₁))
  have h𝔭 : P₀.comap (algebraMap A A') ≠ maximalIdeal A := comap_ne_maximalIdeal P₀ hQ₁
  exact isUnramifiedAt_of_baseChange (K := K) (K' := K') (L := L) (B := B)
    (P₀.comap (algebraMap A A')) hgen (height_comap_le_one hm P₀ hQ₁)
    (fun Q _ hQ ↦ hunr Q fun h ↦
      h𝔭 (le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) (h ▸ hQ)))
    Q₁ rfl

end Etale

/-- A field homomorphism into a fraction field of `A` whose image contains `A` is surjective. -/
theorem surjective_of_forall_exists {A K F : Type*} [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field F] (f : F →+* K) (h : ∀ a : A, ∃ u, f u = algebraMap A K a) :
    Function.Surjective f := by
  intro k
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective A k
  obtain ⟨u, hu⟩ := h a
  obtain ⟨v, hv⟩ := h s
  exact ⟨u / v, by rw [map_div₀, hu, hv]⟩

/-- A local ring which is integral over a local ring is a local extension. -/
theorem isLocalHom_of_isIntegral {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [IsLocalRing R] [IsLocalRing C] [Algebra.IsIntegral R C] : IsLocalHom (algebraMap R C) := by
  have h : (maximalIdeal C).comap (algebraMap R C) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  exact ((IsLocalRing.local_hom_TFAE (algebraMap R C)).out 0 4).mpr h

end SemistableReduction.NodeCover.EtaleNbhd
