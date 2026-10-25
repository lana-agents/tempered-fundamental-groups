/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeCoverEtaleNbhdBase

/-!
# "S4-local" over a local ring étale over the node (MR12 T2 S4, charts étale over the node)

Proof: apply `NodeCover.exists_etale_tensor_algEquiv_pi_of_etale` to the finite local extension
`R → C = R ⊗_{R_M} R_1` (`C ≅ R_1 ⊗_{R_M} R'_P` is a local localization of an étale
`R_1`-algebra, hence a Noetherian integrally closed domain, regular of dimension two with
`m_C = (x₁, y₁)`), with `K_C = K_R ⊗_{K_M} K_1`; the hypothesis `hEt` is purity on `C` plus
base change (`EtaleNbhd.etale_integralClosure_of_baseChange`).
-/

open Algebra TensorProduct IsLocalRing IntermediateField Module

universe u

namespace SemistableReduction.NodeCover

section EtaleNbhd

variable {R_M R_1 : Type u} [CommRing R_M] [CommRing R_1] [Algebra R_M R_1] [IsLocalRing R_M]
  [IsLocalRing R_1] [IsDomain R_M] [IsIntegrallyClosed R_M] [IsNoetherianRing R_M]
  [IsDomain R_1] [IsIntegrallyClosed R_1] [IsNoetherianRing R_1]
  [IsLocalHom (algebraMap R_M R_1)] [Module.Finite R_M R_1] {M : ℕ} [NeZero M]

set_option maxHeartbeats 1000000 in
-- The many tensor product, localization and fraction field structures make this proof slow.
/-- **"S4-local" over a local ring étale over the node.** Let `R_M → R_1` be as in
`NodeCover.exists_etale_tensor_algEquiv_pi_of_etale` (finite local, trivial residue extension,
`K_1 = K_M(X)`, `X ^ M ∈ K_M`, `[K_1 : K_M] = M`), with `R_1` "regular of dimension two"
(`m = (x₁, y₁)`, `x₁` prime, `y₁ ∉ (x₁)`), and let `R = R'_P` be the local ring of an étale
`R_M`-algebra `R'` at a prime `P` over the closed point, with fraction field `K_R ⊇ K_M`. Let
`L / K_R` be finite Galois of degree prime to `q` (`M = q M'`, `ζ_{M'} ∈ K_R`) whose normalisation
`B` over `R` is unramified over the punctured spectrum of `R`. Then over the function field `E`
of an étale neighbourhood of the closed point of `R`, `L` becomes a product of copies of
`K_R ⊗_{K_M} K_M(X ^ n)`, `n = q (M' / e)`, `e ∣ M'`. -/
theorem exists_etale_tensor_algEquiv_pi_of_etaleNbhd
    (hκ' : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R_M R_1)))
    {x₁ y₁ : R_1} (hx₁ : Prime x₁) (hy₁ : y₁ ∉ Ideal.span {x₁})
    (hm₁ : maximalIdeal R_1 = Ideal.span {x₁, y₁})
    (K_M : Type u) [Field K_M] [Algebra R_M K_M] [IsFractionRing R_M K_M]
    (K_1 : Type u) [Field K_1] [Algebra R_1 K_1] [IsFractionRing R_1 K_1] [Algebra K_M K_1]
    [Algebra R_M K_1] [IsScalarTower R_M K_M K_1] [IsScalarTower R_M R_1 K_1]
    {X : K_1} {x : K_M} (hx : X ^ M = algebraMap K_M K_1 x) (hX : K_M⟮X⟯ = ⊤)
    (hfin : finrank K_M K_1 = M)
    (R' : Type u) [CommRing R'] [Algebra R_M R'] [Algebra.Etale R_M R'] (P : Ideal R')
    [P.IsPrime] [P.LiesOver (maximalIdeal R_M)]
    (R : Type u) [CommRing R] [Algebra R' R] [IsLocalization.AtPrime R P] [IsLocalRing R]
    [Algebra R_M R] [IsScalarTower R_M R' R]
    (K_R : Type u) [Field K_R] [Algebra R K_R] [IsFractionRing R K_R] [Algebra K_M K_R]
    [Algebra R_M K_R] [IsScalarTower R_M K_M K_R] [IsScalarTower R_M R K_R]
    {q M' : ℕ} (hqM : q * M' = M) (hq : 0 < q) (hM' : 0 < M') {ζ : K_R}
    (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K_R L] [Algebra R L] [IsScalarTower R K_R L]
    [FiniteDimensional K_R L] [IsGalois K_R L] (hL : (finrank K_R L).Coprime q)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
    [IsIntegralClosure B R L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap R B) ≠ maximalIdeal R →
      Algebra.IsUnramifiedAt R Q) :
    ∃ (R'' : Type u) (_ : CommRing R'') (_ : Algebra R R'') (_ : Algebra.Etale R R'')
      (P'' : Ideal R'') (_ : P''.IsPrime) (_ : P''.LiesOver (maximalIdeal R)),
      ∃ (E : Type u) (_ : Field E) (_ : Algebra K_R E),
        Nonempty (K_R ⊗[R] Localization.AtPrime P'' ≃ₐ[K_R] E) ∧ ∃ e, e ∣ M' ∧ ∃ r : ℕ,
          Nonempty (E ⊗[K_R] L ≃ₐ[E]
            (Fin r → E ⊗[K_R] (K_R ⊗[K_M] K_M⟮X ^ (q * (M' / e))⟯))) := by
  classical
  have : Algebra.IsIntegral R_M R_1 := Algebra.IsIntegral.of_finite R_M R_1
  have : FiniteDimensional K_M K_1 :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact Nat.pos_of_neZero M)
  -- `R_M → R_1` is injective
  have hM1 : Function.Injective (algebraMap R_M R_1) := by
    have h : Function.Injective (algebraMap R_M K_1) := by
      rw [IsScalarTower.algebraMap_eq R_M K_M K_1]
      exact (algebraMap K_M K_1).injective.comp (IsFractionRing.injective R_M K_M)
    rw [IsScalarTower.algebraMap_eq R_M R_1 K_1, RingHom.coe_comp] at h
    exact h.of_comp
  -- `R` is a Noetherian integrally closed local domain, flat over `R_M`
  let eR : Localization.AtPrime P ≃ₐ[R'] R := IsLocalization.algEquiv P.primeCompl _ R
  have := EtaleNbhd.isDomain_localization R_M P.primeCompl
  have := EtaleNbhd.isIntegrallyClosed_localization R_M P.primeCompl
  have : IsNoetherianRing (Localization.AtPrime P) :=
    EtaleNbhd.isNoetherianRing_localization (A := R_M) P.primeCompl
  have : IsDomain R := Function.Injective.isDomain eR.symm.toRingEquiv.toRingHom eR.symm.injective
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv eR.toRingEquiv
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ eR.toRingEquiv
  have : Module.Flat R' R := IsLocalization.flat R P.primeCompl
  have : Module.Flat R_M R := Module.Flat.trans R_M R' R
  -- the unique prime `P₁` of `R_1 ⊗ R'` over `P`
  have hκ := bijective_mapₐ_of_forall_sub_mem (exists_sub_mem_of_bijective hκ')
  obtain ⟨P₁, hP₁, h₁⟩ : ∃ P₁ : Ideal (R_1 ⊗[R_M] R'), P₁.IsPrime ∧
      P₁.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R_M] R_1 ⊗[R_M] R').toRingHom = P := by
    letI : Algebra R' (R_1 ⊗[R_M] R') :=
      (Algebra.TensorProduct.includeRight : R' →ₐ[R_M] R_1 ⊗[R_M] R').toRingHom.toAlgebra
    have : Algebra.IsIntegral R' (R_1 ⊗[R_M] R') := ⟨isIntegral_includeRight⟩
    have hinj : Function.Injective
        (Algebra.TensorProduct.includeRight : R' →ₐ[R_M] R_1 ⊗[R_M] R') :=
      Algebra.TensorProduct.includeRight_injective hM1
    obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P
      (⊥ : Ideal (R_1 ⊗[R_M] R')) (by
      rw [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot (algebraMap R' (R_1 ⊗[R_M] R'))).mp hinj]
      exact bot_le)
    exact ⟨Q, hQ, hQP⟩
  -- the local ring `T = R_1 ⊗ R'_P`, a localization of an étale `R_1`-algebra
  set S := P.primeCompl.map (Algebra.TensorProduct.includeRight : R' →ₐ[R_M] R_1 ⊗[R_M] R')
  let T := TensorLoc R_M R_1 P
  have : IsLocalRing T := isLocalRing_tensorLoc hκ P P₁ h₁
  have hTm : (maximalIdeal T).comap (algebraMap R_1 T) = maximalIdeal R_1 := by
    rw [IsScalarTower.algebraMap_eq R_1 (R_1 ⊗[R_M] R') T, ← Ideal.comap_comap,
      comap_eq_of_isMaximal hκ P P₁ h₁]
    exact comap_includeLeft_eq_maximalIdeal P P₁ h₁
  have : IsLocalHom (algebraMap R_1 T) := ((IsLocalRing.local_hom_TFAE _).out 0 4).mpr hTm
  have : IsDomain T := EtaleNbhd.isDomain_localization R_1 S
  have : IsIntegrallyClosed T := EtaleNbhd.isIntegrallyClosed_localization R_1 S
  have : IsNoetherianRing T := EtaleNbhd.isNoetherianRing_localization (A := R_1) S
  have hTinj : Function.Injective (algebraMap R_1 T) := EtaleNbhd.algebraMap_injective R_1 S
  have : Module.Flat R_1 T := Module.Flat.trans R_1 (R_1 ⊗[R_M] R') T
  have : Algebra.FormallyEtale (R_1 ⊗[R_M] R') T := Algebra.FormallyEtale.of_isLocalization S
  have : Algebra.FormallyUnramified R_1 T :=
    Algebra.FormallyUnramified.comp R_1 (R_1 ⊗[R_M] R') T
  have hmT := EtaleNbhd.maximalIdeal_eq_span_pair (T := T) hm₁
  have hxT := EtaleNbhd.prime_algebraMap (T := T) hx₁ hy₁ hm₁ hTinj
  have hyT := EtaleNbhd.algebraMap_notMem_span (T := T) hx₁ hy₁ hm₁
  -- `C = R ⊗_{R_M} R_1 ≅ T`
  let C := R ⊗[R_M] R_1
  let ι₁ : R_1 →ₐ[R_M] C := Algebra.TensorProduct.includeRight
  let e₁ : R_1 ⊗[R_M] R ≃ₐ[R_1] T :=
    IsLocalization.tensorProductEquivOfMapIncludeRight R_M R_1 P.primeCompl R T
  let φ : C ≃+* T := (Algebra.TensorProduct.comm R_M R R_1).toRingEquiv.trans e₁.toRingEquiv
  have hφ : ∀ r : R_1, φ (ι₁ r) = algebraMap R_1 T r := fun r ↦ by
    have h := e₁.commutes r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
    change e₁ (Algebra.TensorProduct.comm R_M R R_1 ((1 : R) ⊗ₜ r)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact h
  have hφs : ∀ r : R_1, φ.symm (algebraMap R_1 T r) = ι₁ r := fun r ↦ by
    rw [← hφ, RingEquiv.symm_apply_apply]
  have : Nontrivial C := φ.toEquiv.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' φ.symm.toRingHom φ.symm.surjective
  have : IsDomain C := Function.Injective.isDomain φ.toRingHom φ.injective
  have : IsIntegrallyClosed C := IsIntegrallyClosed.of_equiv φ.symm
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv T φ.symm
  obtain ⟨hxC, hyC, hmC⟩ := EtaleNbhd.regularPair_of_ringEquiv φ.symm hxT hyT hmT
  simp only [hφs] at hxC hyC hmC
  have hι₁inj : Function.Injective ι₁ := fun a b h ↦ hTinj (by rw [← hφ, ← hφ, h])
  have hRC : Function.Injective (algebraMap R C) := by
    intro a b h
    apply Algebra.TensorProduct.includeLeft_injective (S := R) (A := R) (B := R_1) hM1
    exact h
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hRC
  have : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have : IsLocalHom (algebraMap R C) := EtaleNbhd.isLocalHom_of_isIntegral
  -- the residue field extension of `R → C` is trivial
  have hι₁m : ∀ m ∈ maximalIdeal R_1, ι₁ m ∈ maximalIdeal C := by
    intro m hm
    rw [mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
    intro hu
    apply hm
    have h := hu.map φ.toRingHom
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hφ] at h
    exact (isUnit_map_iff (algebraMap R_1 T) m).mp h
  have hκC : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C)) := by
    refine bijective_residueField_map_of_forall_sub_mem fun c ↦ ?_
    induction c using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r r₁ =>
      obtain ⟨a, ha⟩ := exists_sub_mem_of_bijective hκ' r₁
      refine ⟨r * algebraMap R_M R a, ?_⟩
      have h1 : (r * algebraMap R_M R a) ⊗ₜ[R_M] (1 : R_1) = r ⊗ₜ algebraMap R_M R_1 a := by
        rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
          ← Algebra.algebraMap_eq_smul_one]
      have h2 : r ⊗ₜ[R_M] r₁ - algebraMap R C (r * algebraMap R_M R a) =
          (r ⊗ₜ[R_M] (1 : R_1)) * ι₁ (r₁ - algebraMap R_M R_1 a) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, h1]
        change _ = (r ⊗ₜ[R_M] (1 : R_1)) * ((1 : R) ⊗ₜ[R_M] (r₁ - algebraMap R_M R_1 a))
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub]
      rw [h2]
      exact Ideal.mul_mem_left _ _ (hι₁m _ ha)
    | add c d hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨b, hb⟩ := hd
      exact ⟨a + b, by rw [map_add, add_sub_add_comm]; exact add_mem ha hb⟩
  -- the fraction field `K_C` of `C` and the maps `K_R → K_C ← K_1`
  let K_C := FractionRing C
  have hRK : Function.Injective (algebraMap R K_C) := by
    rw [IsScalarTower.algebraMap_eq R C K_C]
    exact (IsFractionRing.injective C K_C).comp hRC
  letI : Algebra K_R K_C := (IsFractionRing.lift hRK).toAlgebra
  have : IsScalarTower R K_R K_C := IsScalarTower.of_algebraMap_eq fun r ↦
    (IsFractionRing.lift_algebraMap hRK r).symm
  have h1K : Function.Injective ((algebraMap C K_C).comp ι₁.toRingHom) :=
    (IsFractionRing.injective C K_C).comp hι₁inj
  let j₁ : K_1 →+* K_C := IsFractionRing.lift h1K
  have hj₁ : ∀ r, j₁ (algebraMap R_1 K_1 r) = algebraMap C K_C (ι₁ r) := fun r ↦
    IsFractionRing.lift_algebraMap h1K r
  letI : Algebra K_M K_C := ((algebraMap K_R K_C).comp (algebraMap K_M K_R)).toAlgebra
  have : IsScalarTower K_M K_R K_C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hcomp : ∀ k : K_M, j₁ (algebraMap K_M K_1 k) = algebraMap K_M K_C k := by
    have : j₁.comp (algebraMap K_M K_1) = algebraMap K_M K_C := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R_M) (RingHom.ext fun a ↦ ?_)
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply R_M K_M K_1, IsScalarTower.algebraMap_apply R_M R_1 K_1,
        hj₁]
      change _ = algebraMap K_R K_C (algebraMap K_M K_R (algebraMap R_M K_M a))
      rw [← IsScalarTower.algebraMap_apply R_M K_M K_R, IsScalarTower.algebraMap_apply R_M R K_R,
        ← IsScalarTower.algebraMap_apply R K_R K_C, IsScalarTower.algebraMap_apply R C K_C,
        ← IsScalarTower.algebraMap_apply R_M R C]
      congr 1
      exact ι₁.commutes a
    exact fun k ↦ RingHom.congr_fun this k
  let j₁' : K_1 →ₐ[K_M] K_C := { j₁ with commutes' := hcomp }
  let ψ : K_R ⊗[K_M] K_1 →ₐ[K_R] K_C :=
    Algebra.TensorProduct.lift (Algebra.ofId K_R K_C) j₁' fun _ _ ↦ Commute.all _ _
  have hψ : ∀ k k₁, ψ (k ⊗ₜ k₁) = algebraMap K_R K_C k * j₁ k₁ := fun _ _ ↦ rfl
  -- `K_R ⊗_{K_M} K_1 ≅ K_C`
  have hE₀ := isField_tensor_localization (R := R_M) K_M P
  let g : Localization.AtPrime P →ₐ[R_M] K_R :=
    (IsScalarTower.toAlgHom R_M R K_R).comp (eR.toAlgHom.restrictScalars R_M)
  let fE : K_M ⊗[R_M] Localization.AtPrime P →ₐ[K_M] K_R :=
    Algebra.TensorProduct.lift (Algebra.ofId K_M K_R) g fun _ _ ↦ Commute.all _ _
  have hfE : Function.Bijective fE := by
    letI := hE₀.toField
    refine ⟨fE.toRingHom.injective, EtaleNbhd.surjective_of_forall_exists (A := R)
      fE.toRingHom fun a ↦ ⟨1 ⊗ₜ eR.symm a, ?_⟩⟩
    change fE (1 ⊗ₜ eR.symm a) = _
    simp [fE, g]
  let eE := AlgEquiv.ofBijective fE hfE
  have hF : IsField (K_R ⊗[K_M] K_1) :=
    MulEquiv.isField (isField_tensor_tensor K_M K_1 P hκ P₁ h₁)
      (Algebra.TensorProduct.congr eE (AlgEquiv.refl : K_1 ≃ₐ[K_M] K_1)).symm.toMulEquiv
  have hψinj : Function.Injective ψ := by
    letI := hF.toField
    exact ψ.toRingHom.injective
  have hψsurj : Function.Surjective ψ := by
    letI := hF.toField
    refine EtaleNbhd.surjective_of_forall_exists (A := C) ψ.toRingHom fun c ↦ ?_
    induction c using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r r₁ =>
      refine ⟨algebraMap R K_R r ⊗ₜ algebraMap R_1 K_1 r₁, ?_⟩
      change ψ _ = _
      rw [hψ, hj₁, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R C K_C,
        ← map_mul]
      congr 1
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      change (r ⊗ₜ[R_M] (1 : R_1)) * ((1 : R) ⊗ₜ[R_M] r₁) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add c d hc hd =>
      obtain ⟨u, hu⟩ := hc
      obtain ⟨v, hv⟩ := hd
      exact ⟨u + v, by rw [map_add, hu, hv, map_add]⟩
  have hfin' : finrank K_R K_C = M := by
    rw [← (AlgEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).toLinearEquiv.finrank_eq,
      Module.finrank_baseChange, hfin]
  have : FiniteDimensional K_R K_C :=
    Module.finite_of_finrank_pos (by rw [hfin']; exact Nat.pos_of_neZero M)
  -- the generator `X_C`
  set X_C := j₁ X
  have hxC' : X_C ^ M = algebraMap K_R K_C (algebraMap K_M K_R x) := by
    rw [← map_pow, hx, hcomp]
    rfl
  have hj : ∀ n : ℕ, ∀ z ∈ Algebra.adjoin K_M {X ^ n},
      j₁ z ∈ Algebra.adjoin K_R {X_C ^ n} := by
    intro n z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff.mp hz, map_pow]; exact Algebra.subset_adjoin rfl
    | algebraMap k =>
      rw [hcomp]
      exact Subalgebra.algebraMap_mem _ (algebraMap K_M K_R k)
    | add a b _ _ ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
  have hadj : ∀ n : ℕ, (K_M⟮X ^ n⟯).toSubalgebra = Algebra.adjoin K_M {X ^ n} := fun n ↦
    adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.of_finite K_M _).isAlgebraic
  have hX' : K_R⟮X_C⟯ = ⊤ := by
    rw [_root_.eq_top_iff]
    rintro z -
    obtain ⟨t, rfl⟩ := hψsurj z
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul k k₁ =>
      rw [hψ]
      refine mul_mem (IntermediateField.algebraMap_mem _ k) (algebra_adjoin_le_adjoin K_R _ ?_)
      have hk₁ : k₁ ∈ Algebra.adjoin K_M {X ^ 1} := by
        rw [← hadj, pow_one, hX]
        exact Algebra.mem_top
      simpa using hj 1 k₁ hk₁
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  -- `K_R ⊗_{K_M} K_M(X ^ n) ≅ K_R(X_C ^ n)`
  have hconv : ∀ n : ℕ, Nonempty (K_R ⊗[K_M] K_M⟮X ^ n⟯ ≃ₐ[K_R] K_R⟮X_C ^ n⟯) := by
    intro n
    let incl : K_M⟮X ^ n⟯ →ₐ[K_M] K_1 := (K_M⟮X ^ n⟯).val
    let χ : K_R ⊗[K_M] K_M⟮X ^ n⟯ →ₐ[K_R] K_C :=
      ψ.comp (Algebra.TensorProduct.map (AlgHom.id K_R K_R) incl)
    have hmap : Function.Injective (Algebra.TensorProduct.map (AlgHom.id K_R K_R) incl) := by
      convert Module.Flat.lTensor_preserves_injective_linearMap (M := K_R) incl.toLinearMap
        Subtype.val_injective using 1
      refine funext fun t ↦ ?_
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add a b ha hb => simp only [map_add, ha, hb]
    have hχ : Function.Injective χ := hψinj.comp hmap
    have hrange : χ.range = (K_R⟮X_C ^ n⟯).toSubalgebra := by
      rw [adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.of_finite K_R _).isAlgebraic]
      apply le_antisymm
      · rintro _ ⟨t, rfl⟩
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul k z =>
          change ψ (k ⊗ₜ (z : K_1)) ∈ _
          rw [hψ]
          refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k) (hj n z ?_)
          rw [← hadj]
          exact z.2
        | add a b ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
      · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        refine ⟨1 ⊗ₜ ⟨X ^ n, mem_adjoin_simple_self K_M _⟩, ?_⟩
        change ψ (1 ⊗ₜ (X ^ n)) = _
        rw [hψ, map_one, one_mul, map_pow]
    exact ⟨(AlgEquiv.ofInjective χ hχ).trans (Subalgebra.equivOfEq _ _ hrange)⟩
  -- apply the generic "S4-local"
  obtain ⟨R'', i₁, i₂, i₃, P'', i₄, i₅, E, i₆, i₇, hE, e, he, r, ⟨Φ⟩⟩ :=
    exists_etale_tensor_algEquiv_pi_of_etale (R_M := R) (R_1 := C) hqM hq hM' hκC K_R K_C
      hxC' hX' hfin' hζ L hL fun L₁ _ _ _ _ _ _ _ _ _ _ hgen ↦
        EtaleNbhd.etale_integralClosure_of_baseChange hxC hyC hmC K_R K_C L B hunr L₁ hgen
  obtain ⟨Ψ⟩ := hconv (q * (M' / e))
  exact ⟨R'', i₁, i₂, i₃, P'', i₄, i₅, E, i₆, i₇, hE, e, he, r, ⟨Φ.trans
    (AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.congr AlgEquiv.refl Ψ.symm)⟩⟩

end EtaleNbhd

end SemistableReduction.NodeCover
