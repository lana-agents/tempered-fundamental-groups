/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleLocalDomain

/-!
# Étale neighbourhoods and finite local extensions with trivial residue extension

Let `R → C` be a finite local homomorphism of local rings inducing an isomorphism of residue
fields (in the application: the Kummer map from the node of thickness `M` to the regular node,
localized at the closed points), and let `(R', P)` be an étale neighbourhood of the closed point
of `R` (`R'` étale over `R`, `P` a prime over the maximal ideal). We show:

* `eq_of_liesOver_tensor`: there is at most one prime of `C ⊗_R R'` over `P`.
* `isLocalRing_localization_tensor`: the localization `G` of `C ⊗_R R'` at (the image of) the
  complement of `P` (i.e. `C ⊗_R R'_P`) is a local ring, whose maximal ideal contracts to any
  given prime over `P`.
* `isField_tensor_of_isLocalization`: a local ring `T` which is a localization of an étale
  algebra over an integrally closed domain `A` has a field as generic fibre `T ⊗_A Frac A`
  (generalising `isField_tensor_fractionRing` from `Localization.AtPrime` to any localization).

These are the inputs of the étale-local form of "S4-local" (MR12 plan): over such an étale
neighbourhood the function fields `E = Frac R'_P` and `E ⊗_{Frac R} Frac C` are fields.
-/

open Algebra TensorProduct IsLocalRing

namespace SemistableReduction

section Field

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
  [Algebra A B] [Algebra.Etale A B] (M : Submonoid B) (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]

local notation "T" => Localization M

omit [IsDomain A] in
/-- Elements of `T ⊗_A K` integral over a localization `T` of an étale `A`-algebra come from
`T`. -/
theorem exists_eq_tmul_one_of_isIntegral' {e : T ⊗[A] K} (he : IsIntegral T e) :
    ∃ d : T, d ⊗ₜ[A] (1 : K) = e := by
  have H : Function.Bijective (TensorProduct.toIntegralClosure A B K) :=
    TensorProduct.toIntegralClosure_bijective_of_smooth
  have H' : Function.Bijective (TensorProduct.toIntegralClosure B T (B ⊗[A] K)) :=
    TensorProduct.toIntegralClosure_bijective_of_isLocalization M
  have Hb := TensorProduct.toIntegralClosure_bijective_of_tower (B := K) H H'
  obtain ⟨t, ht⟩ := Hb.2 ⟨e, he⟩
  have ht' : (Algebra.TensorProduct.map (AlgHom.id T T) (integralClosure A K).val) t = e :=
    congrArg Subtype.val ht
  rw [← ht']
  clear ht ht' Hb H H'
  induction t with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add]⟩
  | tmul d k =>
    have hk : (k : K) ∈ (⊥ : Subalgebra A K) := by
      rw [← IsIntegrallyClosed.integralClosure_eq_bot A K]
      exact k.2
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hk
    refine ⟨r • d, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

omit [IsDomain A] in
variable (A) in
include A in
/-- **The generic fibre of a local localization of an étale algebra over a normal domain is a
field**: if `T = B_M` is local, `T ⊗_A K` is a field. -/
theorem isField_tensor_of_isLocalization [IsLocalRing T] : IsField (T ⊗[A] K) := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] K) :=
    Algebra.TensorProduct.includeLeft_injective (S := A) (IsFractionRing.injective A K)
  have hidem : ∀ e : T ⊗[A] K, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    have hint : IsIntegral T e := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub (by simp)
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, sq, Polynomial.eval₂_mul]
        rw [he.eq, sub_self]
    obtain ⟨d, rfl⟩ := exists_eq_tmul_one_of_isIntegral' M K hint
    have hd : IsIdempotentElem d := by
      apply hinj
      change (d * d) ⊗ₜ[A] (1 : K) = d ⊗ₜ[A] (1 : K)
      rw [← he.eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rcases eq_zero_or_one_of_isIdempotentElem hd with h | h
    · left; rw [h, TensorProduct.zero_tmul]
    · right; rw [h]; rfl
  let φ : T ⊗[A] K ≃ₐ[A] K ⊗[A] T := Algebra.TensorProduct.comm A T K
  have hidem' : ∀ e : K ⊗[A] T, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    rcases hidem (φ.symm e) (he.map φ.symm) with h | h
    · left; simpa using congrArg φ h
    · right; simpa using congrArg φ h
  haveI : IsReduced (K ⊗[A] T) := Algebra.FormallyUnramified.isReduced_of_field K _
  haveI : Module.Finite K (K ⊗[A] T) := by
    haveI : Module.Free K (K ⊗[A] T) := Module.Free.of_divisionRing K _
    exact Algebra.FormallyUnramified.finite_of_free K _
  haveI : IsArtinianRing (K ⊗[A] T) := IsArtinianRing.of_finite K _
  haveI : Nontrivial (K ⊗[A] T) := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have := congrArg φ.symm h
    rw [map_zero, map_one] at this
    exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact this))
  exact MulEquiv.isField (isField_of_isArtinianRing_of_isReduced hidem') φ.toRingEquiv.toMulEquiv

end Field

section Primes

variable {R C R' : Type*} [CommRing R] [CommRing C] [CommRing R'] [Algebra R C] [Algebra R R']
  [IsLocalRing R] [IsLocalRing C] [Algebra.IsIntegral R C]
  [(maximalIdeal C).LiesOver (maximalIdeal R)]

omit [IsLocalRing R] [IsLocalRing C] [(maximalIdeal C).LiesOver (maximalIdeal R)] in
/-- `C ⊗_R R'` is integral over `R'` (via `includeRight`). -/
theorem isIntegral_includeRight :
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom.IsIntegral := by
  letI : Algebra R' (C ⊗[R] R') :=
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom.toAlgebra
  intro x
  let e := Algebra.TensorProduct.comm R C R'
  have h : IsIntegral R' (e x) := Algebra.IsIntegral.isIntegral _
  have h2 : IsIntegral R' (e.symm (e x)) :=
    h.map_of_comp_eq (RingHom.id R') e.symm.toRingHom (by
      ext r
      simp [e, RingHom.algebraMap_toAlgebra])
  rw [AlgEquiv.symm_apply_apply] at h2
  exact h2

omit [(maximalIdeal C).LiesOver (maximalIdeal R)] in
/-- A prime of `C ⊗_R R'` lying over a prime `P` of `R'` over the maximal ideal of `R` lies over
the maximal ideal of `C`. -/
theorem comap_includeLeft_eq_maximalIdeal (P : Ideal R') [P.LiesOver (maximalIdeal R)]
    (P₁ : Ideal (C ⊗[R] R')) [P₁.IsPrime]
    (h₁ : P₁.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P) :
    P₁.comap (algebraMap C (C ⊗[R] R')) = maximalIdeal C := by
  have hR : (P₁.comap (algebraMap C (C ⊗[R] R'))).comap (algebraMap R C) = maximalIdeal R := by
    rw [Ideal.comap_comap]
    have : (algebraMap C (C ⊗[R] R')).comp (algebraMap R C) =
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom.comp
          (algebraMap R R') := by
      ext r
      simp [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rw [this, ← Ideal.comap_comap, h₁]
    exact (Ideal.over_def P (maximalIdeal R)).symm
  have : (P₁.comap (algebraMap C (C ⊗[R] R'))).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hR]; infer_instance)
  exact IsLocalRing.eq_maximalIdeal this

variable (R C) in
/-- The localization `C ⊗_R R'_P` of `C ⊗_R R'` at the complement of `P`. -/
abbrev TensorLoc (P : Ideal R') [P.IsPrime] : Type _ :=
  Localization (P.primeCompl.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R'))

variable (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) (maximalIdeal C)
  (Algebra.ofId R C) ((maximalIdeal C).over_def (maximalIdeal R))))
include hκ

/-- **At most one prime over `P`.** If `κ(R) → κ(C)` is bijective, a prime `P` of `R'` over the
maximal ideal of `R` has at most one prime of `C ⊗_R R'` over it. -/
theorem eq_of_comap_includeRight_eq (P : Ideal R') [P.IsPrime] [P.LiesOver (maximalIdeal R)]
    (P₁ P₂ : Ideal (C ⊗[R] R')) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : P₁.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P)
    (h₂ : P₂.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P) :
    P₁ = P₂ := by
  have : P₁.LiesOver (maximalIdeal C) := ⟨(comap_includeLeft_eq_maximalIdeal P P₁ h₁).symm⟩
  have : P₂.LiesOver (maximalIdeal C) := ⟨(comap_includeLeft_eq_maximalIdeal P P₂ h₂).symm⟩
  exact Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hκ P₁ P₂ (h₁.trans h₂.symm)

omit [IsLocalRing R] [IsLocalRing C] [(maximalIdeal C).LiesOver (maximalIdeal R)] hκ in
/-- A prime of `C ⊗_R R'` which avoids the image of `R' ∖ P` lies over a prime contained in
`P`; by going up it is contained in a prime over `P`, which still avoids `R' ∖ P`. -/
theorem exists_le_comap_eq (P : Ideal R') [P.IsPrime] (Q : Ideal (C ⊗[R] R')) [Q.IsPrime]
    (hQ : Disjoint (P.primeCompl.map (Algebra.TensorProduct.includeRight :
      R' →ₐ[R] C ⊗[R] R') : Set (C ⊗[R] R')) Q) :
    ∃ Q' ≥ Q, Q'.IsPrime ∧
      Q'.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P := by
  letI : Algebra R' (C ⊗[R] R') :=
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom.toAlgebra
  have : Algebra.IsIntegral R' (C ⊗[R] R') := ⟨isIntegral_includeRight⟩
  have hle : Q.comap (algebraMap R' (C ⊗[R] R')) ≤ P := by
    intro r hr
    by_contra hrP
    exact Set.disjoint_left.mp hQ ⟨r, hrP, rfl⟩ hr
  exact Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P Q hle

/-- **`C ⊗_R R'_P` is local**: every maximal ideal contracts to the unique prime `P₁` of
`C ⊗_R R'` over `P`. -/
theorem comap_eq_of_isMaximal (P : Ideal R') [P.IsPrime] [P.LiesOver (maximalIdeal R)]
    (P₁ : Ideal (C ⊗[R] R')) [P₁.IsPrime]
    (h₁ : P₁.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P)
    (𝔐 : Ideal (TensorLoc R C P)) [𝔐.IsMaximal] :
    𝔐.comap (algebraMap (C ⊗[R] R') (TensorLoc R C P)) = P₁ := by
  set S := P.primeCompl.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R')
  set Q := 𝔐.comap (algebraMap (C ⊗[R] R') (TensorLoc R C P))
  have hQ : Disjoint (S : Set (C ⊗[R] R')) Q :=
    (IsLocalization.isPrime_iff_isPrime_disjoint S (TensorLoc R C P) 𝔐).mp inferInstance |>.2
  obtain ⟨Q', hQQ', hQ', hQ'P⟩ := exists_le_comap_eq P Q hQ
  have hQ'S : Disjoint (S : Set (C ⊗[R] R')) Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hr'
    exact hr (by rw [← hQ'P]; exact hr')
  have hmap : (Q'.map (algebraMap (C ⊗[R] R') (TensorLoc R C P))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S _ Q' hQ' hQ'S
  have h𝔐 : 𝔐 = Q.map (algebraMap (C ⊗[R] R') (TensorLoc R C P)) :=
    (IsLocalization.map_under S (TensorLoc R C P) 𝔐).symm
  have hle : 𝔐 ≤ Q'.map (algebraMap (C ⊗[R] R') (TensorLoc R C P)) := by
    rw [h𝔐]; exact Ideal.map_mono hQQ'
  have heq : 𝔐 = Q'.map (algebraMap (C ⊗[R] R') (TensorLoc R C P)) :=
    (‹𝔐.IsMaximal›.eq_of_le hmap.ne_top hle)
  have hQQ : Q = Q' := by
    change 𝔐.comap _ = Q'
    rw [heq]
    exact IsLocalization.under_map_of_isPrime_disjoint S _ hQ' hQ'S
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  exact eq_of_comap_includeRight_eq hκ P Q P₁ (by rw [hQQ, hQ'P]) h₁

/-- **`C ⊗_R R'_P` is local.** -/
theorem isLocalRing_tensorLoc (P : Ideal R') [P.IsPrime] [P.LiesOver (maximalIdeal R)]
    (P₁ : Ideal (C ⊗[R] R')) [P₁.IsPrime]
    (h₁ : P₁.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P) :
    IsLocalRing (TensorLoc R C P) := by
  set S := P.primeCompl.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R')
  have hP₁S : Disjoint (S : Set (C ⊗[R] R')) P₁ := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hr'
    exact hr (by rw [← h₁]; exact hr')
  have hprime : (P₁.map (algebraMap (C ⊗[R] R') (TensorLoc R C P))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S _ P₁ inferInstance hP₁S
  have : Nontrivial (TensorLoc R C P) := ⟨⟨0, 1, fun h ↦ hprime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ Ideal.zero_mem _))⟩⟩
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨𝔐, h𝔐⟩ := Ideal.exists_maximal (TensorLoc R C P)
  refine ⟨𝔐, h𝔐, fun 𝔐' h𝔐' ↦ ?_⟩
  have h1 := comap_eq_of_isMaximal hκ P P₁ h₁ 𝔐'
  have h2 := comap_eq_of_isMaximal hκ P P₁ h₁ 𝔐
  rw [← IsLocalization.map_under S (TensorLoc R C P) 𝔐', ← IsLocalization.map_under S _ 𝔐]
  exact congrArg (Ideal.map (algebraMap (C ⊗[R] R') (TensorLoc R C P))) (h1.trans h2.symm)

end Primes

section Fields

variable {R C R' : Type*} [CommRing R] [CommRing C] [CommRing R'] [Algebra R C] [Algebra R R']
  [IsLocalRing R] [IsLocalRing C] [Algebra.IsIntegral R C]
  [(maximalIdeal C).LiesOver (maximalIdeal R)]
  [IsDomain R] [IsIntegrallyClosed R] [IsDomain C] [IsIntegrallyClosed C] [Algebra.Etale R R']
  (K_R K_C : Type*) [Field K_R] [Field K_C] [Algebra R K_R] [IsFractionRing R K_R]
  [Algebra C K_C] [IsFractionRing C K_C] [Algebra K_R K_C] [Algebra R K_C]
  [IsScalarTower R K_R K_C] [IsScalarTower R C K_C]
  (P : Ideal R') [P.IsPrime] [P.LiesOver (maximalIdeal R)]

omit [IsLocalRing R] [P.LiesOver (maximalIdeal R)] [IsLocalRing C] [Algebra.IsIntegral R C]
  [(maximalIdeal C).LiesOver (maximalIdeal R)] [IsDomain C] [IsIntegrallyClosed C] [IsDomain R] in
/-- **The function field of the étale neighbourhood**: `E = K_R ⊗_R R'_P` is a field. -/
theorem isField_tensor_localization : IsField (K_R ⊗[R] Localization.AtPrime P) :=
  MulEquiv.isField (isField_tensor_of_isLocalization R P.primeCompl K_R)
    (Algebra.TensorProduct.comm R K_R (Localization.AtPrime P)).toRingEquiv.toMulEquiv

variable (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) (maximalIdeal C)
  (Algebra.ofId R C) ((maximalIdeal C).over_def (maximalIdeal R))))
include hκ

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain C] [IsFractionRing R K_R] in
/-- **The compositum `E K_C` is a field**: `(K_R ⊗_R R'_P) ⊗_{K_R} K_C` is a field, given a
prime of `C ⊗_R R'` over `P`. It is isomorphic to `K_C ⊗_C (C ⊗_R R'_P)`, the generic fibre over
`C` of the local ring `C ⊗_R R'_P` (`isLocalRing_tensorLoc`), which is a localization of the
étale `C`-algebra `C ⊗_R R'`. -/
theorem isField_tensor_tensor (P₁ : Ideal (C ⊗[R] R')) [P₁.IsPrime]
    (h₁ : P₁.comap (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R').toRingHom = P) :
    IsField ((K_R ⊗[R] Localization.AtPrime P) ⊗[K_R] K_C) := by
  have := isLocalRing_tensorLoc hκ P P₁ h₁
  have hG := isField_tensor_of_isLocalization C
    (P.primeCompl.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] C ⊗[R] R')) K_C
  let e : C ⊗[R] Localization.AtPrime P ≃ₐ[C] TensorLoc R C P :=
    IsLocalization.tensorProductEquivOfMapIncludeRight R C P.primeCompl _ _
  let φ : (K_R ⊗[R] Localization.AtPrime P) ⊗[K_R] K_C ≃+* TensorLoc R C P ⊗[C] K_C :=
    (Algebra.TensorProduct.comm K_R _ K_C).toRingEquiv.trans <|
    (Algebra.TensorProduct.cancelBaseChange R K_R K_C K_C
      (Localization.AtPrime P)).toRingEquiv.trans <|
    (Algebra.TensorProduct.cancelBaseChange R C K_C K_C
      (Localization.AtPrime P)).symm.toRingEquiv.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K_C ≃ₐ[C] K_C) e).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm C K_C _).toRingEquiv
  exact MulEquiv.isField hG φ.toMulEquiv

end Fields

end SemistableReduction
