/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Etale.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import TemperedFundamentalGroups.SemistableReduction.TameGalois

/-!
# The normalisation of a Dedekind domain in a finite étale cover of a principal open

MR13 step 7 (S7, generic part). Let `A` be a Dedekind domain, `x : A`, `A_x = A[1/x]` (any
`IsLocalization.Away x A_x`), and `C'` a domain which is a finite étale `A_x`-algebra. The
normalisation `C0 = integralClosure A C'` of `A` in `C'` satisfies:

* **`finite`**, **`isDedekindDomain`**, **`isDomain`**: `C0` is a finite `A`-algebra and a
  Dedekind domain (`IsIntegralClosure.finite`; the fraction field extension is separable since
  `C'` is unramified over `A_x`: `Algebra.FormallyUnramified.localization_map`,
  `Algebra.FormallyUnramified.isSeparable`; `C'` is Dedekind by
  `isDedekindDomain.of_formallyUnramified`, so `C0` is the integral closure of `A` in `Frac C'`);
* **`isLocalization`**: `C0[1/x] = C'` (`IsLocalization.Away`);
* **`flat`**: `C0` is flat over `A` (torsion-free over a Dedekind domain);
* **`isDiscreteValuationRing`**: localizations of `C0` at primes containing `x` are DVRs;
* **`isGaloisGroup`**: a faithful `A`-linear action of a finite group `G` on `C'` with
  `|G| = rank_{A_x} C'` restricts to `C0` (instance on `integralClosure`) and makes `G` a Galois
  group of `C0 / A` (Artin on the fraction fields, then `IsGaloisGroup.of_isFractionRing`);
  **`ramificationIdx_dvd_card`**: hence `e(P | p) ∣ |G|` (`Ideal.ramificationIdx_dvd_card`);
* **`restrict`**, **`restrictEquiv`**, **`exists_restrict`**: functoriality of the
  normalisation, compatible with `C0 → C'`.
-/

open nonZeroDivisors

set_option linter.unusedSectionVars false

namespace SemistableReduction.NormalizationChart

section Setup

variable (A : Type*) [CommRing A] [IsDedekindDomain A] (x : A)
  (Ax : Type*) [CommRing Ax] [Algebra A Ax] [IsLocalization.Away x Ax]
  (C' : Type*) [CommRing C'] [IsDomain C'] [Algebra Ax C'] [Algebra A C'] [IsScalarTower A Ax C']
  [Algebra.Etale Ax C'] [Module.Finite Ax C']

/-- **The normalisation** `C0` of `A` in `C'`: the integral closure of `A` in `C'`. -/
abbrev C0 : Type _ := integralClosure A C'

include A x Ax C'

/-- `x ≠ 0`, since `C'` is a nonzero `A[1/x]`-algebra. -/
theorem ne_zero : x ≠ 0 := by
  rintro rfl
  have h : IsUnit (algebraMap A C' 0) := by
    rw [IsScalarTower.algebraMap_apply A Ax C']
    exact (IsLocalization.Away.algebraMap_isUnit (0 : A)).map _
  simp at h

/-- `A[1/x]` is a domain. -/
theorem isDomain_Ax : IsDomain Ax :=
  IsLocalization.isDomain_of_le_nonZeroDivisors Ax (M := Submonoid.powers x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ne_zero A x Ax C'))

/-- `A[1/x]` is a Dedekind domain. -/
theorem isDedekindDomain_Ax : IsDedekindDomain Ax :=
  haveI := isDomain_Ax A x Ax C'
  IsLocalization.isDedekindDomain A
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ne_zero A x Ax C')) Ax

/-- `A[1/x] → C'` is injective (`C'` is flat over the domain `A[1/x]`). -/
theorem injective_algebraMap_Ax : Function.Injective (algebraMap Ax C') := by
  haveI := isDomain_Ax A x Ax C'
  exact Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance

/-- `C'` is a Dedekind domain (finite unramified over the Dedekind domain `A[1/x]`). -/
theorem isDedekindDomain_C' : IsDedekindDomain C' :=
  haveI := isDedekindDomain_Ax A x Ax C'
  isDedekindDomain.of_formallyUnramified Ax C'

/-- `A → C'` is injective. -/
theorem injective_algebraMap_A : Function.Injective (algebraMap A C') := by
  rw [IsScalarTower.algebraMap_eq A Ax C']
  exact (injective_algebraMap_Ax A x Ax C').comp
    (IsLocalization.injective Ax
      (powers_le_nonZeroDivisors_of_noZeroDivisors (ne_zero A x Ax C')))

/-- `C0` is torsion-free over `A`. -/
theorem faithfulSMul_C0 : FaithfulSMul A (C0 A C') := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b h
  exact injective_algebraMap_A A x Ax C' (congrArg Subtype.val h)

/-- **`C0` is flat over `A`** (torsion-free over a Dedekind domain). -/
theorem flat : Module.Flat A (C0 A C') := by
  haveI := faithfulSMul_C0 A x Ax C'
  haveI : Module.IsTorsionFree A (C0 A C') :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  infer_instance

/-- **`C0[1/x] = C'`**: `C'` is the localization of `C0` away from `x`. -/
theorem isLocalization : IsLocalization.Away (algebraMap A (C0 A C') x) C' := by
  have hx := ne_zero A x Ax C'
  have hunit : ∀ n : ℕ, IsUnit (algebraMap A C' (x ^ n)) := fun n => by
    rw [IsScalarTower.algebraMap_apply A Ax C', map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := Ax) x).pow n).map
      (algebraMap Ax C')
  refine (isLocalization_iff (M := Submonoid.powers (algebraMap A (C0 A C') x)) (S := C')).mpr
    ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simpa [← map_pow] using hunit n
  · intro z
    have hz : IsIntegral Ax z := Algebra.IsIntegral.isIntegral z
    obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers x) z hz
    refine ⟨⟨⟨_, hm⟩, ⟨_, n, rfl⟩⟩, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, map_pow]
    rw [mul_comm]
    rfl
  · intro a b h
    exact ⟨1, by rw [Subtype.ext (h : (a : C') = b)]⟩

end Setup

section Action

variable {G R S : Type*} [Group G] [CommRing R] [CommRing S] [Algebra R S]
  [MulSemiringAction G S] [SMulCommClass G R S]

/-- The action of `G` on `S` restricts to the integral closure of `R` in `S`. -/
instance : MulSemiringAction G (integralClosure R S) where
  smul g c := ⟨g • (c : S), c.2.map (MulSemiringAction.toAlgHom R S g)⟩
  one_smul c := Subtype.ext (one_smul G (c : S))
  mul_smul g h c := Subtype.ext (mul_smul g h (c : S))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g c d := Subtype.ext (smul_add g (c : S) d)
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g c d := Subtype.ext (smul_mul' g (c : S) d)

/-- The restricted action is computed in `S`. -/
@[simp]
theorem coe_smul (g : G) (c : integralClosure R S) :
    ((g • c : integralClosure R S) : S) = g • c :=
  rfl

instance : SMulCommClass G R (integralClosure R S) :=
  ⟨fun g r c => Subtype.ext (smul_comm g r (c : S))⟩

end Action

section Frac

variable (A : Type*) [CommRing A] [IsDedekindDomain A] (x : A)
  (Ax : Type*) [CommRing Ax] [Algebra A Ax] [IsLocalization.Away x Ax]
  (C' : Type*) [CommRing C'] [IsDomain C'] [Algebra Ax C'] [Algebra A C'] [IsScalarTower A Ax C']
  [Algebra.Etale Ax C'] [Module.Finite Ax C']
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra Ax K]
  [IsScalarTower A Ax K] [Algebra C' L] [IsFractionRing C' L] [Algebra K L] [Algebra Ax L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower Ax K L] [IsScalarTower Ax C' L]
  [IsScalarTower A C' L]

include A x Ax C' K L

theorem isFractionRing_Ax : IsFractionRing Ax K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers x) Ax K

theorem isLocalization_frac : IsLocalization (Algebra.algebraMapSubmonoid C' Ax⁰) L := by
  haveI := isDomain_Ax A x Ax C'
  haveI := isDedekindDomain_C' A x Ax C'
  haveI := isFractionRing_Ax A x Ax C' K L
  haveI : Algebra.IsAlgebraic K L := isAlgebraic_of_isFractionRing Ax C' K L
  exact IsIntegralClosure.isLocalization Ax K L C'

theorem finiteDimensional_frac : FiniteDimensional K L := by
  haveI := isFractionRing_Ax A x Ax C' K L
  haveI := isLocalization_frac A x Ax C' K L
  exact Module.Finite.of_isLocalization Ax C' Ax⁰

theorem isSeparable_frac : Algebra.IsSeparable K L := by
  haveI := isFractionRing_Ax A x Ax C' K L
  haveI := isLocalization_frac A x Ax C' K L
  haveI := finiteDimensional_frac A x Ax C' K L
  haveI : Algebra.FormallyUnramified K L :=
    haveI : IsLocalization (Submonoid.map (algebraMap Ax C') Ax⁰) L :=
      isLocalization_frac A x Ax C' K L
    Algebra.FormallyUnramified.localization_map (Rₘ := K) (Sₘ := L) (S := C') Ax⁰
  exact Algebra.FormallyUnramified.isSeparable K L

theorem isIntegralClosure_frac : IsIntegralClosure (C0 A C') A L where
  algebraMap_injective := (IsFractionRing.injective C' L).comp Subtype.val_injective
  isIntegral_iff := by
    intro l
    constructor
    · intro hl
      haveI := isDedekindDomain_C' A x Ax C'
      obtain ⟨c, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hl.tower_top (A := C'))
      exact ⟨⟨c, (isIntegral_algebraMap_iff (IsFractionRing.injective C' L)).mp hl⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact IsIntegral.algebraMap (B := L) (x := (c : C')) (show IsIntegral A (c : C') from c.2)

theorem finite_frac : Module.Finite A (C0 A C') := by
  haveI := isIntegralClosure_frac A x Ax C' K L
  haveI := finiteDimensional_frac A x Ax C' K L
  haveI := isSeparable_frac A x Ax C' K L
  exact IsIntegralClosure.finite A K L (C0 A C')

theorem isDedekindDomain_frac : IsDedekindDomain (C0 A C') := by
  haveI := isIntegralClosure_frac A x Ax C' K L
  haveI := finiteDimensional_frac A x Ax C' K L
  haveI := isSeparable_frac A x Ax C' K L
  exact IsIntegralClosure.isDedekindDomain A K L (C0 A C')

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G C'] [SMulCommClass G A C']
  [FaithfulSMul G C'] [MulSemiringAction G L] [SMulDistribClass G C' L]

theorem isGaloisGroup_frac (hG : Module.finrank Ax C' = Nat.card G) : IsGaloisGroup G K L := by
  haveI := isFractionRing_Ax A x Ax C' K L
  haveI := finiteDimensional_frac A x Ax C' K L
  haveI := isDomain_Ax A x Ax C'
  haveI : FaithfulSMul Ax C' :=
    (faithfulSMul_iff_algebraMap_injective Ax C').mpr (injective_algebraMap_Ax A x Ax C')
  haveI : FaithfulSMul G L := IsFractionRing.faithfulSMul G C' L
  haveI : SMulCommClass G K L := IsFractionRing.smulCommClass G A C' K L
  have hrank : Module.finrank K L = Nat.card G := by
    rw [← hG]; exact Algebra.IsAlgebraic.finrank_of_isFractionRing Ax K C' L
  let f := MulSemiringAction.toAlgAut G K L
  have hinj : Function.Injective f := MulSemiringAction.toAlgEquiv_injective K L
  have hle : Nat.card Gal(L/K) ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card, ← hrank]; exact AlgEquiv.card_le
  have hge : Nat.card G ≤ Nat.card Gal(L/K) := Nat.card_le_card_of_injective f hinj
  haveI : IsGalois K L :=
    IsGalois.of_card_aut_eq_finrank K L (by rw [hrank]; exact le_antisymm hle hge)
  exact IsGaloisGroup.of_mulEquiv_algEquiv (MulEquiv.ofBijective f
    (hinj.bijective_of_nat_card_le hle)) fun _ _ => rfl

theorem isGaloisGroup_C0_frac (hG : Module.finrank Ax C' = Nat.card G) :
    IsGaloisGroup G A (C0 A C') := by
  haveI := isIntegralClosure_frac A x Ax C' K L
  haveI := finiteDimensional_frac A x Ax C' K L
  haveI := isGaloisGroup_frac A x Ax C' K L G hG
  haveI : IsFractionRing (C0 A C') L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L (C0 A C')
  haveI : SMulDistribClass G (C0 A C') L := ⟨fun g c l => smul_distrib_smul g (c : C') l⟩
  exact IsGaloisGroup.of_isFractionRing G A (C0 A C') K L

end Frac

section Concrete

universe u v

variable (A : Type u) [CommRing A] [IsDedekindDomain A] (x : A)
  (Ax : Type*) [CommRing Ax] [Algebra A Ax] [IsLocalization.Away x Ax]
  (C' : Type v) [CommRing C'] [IsDomain C'] [Algebra Ax C'] [Algebra A C'] [IsScalarTower A Ax C']
  [Algebra.Etale Ax C'] [Module.Finite Ax C']

attribute [local instance] FractionRing.liftAlgebra

/-- The `A[1/x]`-algebra structure of `Frac A` (for `x ≠ 0`). -/
noncomputable abbrev algAxFrac (hx : x ≠ 0) : Algebra Ax (FractionRing A) :=
  (IsLocalization.Away.lift x (g := algebraMap A (FractionRing A))
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr hx))).toAlgebra

include A x Ax C'

/-- Instantiate the fraction-field statements with `Frac A` and `Frac C'`. -/
theorem frac_setup {P : Prop}
    (h : ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
      [Algebra Ax K] [IsScalarTower A Ax K] [Algebra C' L] [IsFractionRing C' L] [Algebra K L]
      [Algebra Ax L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower Ax K L]
      [IsScalarTower Ax C' L] [IsScalarTower A C' L], P) : P := by
  have hx := ne_zero A x Ax C'
  letI := algAxFrac A x Ax hx
  haveI : IsScalarTower A Ax (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.Away.lift_eq x _ a).symm
  haveI : FaithfulSMul A (FractionRing C') := (faithfulSMul_iff_algebraMap_injective _ _).mpr <| by
    rw [IsScalarTower.algebraMap_eq A C' (FractionRing C')]
    exact (IsFractionRing.injective C' _).comp (injective_algebraMap_A A x Ax C')
  haveI : IsScalarTower Ax (FractionRing A) (FractionRing C') :=
    IsScalarTower.of_algebraMap_eq' <| IsLocalization.ringHom_ext (Submonoid.powers x) <| by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A Ax (FractionRing A),
        ← IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing C'),
        ← IsScalarTower.algebraMap_eq A Ax (FractionRing C')]
  exact h (FractionRing A) (FractionRing C')

/-- **`C0` is finite over `A`.** -/
theorem finite : Module.Finite A (C0 A C') :=
  frac_setup A x Ax C' fun K L => by intros; exact finite_frac A x Ax C' K L

/-- **`C0` is a Dedekind domain.** -/
theorem isDedekindDomain : IsDedekindDomain (C0 A C') :=
  frac_setup A x Ax C' fun K L => by intros; exact isDedekindDomain_frac A x Ax C' K L

/-- **`C0` is a domain.** -/
theorem isDomain : IsDomain (C0 A C') := inferInstance

/-- **Localizations of `C0` at nonzero primes are DVRs**; this applies to primes containing `x`. -/
theorem isDiscreteValuationRing (P : Ideal (C0 A C')) [P.IsPrime]
    (hxP : algebraMap A (C0 A C') x ∈ P) : IsDiscreteValuationRing (Localization.AtPrime P) := by
  haveI := isDedekindDomain A x Ax C'
  have hP : P ≠ ⊥ := by
    rintro rfl
    have h0 : algebraMap A (C0 A C') x = 0 := (Ideal.mem_bot).mp hxP
    haveI := faithfulSMul_C0 A x Ax C'
    exact ne_zero A x Ax C'
      (FaithfulSMul.algebraMap_injective A (C0 A C') (h0.trans (map_zero _).symm))
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (C0 A C') hP _

/-- An `A[1/x]`-linear action on `C'` is `A`-linear. -/
theorem smulCommClass_of_Ax (G : Type*) [Monoid G] [MulSemiringAction G C']
    [SMulCommClass G Ax C'] : SMulCommClass G A C' :=
  ⟨fun g a c => by rw [← algebraMap_smul Ax a c, smul_comm, algebraMap_smul]⟩

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G C'] [SMulCommClass G A C']
  [FaithfulSMul G C']

/-- **Galois**: a faithful `A`-linear action of `G` on `C'` with `|G| = rank_{A[1/x]} C'` makes
`G` a Galois group of `C0 / A`. -/
theorem isGaloisGroup (hG : Module.finrank Ax C' = Nat.card G) : IsGaloisGroup G A (C0 A C') :=
  frac_setup A x Ax C' fun K L => by
    intros
    letI := IsFractionRing.mulSemiringAction G C' L
    exact isGaloisGroup_C0_frac A x Ax C' K L G hG

/-- **Tameness bound**: ramification indices of `C0 / A` at maximal ideals divide `|G|`. -/
theorem ramificationIdx_dvd_card (hG : Module.finrank Ax C' = Nat.card G) (p : Ideal A)
    [p.IsMaximal] (P : Ideal (C0 A C')) [P.IsPrime] [P.LiesOver p] :
    P.ramificationIdx A ∣ Nat.card G := by
  haveI := finite A x Ax C'
  haveI := flat A x Ax C'
  haveI := isGaloisGroup A x Ax C' G hG
  exact Ideal.ramificationIdx_dvd_card (C0 A C') G P p

end Concrete

section Functorial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Functoriality of the normalisation**: an `R`-algebra endomorphism of `S` restricts to the
integral closure of `R` in `S`. -/
noncomputable def restrict (φ : S →ₐ[R] S) :
    integralClosure R S →ₐ[R] integralClosure R S :=
  φ.mapIntegralClosure

/-- The restriction is compatible with `integralClosure R S → S`. -/
theorem algebraMap_restrict (φ : S →ₐ[R] S) (c : integralClosure R S) :
    algebraMap (integralClosure R S) S (restrict φ c) =
      φ (algebraMap (integralClosure R S) S c) :=
  rfl

/-- Restriction preserves the identity. -/
theorem restrict_id : restrict (AlgHom.id R S) = AlgHom.id R (integralClosure R S) :=
  AlgHom.ext fun _ => rfl

/-- Restriction preserves composition. -/
theorem restrict_comp (φ ψ : S →ₐ[R] S) :
    restrict (φ.comp ψ) = (restrict φ).comp (restrict ψ) :=
  AlgHom.ext fun _ => rfl

/-- The restriction of an `R`-algebra automorphism of `S` to the integral closure. -/
noncomputable def restrictEquiv (φ : S ≃ₐ[R] S) :
    integralClosure R S ≃ₐ[R] integralClosure R S :=
  φ.mapIntegralClosure

/-- The restriction of an automorphism is compatible with `integralClosure R S → S`. -/
theorem algebraMap_restrictEquiv (φ : S ≃ₐ[R] S) (c : integralClosure R S) :
    algebraMap (integralClosure R S) S (restrictEquiv φ c) =
      φ (algebraMap (integralClosure R S) S c) :=
  rfl

/-- Restriction preserves the identity automorphism. -/
theorem restrictEquiv_refl : restrictEquiv (AlgEquiv.refl : S ≃ₐ[R] S) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => rfl

/-- Restriction preserves composition of automorphisms. -/
theorem restrictEquiv_trans (φ ψ : S ≃ₐ[R] S) :
    restrictEquiv (φ.trans ψ) = (restrictEquiv φ).trans (restrictEquiv ψ) :=
  AlgEquiv.ext fun _ => rfl

end Functorial

/-- For the normalisation chart: an `A[1/x]`-algebra endomorphism of `C'` restricts to
`C0 →ₐ[A] C0`, compatibly with `C0 → C'`. -/
theorem exists_restrict {A Ax C' : Type*} [CommRing A] [CommRing Ax] [CommRing C'] [Algebra A Ax]
    [Algebra Ax C'] [Algebra A C'] [IsScalarTower A Ax C'] (φ : C' →ₐ[Ax] C') :
    ∃ φ0 : C0 A C' →ₐ[A] C0 A C',
      ∀ c, algebraMap (C0 A C') C' (φ0 c) = φ (algebraMap (C0 A C') C' c) :=
  ⟨restrict (φ.restrictScalars A), fun _ => rfl⟩

end SemistableReduction.NormalizationChart
