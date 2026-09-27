/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import TemperedFundamentalGroups.Models.Specialization

/-!
# Projective space over a ring and projective model codes

* `projSpace R m`: projective space `ℙᵐ_R = Proj R[x₀, …, xₘ]`, with the proper structure
  morphism `projSpace.toSpec R m : ℙᵐ_R ⟶ Spec R`; for `m = 0` it is an isomorphism.
* `ModelCode R`: a closed subscheme of some `ℙᵐ_R`, coded by an ideal sheaf (so codes live in
  `Type u`); `ModelCode.toSpec c` is proper.
* `ModelCode.trivial R`: the code of `ℙ⁰_R ≅ Spec R`; its special fibre is a subsingleton.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-- Projective `m`-space over `R`, as `Proj R[x₀, …, xₘ]`. -/
noncomputable def projSpace (m : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)

/-- The degree-zero part of `R[x₀, …, xₘ]` is `R`. -/
lemma bijective_algebraMap_projSpace (m : ℕ) :
    Function.Bijective
      (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0)) := by
  refine ⟨fun a b h ↦ ?_, fun p ↦ ?_⟩
  · have := congrArg Subtype.val h
    simpa using this
  · have hp : (p : MvPolynomial (Fin (m + 1)) R) ∈ (1 : Submodule R _) := by
      rw [← MvPolynomial.homogeneousSubmodule_zero]
      exact p.2
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
    exact ⟨r, Subtype.ext hr⟩

instance (m : ℕ) : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0)
    (MvPolynomial (Fin (m + 1)) R) :=
  IsScalarTower.of_algebraMap_eq (R := R)
    (S := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0) fun _ ↦ rfl

instance (m : ℕ) : Algebra.FiniteType
    (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0) (MvPolynomial (Fin (m + 1)) R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

/-- The structure morphism `ℙᵐ_R ⟶ Spec R`. -/
noncomputable def projSpace.toSpec (m : ℕ) : projSpace R m ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0)))

instance (m : ℕ) : IsIso (Spec.map (CommRingCat.ofHom
    (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0)))) := by
  have : IsIso (CommRingCat.ofHom
      (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_algebraMap_projSpace R m)
  infer_instance

instance (m : ℕ) : IsProper (projSpace.toSpec R m) := by
  unfold projSpace.toSpec
  have : IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)) :=
    inferInstance
  have : IsProper (Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 0)))) :=
    MorphismProperty.of_isIso @IsProper _
  exact MorphismProperty.comp_mem @IsProper _ _ ‹_› ‹_›

/-! ### `ℙ⁰_R = Spec R` -/

section ProjZero

open MvPolynomial HomogeneousLocalization

variable {R}

lemma isHomogeneous_fin_one {p : MvPolynomial (Fin (0 + 1)) R} {n : ℕ} (hp : p.IsHomogeneous n) :
    p = C (coeff (Finsupp.single 0 n) p) * X 0 ^ n := by
  ext d
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hd : Finsupp.single 0 n = d
  · subst hd
    simp
  · rw [if_neg hd, mul_zero]
    refine hp.coeff_eq_zero fun h ↦ hd ?_
    ext i
    rw [Fin.fin_one_eq_zero i, Finsupp.single_eq_same, ← h]
    simp [Finsupp.degree_eq_sum]

lemma X_zero_mem_homogeneousSubmodule :
    (X 0 : MvPolynomial (Fin (0 + 1)) R) ∈ homogeneousSubmodule (Fin (0 + 1)) R 1 :=
  isHomogeneous_X R 0

lemma X_zero_not_mem (x : projSpace R 0) :
    (X 0 : MvPolynomial (Fin (0 + 1)) R) ∉ x.asHomogeneousIdeal := by
  intro h
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  change a ∈ homogeneousSubmodule (Fin (0 + 1)) R i at ha
  change a ∈ x.asHomogeneousIdeal.toIdeal
  rw [isHomogeneous_fin_one ha]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h i hi)

lemma bijective_fromZeroRingHom_projSpace_zero :
    Function.Bijective (fromZeroRingHom (homogeneousSubmodule (Fin (0 + 1)) R)
      (Submonoid.powers (X 0))) := by
  refine ⟨fun a b h ↦ ?_, fun z ↦ ?_⟩
  · have h' := congrArg HomogeneousLocalization.val h
    have hle : Submonoid.powers (X 0 : MvPolynomial (Fin (0 + 1)) R) ≤
        nonZeroDivisors _ := by
      rintro _ ⟨k, rfl⟩
      exact (isRegular_X_pow k).mem_nonZeroDivisors
    have hinj : Function.Injective (algebraMap (MvPolynomial (Fin (0 + 1)) R)
        (Localization.Away (X 0 : MvPolynomial (Fin (0 + 1)) R))) :=
      IsLocalization.injective _ hle
    refine Subtype.ext (hinj ?_)
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap]
    exact h'
  · obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (homogeneousSubmodule (Fin (0 + 1)) R)
      X_zero_mem_homogeneousSubmodule z
    have ha' : a.IsHomogeneous n := by simpa using ha
    refine ⟨⟨C (coeff (Finsupp.single 0 n) a), isHomogeneous_C _ _⟩, ?_⟩
    apply val_injective
    rw [Away.val_mk]
    change Localization.mk _ 1 = _
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    conv_rhs => rw [isHomogeneous_fin_one ha']
    simp [mul_comm]

instance isIso_projSpace_toSpec_zero : IsIso (projSpace.toSpec R 0) := by
  let 𝒜 := homogeneousSubmodule (Fin (0 + 1)) R
  have hι : IsIso (Proj.awayι 𝒜 (X 0) X_zero_mem_homogeneousSubmodule zero_lt_one) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x ↦ ?_⟩⟩
    have hx : x ∈ (Proj.awayι 𝒜 (X 0) X_zero_mem_homogeneousSubmodule zero_lt_one).opensRange := by
      rw [Proj.opensRange_awayι]
      exact X_zero_not_mem x
    exact hx
  have hS : IsIso (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers (X 0))))) := by
    have : IsIso (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers (X 0)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr bijective_fromZeroRingHom_projSpace_zero
    infer_instance
  have hc := Proj.awayι_toSpecZero 𝒜 (X 0) X_zero_mem_homogeneousSubmodule zero_lt_one
  have : IsIso (Proj.toSpecZero 𝒜) := by
    have : IsIso (Proj.awayι 𝒜 (X 0) X_zero_mem_homogeneousSubmodule zero_lt_one ≫
        Proj.toSpecZero 𝒜) := by
      rw [hc]
      exact hS
    exact IsIso.of_isIso_comp_left
      (Proj.awayι 𝒜 (X 0) X_zero_mem_homogeneousSubmodule zero_lt_one) _
  have h2 : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := inferInstance
  exact MorphismProperty.comp_mem (MorphismProperty.isomorphisms _) _ _ this h2

end ProjZero

/-! ### Model codes -/

/-- A *model code* over `R`: a closed subscheme of some projective space `ℙᵐ_R`, given by an ideal
sheaf. Codes live in `Type u`, so that they can index categories in `Type u`. -/
structure ModelCode : Type u where
  /-- The dimension of the ambient projective space. -/
  m : ℕ
  /-- The ideal sheaf cutting out the model. -/
  I : (projSpace R m).IdealSheafData

namespace ModelCode

variable {R}

/-- The scheme described by a model code. -/
noncomputable def scheme (c : ModelCode R) : Scheme.{u} :=
  c.I.subscheme

/-- The structure morphism of the scheme described by a model code. -/
noncomputable def toSpec (c : ModelCode R) : c.scheme ⟶ Spec (CommRingCat.of R) :=
  c.I.subschemeι ≫ projSpace.toSpec R c.m

instance (c : ModelCode R) : IsProper c.toSpec := by
  unfold toSpec scheme
  infer_instance

variable (R) in
/-- The trivial model code: `ℙ⁰_R = Spec R` itself. -/
noncomputable def trivial : ModelCode R where
  m := 0
  I := ⊥

instance : IsIso (trivial R).toSpec := by
  unfold toSpec
  have h₁ : IsIso (trivial R).I.subschemeι :=
    inferInstanceAs (IsIso (Scheme.IdealSheafData.subschemeι ⊥))
  have h₂ : IsIso (projSpace.toSpec R (trivial R).m) := isIso_projSpace_toSpec_zero
  exact MorphismProperty.comp_mem (MorphismProperty.isomorphisms _) _ _ h₁ h₂

lemma trivial_toSpec_injective : Function.Injective (trivial R).toSpec :=
  (Scheme.homeoOfIso (asIso (trivial R).toSpec)).injective

instance [IsLocalRing R] : Subsingleton (specialFibre (trivial R).toSpec) :=
  ⟨fun x y ↦ Subtype.ext (trivial_toSpec_injective (x.2.trans y.2.symm))⟩

end ModelCode

end TemperedFundamentalGroups
