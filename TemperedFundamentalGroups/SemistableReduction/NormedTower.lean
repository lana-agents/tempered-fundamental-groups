/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerDefectless
import TemperedFundamentalGroups.SemistableReduction.Inertia
import TemperedFundamentalGroups.SemistableReduction.UniqueExtension

/-!
# Towers of non-archimedean normed fields

Adapters for Blueprint §9.4, step G: all fields of step G are non-archimedean normed fields, and
the valuations are the norm valuations `NormedField.valuation` (`DenseCompletion`
`hasExtension_normedField`).

* instances: an intermediate field `E` of a normed extension `N / K` acts isometrically on `N`
  (`NormedAlgebra E N`), is a normed `C`-algebra if `N` is, and is complete if `K` is and
  `E / K` is finite;
* residues: `rd_algebraMap'` (`rd (a) ↦ rd (algebraMap a)`),
  `fieldRange_algebraMap_residueField` (the image of `κ_A → κ_B` is the `residueSubfield` of the
  image of `A`);
* congruence lemmas for `inertiaDeg` along equalities of valuations, `inertiaDeg_le_finrank`,
  `inertiaDeg_pos`;
* `inertiaDeg_le_of_le`, `inertiaDeg_eq_finrank_of_le`: monotonicity of the inertia degree in
  the lattice of intermediate fields;
* `exists_normed_galois_closure`: a finite extension `B` of a complete field `K` embeds
  isometrically into a finite Galois extension `N / K` carrying the spectral norm.
-/

open Polynomial IsLocalRing Valuation

namespace SemistableReduction

open FundamentalInequality DenseCompletion KummerNormalForm DiscreteCoefficients

namespace NormedTower

section Instances

variable {K N : Type*} [NormedField K] [NormedField N] [NormedAlgebra K N]

/-- An intermediate field acts isometrically. -/
noncomputable instance normedAlgebra_intermediateField (E : IntermediateField K N) :
    NormedAlgebra E N where
  norm_smul_le a x := le_of_eq (by rw [Algebra.smul_def, norm_mul]; rfl)

/-- A subfield acts isometrically. -/
noncomputable instance normedAlgebra_subfield (S : Subfield N) : NormedAlgebra S N where
  norm_smul_le a x := le_of_eq (by rw [Algebra.smul_def, norm_mul]; rfl)

/-- An intermediate field of an extension of normed `C`-algebras is a normed `C`-algebra. -/
noncomputable instance normedAlgebra_intermediateField' {C : Type*} [NormedField C]
    [NormedAlgebra C N] [Algebra C K] [IsScalarTower C K N] (E : IntermediateField K N) :
    NormedAlgebra C E where
  norm_smul_le c x := norm_smul_le c (x : N)

/-- A finite intermediate field over a complete field is complete. -/
instance completeSpace_intermediateField {K : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] [NormedAlgebra K N] (E : IntermediateField K N) [FiniteDimensional K E] :
    CompleteSpace E :=
  FiniteDimensional.complete K E

end Instances

section Residue

variable {A B : Type*} [NormedField A] [IsUltrametricDist A] [NormedField B] [IsUltrametricDist B]
  [NormedAlgebra A B]

local notation "κ" X => ResidueField (HenselComplete.integers X)

lemma rd_algebraMap' {a : A} (ha : ‖a‖ ≤ 1) :
    rd (algebraMap A B a) = algebraMap (κ A) (κ B) (rd a) := by
  set a' : HenselComplete.integers A := ⟨a, (HenselComplete.mem_integers_iff a).2 ha⟩
  rw [show a = (a' : A) from rfl, rd_coe,
    HasExtension.algebraMap_residue_eq_residue_algebraMap, ← rd_coe,
    HasExtension.coe_algebraMap_valuationSubring_eq]

/-- The image of the residue field of `A` in that of `B` is the residue field of the image
of `A`. -/
theorem fieldRange_algebraMap_residueField :
    (algebraMap (κ A) (κ B)).fieldRange = residueSubfield (algebraMap A B).fieldRange := by
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨a, rfl⟩ := residue_surjective s
    rw [← rd_coe, ← rd_algebraMap' (HenselComplete.norm_le_one a)]
    exact rd_mem_residueSubfield ⟨a, rfl⟩
      ((norm_algebraMap' B (a : A)).trans_le (HenselComplete.norm_le_one a))
  · rintro ⟨_, ⟨a, rfl⟩, ha1, rfl⟩
    rw [norm_algebraMap'] at ha1
    exact ⟨rd a, (rd_algebraMap' ha1).symm⟩

end Residue

section Congr

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]

lemma inertiaDeg_congr {v : Valuation K Γ₀} {w w' : Valuation L Γ₁} [v.HasExtension w]
    [v.HasExtension w'] (h : w = w') : inertiaDeg v w = inertiaDeg v w' := by
  subst h
  rfl

lemma inertiaDeg_congr_left {v v' : Valuation K Γ₀} {w : Valuation L Γ₁} [v.HasExtension w]
    [v'.HasExtension w] (h : v = v') : inertiaDeg v w = inertiaDeg v' w := by
  subst h
  rfl

lemma isSeparable_congr {v : Valuation K Γ₀} {w w' : Valuation L Γ₁} [v.HasExtension w]
    [v.HasExtension w'] (h : w = w')
    [Algebra.IsSeparable (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)] :
    Algebra.IsSeparable (ResidueField v.valuationSubring) (ResidueField w'.valuationSubring) := by
  subst h
  assumption

lemma isPurelyInseparable_congr_left {v v' : Valuation K Γ₀} {w : Valuation L Γ₁}
    [v.HasExtension w] [v'.HasExtension w] (h : v = v')
    [IsPurelyInseparable (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)] :
    IsPurelyInseparable (ResidueField v'.valuationSubring) (ResidueField w.valuationSubring) := by
  subst h
  assumption

variable [FiniteDimensional K L] {v : Valuation K Γ₀} {w : Valuation L Γ₁} [v.HasExtension w]

lemma inertiaDeg_pos : 0 < inertiaDeg v w := by
  haveI := finite_residueField (v := v) (w := w)
  exact Module.finrank_pos

lemma inertiaDeg_le_finrank : inertiaDeg v w ≤ Module.finrank K L :=
  (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (ramificationIdx_ne_zero (K := K) w))).trans
    ramificationIdx_mul_inertiaDeg_le

end Congr

section Tower

variable {K A A' : Type*} [NormedField K] [IsUltrametricDist K] [NormedField A]
  [IsUltrametricDist A] [NormedField A'] [IsUltrametricDist A'] [NormedAlgebra K A]
  [NormedAlgebra A A'] [NormedAlgebra K A'] [IsScalarTower K A A'] [FiniteDimensional K A]
  [FiniteDimensional A A']

omit [FiniteDimensional K A] in
/-- The inertia degree grows in towers `K ⊆ A ⊆ A'`. -/
theorem inertiaDeg_le_of_tower :
    inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A)) ≤
      inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A')) := by
  rw [inertiaDeg_tower _ (NormedField.valuation (K := A)) (NormedField.valuation (K := A'))]
  exact Nat.le_mul_of_pos_left _ (inertiaDeg_pos (v := NormedField.valuation (K := A))
    (w := NormedField.valuation (K := A')))

/-- In a tower `K ⊆ A ⊆ A'` with `A' / K` unramified (`f = [A' : K]`), both steps are
unramified. -/
theorem inertiaDeg_eq_finrank_of_tower
    (h : inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A')) =
      Module.finrank K A') :
    inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A)) =
        Module.finrank K A ∧
      inertiaDeg (NormedField.valuation (K := A)) (NormedField.valuation (K := A')) =
        Module.finrank A A' := by
  haveI : FiniteDimensional K A' := Module.Finite.trans A A'
  rw [inertiaDeg_tower _ (NormedField.valuation (K := A)) (NormedField.valuation (K := A')),
    ← Module.finrank_mul_finrank K A A'] at h
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_eq
    (inertiaDeg_le_finrank (v := NormedField.valuation (K := A))
      (w := NormedField.valuation (K := A')))
    (inertiaDeg_le_finrank (v := NormedField.valuation (K := K))
      (w := NormedField.valuation (K := A)))
    Module.finrank_pos Module.finrank_pos (h.trans (mul_comm _ _))
  exact ⟨h2, h1⟩

end Tower

section Lattice

variable {K N : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NormedField N]
  [IsUltrametricDist N] [NormedAlgebra K N] [FiniteDimensional K N]

/-- The inclusion `A ⊆ A'` of intermediate fields as a normed algebra. -/
private noncomputable abbrev inclusionAlgebra {A A' : IntermediateField K N} (h : A ≤ A') :
    NormedAlgebra A A' :=
  letI : Algebra A A' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  { norm_smul_le := fun a x ↦ le_of_eq (by rw [Algebra.smul_def, norm_mul]; rfl) }

/-- The inertia degree is monotone in the lattice of intermediate fields. -/
theorem inertiaDeg_le_of_le {A A' : IntermediateField K N} (h : A ≤ A') :
    inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A)) ≤
      inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A')) := by
  letI := inclusionAlgebra h
  haveI : IsScalarTower K A A' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional A A' := Module.Finite.of_restrictScalars_finite K A A'
  exact inertiaDeg_le_of_tower

/-- An intermediate field of an unramified extension (`f = [A' : K]`) is unramified. -/
theorem inertiaDeg_eq_finrank_of_le {A A' : IntermediateField K N} (h : A ≤ A')
    (hA' : inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A')) =
      Module.finrank K A') :
    inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := A)) =
      Module.finrank K A := by
  letI := inclusionAlgebra h
  haveI : IsScalarTower K A A' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional A A' := Module.Finite.of_restrictScalars_finite K A A'
  exact (inertiaDeg_eq_finrank_of_tower hA').1

end Lattice

section ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ₀ Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  [LinearOrderedCommGroupWithZero Γ₂]
  {v : Valuation K Γ₀} {w : Valuation L Γ₁} {w' : Valuation L Γ₂} [v.HasExtension w]
  [v.HasExtension w']

/-- Extensions with the same valuation ring have isomorphic residue fields. -/
noncomputable def residueAlgEquivOfEq (h : w.valuationSubring = w'.valuationSubring) :
    ResidueField w.valuationSubring ≃ₐ[ResidueField v.valuationSubring]
      ResidueField w'.valuationSubring :=
  let e : w.valuationSubring ≃+* w'.valuationSubring :=
    { toFun := fun x ↦ ⟨x, h ▸ x.2⟩
      invFun := fun x ↦ ⟨x, h.symm ▸ x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv e) fun r ↦ by
    obtain ⟨a, rfl⟩ := residue_surjective r
    rw [HasExtension.algebraMap_residue_eq_residue_algebraMap,
      HasExtension.algebraMap_residue_eq_residue_algebraMap,
      IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    congr 1

/-- Extensions with the same valuation ring have the same inertia degree. -/
theorem inertiaDeg_eq_of_valuationSubring_eq (h : w.valuationSubring = w'.valuationSubring) :
    inertiaDeg v w = inertiaDeg v w' :=
  (residueAlgEquivOfEq h).toLinearEquiv.finrank_eq

/-- Separability of the residue field extension only depends on the valuation ring. -/
theorem isSeparable_of_valuationSubring_eq (h : w.valuationSubring = w'.valuationSubring)
    [Algebra.IsSeparable (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)] :
    Algebra.IsSeparable (ResidueField v.valuationSubring) (ResidueField w'.valuationSubring) :=
  AlgEquiv.Algebra.isSeparable (residueAlgEquivOfEq h)

end ValuationSubring

section FieldRange

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The degree over the image of the base field. -/
lemma finrank_fieldRange_eq :
    Module.finrank (algebraMap F E).fieldRange E = Module.finrank F E :=
  (Algebra.finrank_eq_of_equiv_equiv (algebraMap F E).rangeRestrictFieldEquiv (RingEquiv.refl E)
    (by ext; rfl)).symm

lemma finite_fieldRange_iff :
    Module.Finite (algebraMap F E).fieldRange E ↔ Module.Finite F E := by
  letI : Algebra F (algebraMap F E).fieldRange :=
    (algebraMap F E).rangeRestrictFieldEquiv.toRingHom.toAlgebra
  haveI : IsScalarTower F (algebraMap F E).fieldRange E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨fun _ ↦ ?_, fun _ ↦ Module.Finite.of_restrictScalars_finite F _ E⟩
  haveI : Module.Finite F (algebraMap F E).fieldRange := Module.Finite.of_surjective
    (Algebra.linearMap F _) (algebraMap F E).rangeRestrictFieldEquiv.surjective
  exact Module.Finite.trans (algebraMap F E).fieldRange E

lemma isSeparable_fieldRange_iff :
    Algebra.IsSeparable (algebraMap F E).fieldRange E ↔ Algebra.IsSeparable F E := by
  letI : Algebra F (algebraMap F E).fieldRange :=
    (algebraMap F E).rangeRestrictFieldEquiv.toRingHom.toAlgebra
  haveI : IsScalarTower F (algebraMap F E).fieldRange E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨fun _ ↦ ?_, fun _ ↦ Algebra.isSeparable_tower_top_of_isSeparable F _ E⟩
  haveI : Algebra.IsSeparable F (algebraMap F E).fieldRange := ⟨fun r ↦ by
    obtain ⟨f, rfl⟩ := (algebraMap F E).rangeRestrictFieldEquiv.surjective r
    exact isSeparable_algebraMap (K := (algebraMap F E).fieldRange) f⟩
  exact Algebra.IsSeparable.trans F (algebraMap F E).fieldRange E

end FieldRange

section Closure

universe u

variable (C : Type*) (K B : Type u) [NormedField C] [NontriviallyNormedField K]
  [IsUltrametricDist K]
  [CompleteSpace K] [NormedAlgebra C K] [NormedField B] [NormedAlgebra K B] [FiniteDimensional K B]
  [CharZero K] [Algebra.IsSeparable K B]

/-- **Normed Galois closure.** A finite separable extension `B` of a complete field `K` embeds
isometrically into a finite Galois extension `N / K` (the normal closure of `B` in an algebraic
closure, with the spectral norm). -/
theorem exists_normed_galois_closure :
    ∃ (N : Type u) (_ : NormedField N) (_ : NormedAlgebra K N) (_ : NormedAlgebra B N)
      (_ : IsScalarTower K B N) (_ : NormedAlgebra C N) (_ : IsScalarTower C K N)
      (_ : FiniteDimensional K N) (_ : IsGalois K N), IsUltrametricDist N := by
  let L := AlgebraicClosure B
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.trans K B L
  haveI : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : NormedAlgebra B L := spectralNorm.normedAlgebra' K B L
  let N := IntermediateField.normalClosure K B L
  letI : NormedAlgebra B N :=
    { norm_smul_le := fun b x ↦ le_of_eq (by
        rw [Algebra.smul_def, norm_mul]
        congr 1
        change ‖algebraMap N L (algebraMap B N b)‖ = ‖b‖
        rw [← IsScalarTower.algebraMap_apply B N L, norm_algebraMap']) }
  letI : Algebra C N := ((algebraMap K N).comp (algebraMap C K)).toAlgebra
  haveI : IsScalarTower C K N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : NormedAlgebra C N :=
    { norm_smul_le := fun c x ↦ le_of_eq (by
        rw [Algebra.smul_def, norm_mul, IsScalarTower.algebraMap_apply C K N, norm_algebraMap',
          norm_algebraMap']) }
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, IsUltrametricDist.of_normedAlgebra K⟩

end Closure

end NormedTower

end SemistableReduction
