/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Base change of an `R/J`-algebra along `S → S/JS` (Blueprint §12.8, M2.3 (d'), step κ2)

The special-fibre covering `C` of an admissible covering is an algebra over the special fibre
`R/J` of the chart. The patching compares `R̂ ⊗_R C` (`R̂` the completion of the level-`n` chart)
with `Ĉ = R̂' ⊗_{R/J} C` (`R̂'` the completion of the special fibre, where the formally Kummer
condition `Admissible.Covering.kummer` is stated). Generic statement:

**`TensorQuotBase.equiv ψ`**: for an `R`-algebra `S`, an `R/J`-algebra `S'`, and a surjective
`R`-algebra map `ψ : S → S'` with kernel `JS`, and an `R/J`-algebra `C`,
`S ⊗_R C ≃+* S' ⊗_{R/J} C`, `s ⊗ c ↦ ψ(s) ⊗ c` (`equiv_tmul`).

(With `S = R̂` and `S'` the completion of `R/J`, `ψ` is the completion of `R → R/J`, whose kernel is
`J R̂` for `R` Noetherian.)
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace TensorQuotBase

noncomputable section

variable {R : Type u} [CommRing R] (J : Ideal R)
  {S : Type u} [CommRing S] [Algebra R S]
  {S' : Type u} [CommRing S'] [Algebra R S'] [Algebra (R ⧸ J) S'] [IsScalarTower R (R ⧸ J) S']
  (C : Type u) [CommRing C] [Algebra R C] [Algebra (R ⧸ J) C] [IsScalarTower R (R ⧸ J) C]
  (ψ : S →ₐ[R] S')

/-- The forward map `S ⊗_R C → S' ⊗_{R/J} C`, `s ⊗ c ↦ ψ(s) ⊗ c`. -/
def fwd : S ⊗[R] C →ₐ[R] S' ⊗[R ⧸ J] C :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : S' →ₐ[R ⧸ J] S' ⊗[R ⧸ J] C).restrictScalars R).comp ψ)
    ((Algebra.TensorProduct.includeRight : C →ₐ[R ⧸ J] S' ⊗[R ⧸ J] C).restrictScalars R)
    fun _ _ ↦ Commute.all _ _

lemma fwd_tmul (s : S) (c : C) : fwd J C ψ (s ⊗ₜ c) = ψ s ⊗ₜ c := by
  simp [fwd]

lemma algebraMap_C_eq_zero {j : R} (hj : j ∈ J) : algebraMap R C j = 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ J) C, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hj, map_zero]

/-- The `R/J`-algebra structure on `S ⊗_R C` through `C`. -/
abbrev algQ : Algebra (R ⧸ J) (S ⊗[R] C) :=
  ((Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toRingHom.comp
    (algebraMap (R ⧸ J) C)).toAlgebra

attribute [local instance] algQ

variable {J C ψ}

variable (hψ : Function.Surjective ψ) (hker : RingHom.ker ψ = J.map (algebraMap R S))

omit [Algebra (R ⧸ J) S'] [IsScalarTower R (R ⧸ J) S'] in
include hker in
lemma ker_le : RingHom.ker ψ ≤ RingHom.ker
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] C).toRingHom := by
  rw [hker, Ideal.map_le_iff_le_comap]
  intro j hj
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_eq_smul_one, smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, algebraMap_C_eq_zero J C hj, tmul_zero]

/-- `S' = S/JS → S ⊗_R C`, `ψ(s) ↦ s ⊗ 1`. -/
def g₀ : S' →+* S ⊗[R] C :=
  (Ideal.Quotient.lift (RingHom.ker ψ)
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] C).toRingHom
    fun _ hx ↦ ker_le hker hx).comp
  (RingHom.quotientKerEquivOfSurjective hψ).symm.toRingHom

omit [Algebra (R ⧸ J) S'] [IsScalarTower R (R ⧸ J) S'] in
lemma g₀_apply (s : S) : g₀ hψ hker (ψ s) = s ⊗ₜ (1 : C) := by
  have : (RingHom.quotientKerEquivOfSurjective hψ).symm (ψ s) = Ideal.Quotient.mk _ s := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [g₀, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
  erw [this, Ideal.Quotient.lift_mk]
  rfl

/-- The inverse map `S' ⊗_{R/J} C → S ⊗_R C`. -/
def bwd : S' ⊗[R ⧸ J] C →+* S ⊗[R] C :=
  (Algebra.TensorProduct.lift
    { g₀ hψ hker with
      commutes' := fun x ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) x
        have h1 : algebraMap (R ⧸ J) S' (Ideal.Quotient.mk J r) = ψ (algebraMap R S r) := by
          rw [ψ.commutes, IsScalarTower.algebraMap_apply R (R ⧸ J) S',
            Ideal.Quotient.algebraMap_eq]
        have h2 : (algebraMap R S r) ⊗ₜ[R] (1 : C) =
            (1 : S) ⊗ₜ algebraMap (R ⧸ J) C (Ideal.Quotient.mk J r) := by
          rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
            Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := C), smul_tmul]
        rw [h1]
        refine (g₀_apply hψ hker _).trans (h2.trans ?_)
        rfl }
    { (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toRingHom with
      commutes' := fun _ ↦ rfl }
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma bwd_tmul (s : S) (c : C) : bwd hψ hker (ψ s ⊗ₜ c) = s ⊗ₜ c := by
  unfold bwd
  erw [Algebra.TensorProduct.lift_tmul]
  change g₀ hψ hker (ψ s) * ((1 : S) ⊗ₜ[R] c) = _
  rw [g₀_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **`S ⊗_R C ≃ S' ⊗_{R/J} C`** for `S' = S/JS` and `C` an `R/J`-algebra. -/
def equiv : S ⊗[R] C ≃+* S' ⊗[R ⧸ J] C :=
  RingEquiv.ofRingHom (fwd J C ψ).toRingHom (bwd hψ hker)
    (by
      refine RingHom.ext fun x ↦ ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s' c =>
        obtain ⟨s, rfl⟩ := hψ s'
        simp only [RingHom.comp_apply, bwd_tmul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          fwd_tmul, RingHom.id_apply]
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy])
    (by
      refine RingHom.ext fun x ↦ ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s c =>
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fwd_tmul,
          bwd_tmul, RingHom.id_apply]
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy])

lemma equiv_tmul (s : S) (c : C) : equiv hψ hker (s ⊗ₜ c) = ψ s ⊗ₜ c := fwd_tmul J C ψ s c

end

end TensorQuotBase

end SemistableReduction
