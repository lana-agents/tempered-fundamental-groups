/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Normalization commutes with étale base change

Blueprint §9.2 (ii), layer (b). Let `A → A'` be étale, `L` an `A`-algebra and `B` the integral
closure of `A` in `L`. Then `A' ⊗_A B` is the integral closure of `A'` in `A' ⊗_A L`: the
comparison map `A' ⊗_A B → A' ⊗_A L` is injective, and its image is the integral closure.

This is the ring-level form of "the normalization of `𝒳` in a cover commutes with étale
localization on `𝒳`", which reduces the local structure of normalizations to étale-local models
(nodes `O[u, v] ⧸ (u v - ϖ ^ n)` and the affine line `O[u]`, `SemistableReduction/LocalModel`).
It is a thin wrapper around Mathlib's `TensorProduct.toIntegralClosure_bijective_of_smooth`
(smooth base change commutes with integral closure).

* `integralClosureTensorEquiv`: `A' ⊗_A (integralClosure A L) ≃ integralClosure A' (A' ⊗_A L)`;
* `tensorIntegralClosureMap`: the comparison map `A' ⊗_A B → A' ⊗_A L` for any integral
  closure `B` of `A` in `L` (`IsIntegralClosure B A L`);
* `tensorIntegralClosureMap_injective`, `range_tensorIntegralClosureMap`: it is injective with
  image the integral closure of `A'`;
* `isIntegralClosure_tensorProduct`: hence `IsIntegralClosure (A' ⊗_A B) A' (A' ⊗_A L)`.
-/

open TensorProduct

namespace SemistableReduction

variable {A A' L : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [CommRing L] [Algebra A L]

variable (A A' L) in
/-- **Étale base change commutes with integral closure**:
`A' ⊗_A (integralClosure A L) ≃ integralClosure A' (A' ⊗_A L)` for `A → A'` étale. -/
noncomputable def integralClosureTensorEquiv [Algebra.Etale A A'] :
    A' ⊗[A] integralClosure A L ≃ₐ[A'] integralClosure A' (A' ⊗[A] L) :=
  AlgEquiv.ofBijective _ TensorProduct.toIntegralClosure_bijective_of_smooth

@[simp]
lemma integralClosureTensorEquiv_tmul [Algebra.Etale A A'] (a : A') (b : integralClosure A L) :
    (integralClosureTensorEquiv A A' L (a ⊗ₜ b) : A' ⊗[A] L) = a ⊗ₜ (b : L) :=
  rfl

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]

variable (A A' B L) in
/-- The comparison map `A' ⊗_A B → A' ⊗_A L`. -/
noncomputable def tensorIntegralClosureMap : A' ⊗[A] B →ₐ[A'] A' ⊗[A] L :=
  Algebra.TensorProduct.map (AlgHom.id A' A') (IsScalarTower.toAlgHom A B L)

@[simp]
lemma tensorIntegralClosureMap_tmul (a : A') (b : B) :
    tensorIntegralClosureMap A A' L B (a ⊗ₜ b) = a ⊗ₜ algebraMap B L b :=
  rfl

variable [IsIntegralClosure B A L]

variable (A A' B L) in
/-- `A' ⊗_A B ≃ integralClosure A' (A' ⊗_A L)` for `A → A'` étale and `B` the integral closure
of `A` in `L`. -/
noncomputable def tensorIntegralClosureEquiv [Algebra.Etale A A'] :
    A' ⊗[A] B ≃ₐ[A'] integralClosure A' (A' ⊗[A] L) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (IsIntegralClosure.equiv A B L _)).trans
    (integralClosureTensorEquiv A A' L)

lemma coe_tensorIntegralClosureEquiv [Algebra.Etale A A'] (x : A' ⊗[A] B) :
    (tensorIntegralClosureEquiv A A' L B x : A' ⊗[A] L) = tensorIntegralClosureMap A A' L B x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul a b =>
    simp only [tensorIntegralClosureEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, integralClosureTensorEquiv_tmul,
      tensorIntegralClosureMap_tmul]
    congr 1
    exact IsIntegralClosure.algebraMap_equiv A B L (integralClosure A L) b

/-- The comparison map `A' ⊗_A B → A' ⊗_A L` is injective for `A → A'` étale. -/
theorem tensorIntegralClosureMap_injective [Algebra.Etale A A'] :
    Function.Injective (tensorIntegralClosureMap A A' L B) := by
  intro x y h
  apply (tensorIntegralClosureEquiv A A' L B).injective
  apply Subtype.ext
  rw [coe_tensorIntegralClosureEquiv, coe_tensorIntegralClosureEquiv, h]

/-- **Normalization commutes with étale base change.** For `A → A'` étale and `B` the integral
closure of `A` in `L`, the image of `A' ⊗_A B → A' ⊗_A L` is the integral closure of `A'` in
`A' ⊗_A L`. -/
theorem range_tensorIntegralClosureMap [Algebra.Etale A A'] :
    (tensorIntegralClosureMap A A' L B).range = integralClosure A' (A' ⊗[A] L) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change tensorIntegralClosureMap A A' L B x ∈ _
    rw [← coe_tensorIntegralClosureEquiv]
    exact (tensorIntegralClosureEquiv A A' L B x).2
  · intro hy
    refine ⟨(tensorIntegralClosureEquiv A A' L B).symm ⟨y, hy⟩, ?_⟩
    change tensorIntegralClosureMap A A' L B _ = _
    rw [← coe_tensorIntegralClosureEquiv, AlgEquiv.apply_symm_apply]

/-- **Normalization commutes with étale base change** (`IsIntegralClosure` form): for `A → A'`
étale and `B` the integral closure of `A` in `L`, `A' ⊗_A B` (mapping to `A' ⊗_A L` by
`tensorIntegralClosureMap`) is the integral closure of `A'` in `A' ⊗_A L`. -/
theorem isIntegralClosure_tensorProduct [Algebra.Etale A A'] :
    letI := (tensorIntegralClosureMap A A' L B).toRingHom.toAlgebra
    IsIntegralClosure (A' ⊗[A] B) A' (A' ⊗[A] L) := by
  letI := (tensorIntegralClosureMap A A' L B).toRingHom.toAlgebra
  haveI : IsScalarTower A' (A' ⊗[A] B) (A' ⊗[A] L) :=
    .of_algebraMap_eq fun x ↦ ((tensorIntegralClosureMap A A' L B).commutes x).symm
  refine ⟨tensorIntegralClosureMap_injective, fun {y} ↦ ?_⟩
  have := congrArg (y ∈ ·) (range_tensorIntegralClosureMap (A := A) (A' := A') (B := B) (L := L))
  simp only [AlgHom.mem_range, mem_integralClosure_iff, eq_iff_iff] at this
  exact this.symm

end SemistableReduction
