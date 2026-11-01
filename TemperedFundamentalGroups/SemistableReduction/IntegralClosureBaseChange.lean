/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleBaseChange
import TemperedFundamentalGroups.SemistableReduction.SmoothBaseChange
import TemperedFundamentalGroups.SemistableReduction.TateChartBaseChange

/-!
# Normalisation commutes with étale base change of the base ring (MR12 S5.7)

Let `O → O'` be étale, `T` an `O`-algebra and `B` the integral closure of `T` in a `T`-algebra
`L` (all compatibly `O`-algebras). Then `O' ⊗_O B` is the integral closure of `O' ⊗_O T` in
`O' ⊗_O L`. This is `isIntegralClosure_tensorProduct` for the étale map `T → O' ⊗_O T`
(`etale_includeRight_base`), transported along `(O' ⊗_O T) ⊗_T M ≃ O' ⊗_O M`
(`Algebra.IsPushout.cancelBaseChangeAlg`).

* **`IsIntegralClosure.of_ringEquiv`**: `IsIntegralClosure` is transported along ring
  isomorphisms of the three rings compatible with the structure maps;
  **`IsIntegralClosure.of_ringEquiv_base`**: the special case of an isomorphism of the base;
* `baseChangeMap`, `baseChangeAlgebra`: the map `O' ⊗_O M → O' ⊗_O N` of an `O`-algebra tower
  `M → N` and the induced algebra structure; `baseChangeAlgebraOfEquiv`: the `T'`-algebra
  structure on `O' ⊗_O N` through an isomorphism `O' ⊗_O T ≃ₐ[O'] T'`;
* **`isIntegralClosure_baseChange`**: `IsIntegralClosure (O' ⊗_O B) (O' ⊗_O T) (O' ⊗_O L)`;
* **`isIntegralClosure_baseChange_of_equiv`**: the same with `O' ⊗_O T` replaced by `T'`;
* **`TateTwoChart.isIntegralClosure_baseChangeT0`**,
  **`TateTwoChart.isIntegralClosure_baseChangeT1`**: the Tate charts, with base `T0'`, `T1'`
  through `baseChangeT0`, `baseChangeT1`.
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

section Transport

variable {A B L A' B' L' : Type*} [CommRing A] [CommRing B] [CommRing L] [CommRing A']
  [CommRing B'] [CommRing L'] [Algebra A L] [Algebra B L] [Algebra A' L'] [Algebra B' L']

/-- **Transport of `IsIntegralClosure` along ring isomorphisms**: if `B` is the integral closure
of `A` in `L` and `A ≃ A'`, `B ≃ B'`, `L ≃ L'` are compatible with the structure maps, then `B'`
is the integral closure of `A'` in `L'`. -/
theorem IsIntegralClosure.of_ringEquiv [IsIntegralClosure B A L] (eA : A ≃+* A')
    (eB : B ≃+* B') (eL : L ≃+* L')
    (hA : ∀ a, eL (algebraMap A L a) = algebraMap A' L' (eA a))
    (hB : ∀ b, eL (algebraMap B L b) = algebraMap B' L' (eB b)) :
    IsIntegralClosure B' A' L' := by
  have hB' : ∀ b', algebraMap B' L' b' = eL (algebraMap B L (eB.symm b')) := fun b' ↦ by
    rw [hB, RingEquiv.apply_symm_apply]
  refine ⟨fun x y h ↦ ?_, fun {x} ↦ ?_⟩
  · rw [hB', hB'] at h
    exact eB.symm.injective (IsIntegralClosure.algebraMap_injective B A L (eL.injective h))
  constructor
  · intro hx
    have h1 : IsIntegral A (eL.symm x) := by
      refine IsIntegral.map_of_comp_eq eA.symm.toRingHom eL.symm.toRingHom ?_ hx
      ext a
      apply eL.injective
      simp [hA]
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp h1
    exact ⟨eB y, by rw [← hB, hy, RingEquiv.apply_symm_apply]⟩
  · rintro ⟨y, rfl⟩
    rw [hB']
    have h1 : IsIntegral A (algebraMap B L (eB.symm y)) :=
      (IsIntegralClosure.isIntegral_iff (A := B)).mpr ⟨eB.symm y, rfl⟩
    refine IsIntegral.map_of_comp_eq eA.toRingHom eL.toRingHom ?_ h1
    ext a
    simp [hA]

end Transport

/-- **Transport of `IsIntegralClosure` along an isomorphism of the base**: if `C` is the integral
closure of `A` in `L` and `e : A ≃ A'` is compatible with the structure maps to `L`, then `C` is
the integral closure of `A'` in `L`. -/
theorem IsIntegralClosure.of_ringEquiv_base {A A' C L : Type*} [CommRing A] [CommRing A']
    [CommRing C] [CommRing L] [Algebra A L] [Algebra A' L] [Algebra C L]
    [IsIntegralClosure C A L] (e : A ≃+* A') (h : ∀ a, algebraMap A' L (e a) = algebraMap A L a) :
    IsIntegralClosure C A' L :=
  IsIntegralClosure.of_ringEquiv e (RingEquiv.refl C) (RingEquiv.refl L) (fun a ↦ (h a).symm)
    (fun _ ↦ rfl)

section BaseChange

variable (O O' : Type u) [CommRing O] [CommRing O'] [Algebra O O']

/-- The base change `O' ⊗_O M → O' ⊗_O N` of an `O`-algebra tower `M → N`. -/
abbrev baseChangeMap (M N : Type*) [CommRing M] [CommRing N] [Algebra O M] [Algebra O N]
    [Algebra M N] [IsScalarTower O M N] : O' ⊗[O] M →ₐ[O'] O' ⊗[O] N :=
  Algebra.TensorProduct.map (AlgHom.id O' O') (IsScalarTower.toAlgHom O M N)

/-- The `O' ⊗_O M`-algebra structure on `O' ⊗_O N` given by `baseChangeMap`. -/
abbrev baseChangeAlgebra (M N : Type*) [CommRing M] [CommRing N] [Algebra O M] [Algebra O N]
    [Algebra M N] [IsScalarTower O M N] : Algebra (O' ⊗[O] M) (O' ⊗[O] N) :=
  (baseChangeMap O O' M N).toRingHom.toAlgebra

/-- The `T'`-algebra structure on `O' ⊗_O N` through an isomorphism `e : O' ⊗_O T ≃ₐ[O'] T'`. -/
abbrev baseChangeAlgebraOfEquiv {T T' : Type*} [CommRing T] [CommRing T'] [Algebra O T]
    [Algebra O' T'] (e : O' ⊗[O] T ≃ₐ[O'] T') (N : Type*) [CommRing N] [Algebra O N]
    [Algebra T N] [IsScalarTower O T N] : Algebra T' (O' ⊗[O] N) :=
  ((baseChangeMap O O' T N).comp e.symm.toAlgHom).toRingHom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (T : Type u) [CommRing T] [Algebra O T] (L : Type*) [CommRing L] [Algebra O L]
  [Algebra T L] [IsScalarTower O T L]

/-- The base change map `O' ⊗_O T → O' ⊗_O L` composed with the inverse of
`(O' ⊗_O T) ⊗_T L ≃ O' ⊗_O L` is the structure map. -/
lemma cancelBaseChangeAlg_symm_baseChangeMap (x : O' ⊗[O] T) :
    (Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) L).symm (baseChangeMap O O' T L x) =
      algebraMap (O' ⊗[O] T) ((O' ⊗[O] T) ⊗[T] L) x := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | tmul o s =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    simp only [AlgHom.id_apply, Algebra.algebraMap_self, RingHom.id_apply,
      IsScalarTower.coe_toAlgHom', Algebra.algebraMap_eq_smul_one s]
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

variable (B : Type*) [CommRing B] [Algebra O B] [Algebra T B] [Algebra B L]
  [IsScalarTower O T B] [IsScalarTower O B L] [IsScalarTower T B L]

/-- Under `(O' ⊗_O T) ⊗_T M ≃ O' ⊗_O M` (for `M = B, L`), the comparison map
`tensorIntegralClosureMap` becomes `baseChangeMap`. -/
lemma cancelBaseChangeAlg_tensorIntegralClosureMap (x : O' ⊗[O] B) :
    Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) L
        (tensorIntegralClosureMap T (O' ⊗[O] T) L B
          ((Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) B).symm x)) =
      baseChangeMap O O' B L x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul o b =>
    rw [Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul, tensorIntegralClosureMap_tmul,
      ← Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul O O' T (O' ⊗[O] T) L,
      AlgEquiv.apply_symm_apply]
    rfl

/-- **Normalisation commutes with étale base change of the base ring**: for `O → O'` étale and
`B` the integral closure of the `O`-algebra `T` in `L`, `O' ⊗_O B` is the integral closure of
`O' ⊗_O T` in `O' ⊗_O L` (structure maps `baseChangeAlgebra`). -/
theorem isIntegralClosure_baseChange (hO : (algebraMap O O').Etale) [IsIntegralClosure B T L] :
    @IsIntegralClosure (O' ⊗[O] B) (O' ⊗[O] T) (O' ⊗[O] L) _ _ _ (baseChangeAlgebra O O' T L)
      (baseChangeAlgebra O O' B L) := by
  haveI : Algebra.Etale T (O' ⊗[O] T) :=
    RingHom.etale_algebraMap.mp (etale_includeRight_base hO T)
  letI := (tensorIntegralClosureMap T (O' ⊗[O] T) L B).toRingHom.toAlgebra
  have h : IsIntegralClosure ((O' ⊗[O] T) ⊗[T] B) (O' ⊗[O] T) ((O' ⊗[O] T) ⊗[T] L) :=
    isIntegralClosure_tensorProduct
  letI := baseChangeAlgebra O O' T L
  letI := baseChangeAlgebra O O' B L
  refine IsIntegralClosure.of_ringEquiv (RingEquiv.refl _)
    (Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) B).toRingEquiv
    (Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) L).toRingEquiv
    (fun a ↦ ?_) (fun b ↦ ?_)
  · refine Eq.trans ?_ (AlgEquiv.apply_symm_apply
      (Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) L) (baseChangeMap O O' T L a))
    rw [cancelBaseChangeAlg_symm_baseChangeMap]
    rfl
  · refine Eq.trans ?_ (cancelBaseChangeAlg_tensorIntegralClosureMap O O' T L B
      (Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) B b))
    rw [AlgEquiv.symm_apply_apply]
    rfl

/-- **Normalisation commutes with étale base change**, with the base `O' ⊗_O T` replaced by an
isomorphic `O'`-algebra `T'` (structure map `baseChangeAlgebraOfEquiv`). -/
theorem isIntegralClosure_baseChange_of_equiv (hO : (algebraMap O O').Etale)
    [IsIntegralClosure B T L] {T' : Type*} [CommRing T'] [Algebra O' T']
    (e : O' ⊗[O] T ≃ₐ[O'] T') :
    @IsIntegralClosure (O' ⊗[O] B) T' (O' ⊗[O] L) _ _ _ (baseChangeAlgebraOfEquiv O O' e L)
      (baseChangeAlgebra O O' B L) := by
  letI := baseChangeAlgebra O O' T L
  letI := baseChangeAlgebra O O' B L
  have h : IsIntegralClosure (O' ⊗[O] B) (O' ⊗[O] T) (O' ⊗[O] L) :=
    isIntegralClosure_baseChange O O' T L B hO
  letI := baseChangeAlgebraOfEquiv O O' e L
  exact IsIntegralClosure.of_ringEquiv_base e.toRingEquiv fun a ↦
    congrArg (baseChangeMap O O' T L) (e.symm_apply_apply a)

end BaseChange

namespace TateTwoChart

variable {O : Type u} [CommRing O] (π b₄ t κ : O) (O' : Type u) [CommRing O'] [Algebra O O']
  (L : Type*) [CommRing L] [Algebra O L] (B : Type*) [CommRing B] [Algebra O B] [Algebra B L]
  [IsScalarTower O B L]

/-- **Normalisation commutes with étale base change at the chart `T0`**: if `B` is the integral
closure of `T0` in `L`, then `O' ⊗_O B` is the integral closure of `T0'` (the chart with the
images of `π, b₄, t, κ` in `O'`) in `O' ⊗_O L`, `T0'` acting through `baseChangeT0`. -/
theorem isIntegralClosure_baseChangeT0 (hO : (algebraMap O O').Etale) [Algebra (T0 π b₄ t κ) L]
    [Algebra (T0 π b₄ t κ) B] [IsScalarTower O (T0 π b₄ t κ) L]
    [IsScalarTower O (T0 π b₄ t κ) B] [IsScalarTower (T0 π b₄ t κ) B L]
    [IsIntegralClosure B (T0 π b₄ t κ) L] :
    @IsIntegralClosure (O' ⊗[O] B)
      (T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ))
      (O' ⊗[O] L) _ _ _ (baseChangeAlgebraOfEquiv O O' (baseChangeT0 π b₄ t κ O') L)
      (baseChangeAlgebra O O' B L) :=
  isIntegralClosure_baseChange_of_equiv O O' _ L B hO _

/-- **Normalisation commutes with étale base change at the chart `T1`**: if `B` is the integral
closure of `T1` in `L`, then `O' ⊗_O B` is the integral closure of `T1'` (the chart with the
images of `π, b₄, t, κ` in `O'`) in `O' ⊗_O L`, `T1'` acting through `baseChangeT1`. -/
theorem isIntegralClosure_baseChangeT1 (hO : (algebraMap O O').Etale) [Algebra (T1 π b₄ t κ) L]
    [Algebra (T1 π b₄ t κ) B] [IsScalarTower O (T1 π b₄ t κ) L]
    [IsScalarTower O (T1 π b₄ t κ) B] [IsScalarTower (T1 π b₄ t κ) B L]
    [IsIntegralClosure B (T1 π b₄ t κ) L] :
    @IsIntegralClosure (O' ⊗[O] B)
      (T1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ))
      (O' ⊗[O] L) _ _ _ (baseChangeAlgebraOfEquiv O O' (baseChangeT1 π b₄ t κ O') L)
      (baseChangeAlgebra O O' B L) :=
  isIntegralClosure_baseChange_of_equiv O O' _ L B hO _

end TateTwoChart

end

end SemistableReduction
