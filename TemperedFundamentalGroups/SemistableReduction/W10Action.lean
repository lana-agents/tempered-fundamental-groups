/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Fields
import TemperedFundamentalGroups.SemistableReduction.GaussDescent

/-!
# Semilinear actions on the function fields of a cover

Blueprint §9.7a (W10 assembly). In the setting of `W10Fields`, a group `H` acting on the constants
`M` over `K` (`α : H →* (M ≃ₐ[K] M)`) and on the cover `A` over `K[X]` (`β : H →* (A ≃ₐ[K[X]] A)`,
e.g. `G × Gal(M/K)`) acts on `BX = M ⊗_K A` (`bxEquiv`), on its localization `LX` (`lxEquiv`,
semilinear over `ratFuncMap (α h)`: `lxEquiv_algebraMap_ratFunc`) and on the product of the
components (`piEquiv`, `piEquiv_algebraMap`).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace W10Fields

attribute [local instance] polyAlgebra

variable {K : Type u} [Field K] {M : Type u} [Field M] [Algebra K M]
  {A : Type u} [CommRing A] [Algebra K[X] A]

/-- The coefficientwise action of `τ` on `M[X]`, as a `K[X]`-algebra automorphism. -/
noncomputable def polyEquiv (τ : M ≃ₐ[K] M) : M[X] ≃ₐ[K[X]] M[X] :=
  { Polynomial.mapAlgEquiv τ with
    commutes' := fun q ↦ by
      change (q.map (algebraMap K M)).map (τ : M →+* M) = q.map (algebraMap K M)
      rw [Polynomial.map_map]
      congr 1
      ext k
      exact τ.commutes k }

lemma polyEquiv_apply (τ : M ≃ₐ[K] M) (p : M[X]) : polyEquiv τ p = p.map (τ : M →+* M) := rfl

lemma polyEquiv_mul (τ₁ τ₂ : M ≃ₐ[K] M) (p : M[X]) :
    polyEquiv (τ₁ * τ₂) p = polyEquiv τ₁ (polyEquiv τ₂ p) := by
  simp only [polyEquiv_apply, Polynomial.map_map]
  rfl

variable (K M A)

/-- The action of `(τ, g)` on `M ⊗_K A`. -/
noncomputable def bxEquiv (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) : BX K M A ≃+* BX K M A :=
  (Algebra.TensorProduct.congr (polyEquiv τ) g).toRingEquiv

variable {K M A}

lemma bxEquiv_tmul (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) (p : M[X]) (a : A) :
    bxEquiv K M A τ g (p ⊗ₜ a : M[X] ⊗[K[X]] A) = (polyEquiv τ p ⊗ₜ g a : M[X] ⊗[K[X]] A) :=
  rfl

lemma bxEquiv_algebraMap (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) (p : M[X]) :
    bxEquiv K M A τ g (algebraMap M[X] (BX K M A) p) =
      algebraMap M[X] (BX K M A) (p.map (τ : M →+* M)) := by
  change bxEquiv K M A τ g (p ⊗ₜ 1 : M[X] ⊗[K[X]] A) = (p.map (τ : M →+* M) ⊗ₜ 1 : M[X] ⊗[K[X]] A)
  rw [bxEquiv_tmul, map_one]
  rfl

lemma bxEquiv_ofA (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) (a : A) :
    bxEquiv K M A τ g (BX.ofA K M A a) = BX.ofA K M A (g a) := by
  change bxEquiv K M A τ g (1 ⊗ₜ a : M[X] ⊗[K[X]] A) = (1 ⊗ₜ g a : M[X] ⊗[K[X]] A)
  rw [bxEquiv_tmul, map_one]

lemma bxEquiv_mul (τ₁ τ₂ : M ≃ₐ[K] M) (g₁ g₂ : A ≃ₐ[K[X]] A) (b : BX K M A) :
    bxEquiv K M A (τ₁ * τ₂) (g₁ * g₂) b = bxEquiv K M A τ₁ g₁ (bxEquiv K M A τ₂ g₂ b) := by
  have hp : polyEquiv (τ₁ * τ₂) = (polyEquiv τ₂).trans (polyEquiv τ₁) :=
    AlgEquiv.ext fun p ↦ polyEquiv_mul τ₁ τ₂ p
  have hg : g₁ * g₂ = g₂.trans g₁ := rfl
  change Algebra.TensorProduct.congr (polyEquiv (τ₁ * τ₂)) (g₁ * g₂) b = _
  rw [hp, hg, Algebra.TensorProduct.congr_trans]
  rfl

lemma bxEquiv_one (b : BX K M A) : bxEquiv K M A 1 1 b = b := by
  have hp : polyEquiv (1 : M ≃ₐ[K] M) = AlgEquiv.refl :=
    AlgEquiv.ext fun p ↦ by rw [polyEquiv_apply]; exact Polynomial.map_id
  change Algebra.TensorProduct.congr (polyEquiv (1 : M ≃ₐ[K] M)) (1 : A ≃ₐ[K[X]] A) b = b
  rw [hp]
  change Algebra.TensorProduct.congr AlgEquiv.refl AlgEquiv.refl b = b
  rw [Algebra.TensorProduct.congr_refl]
  rfl

lemma map_algebraMapSubmonoid (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) :
    (Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X])).map
        (bxEquiv K M A τ g).toMonoidHom =
      Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X]) := by
  have hnz : ∀ (σ : M ≃ₐ[K] M) (q : M[X]), q ∈ nonZeroDivisors M[X] →
      q.map (σ : M →+* M) ∈ nonZeroDivisors M[X] := fun σ q hq ↦
    mem_nonZeroDivisors_of_ne_zero
      ((Polynomial.map_ne_zero_iff (σ : M →+* M).injective).2 (nonZeroDivisors.ne_zero hq))
  ext y
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.map (τ : M →+* M), hnz τ q hq, (bxEquiv_algebraMap τ g q).symm⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨algebraMap M[X] (BX K M A) (q.map (τ.symm : M →+* M)),
      ⟨_, hnz τ.symm q hq, rfl⟩, ?_⟩
    change bxEquiv K M A τ g _ = _
    rw [bxEquiv_algebraMap, Polynomial.map_map]
    congr 2
    convert Polynomial.map_id (R := M)
    ext m
    exact τ.apply_symm_apply m

variable (K M A) in
/-- The action of `(τ, g)` on `LX`. -/
noncomputable def lxEquiv (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) : LX K M A ≃+* LX K M A :=
  IsLocalization.ringEquivOfRingEquiv (LX K M A) (LX K M A) (bxEquiv K M A τ g)
    (map_algebraMapSubmonoid τ g)

lemma lxEquiv_algebraMap (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) (b : BX K M A) :
    lxEquiv K M A τ g (algebraMap (BX K M A) (LX K M A) b) =
      algebraMap (BX K M A) (LX K M A) (bxEquiv K M A τ g b) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ b

lemma lxEquiv_mul (τ₁ τ₂ : M ≃ₐ[K] M) (g₁ g₂ : A ≃ₐ[K[X]] A) (y : LX K M A) :
    lxEquiv K M A (τ₁ * τ₂) (g₁ * g₂) y = lxEquiv K M A τ₁ g₁ (lxEquiv K M A τ₂ g₂ y) := by
  have : (lxEquiv K M A (τ₁ * τ₂) (g₁ * g₂) : LX K M A →+* LX K M A) =
      (lxEquiv K M A τ₁ g₁ : LX K M A →+* LX K M A).comp (lxEquiv K M A τ₂ g₂) := by
    refine IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X])) (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, lxEquiv_algebraMap, bxEquiv_mul]
  exact congrFun (congrArg DFunLike.coe this) y

lemma lxEquiv_one (y : LX K M A) : lxEquiv K M A 1 1 y = y := by
  have : (lxEquiv K M A 1 1 : LX K M A →+* LX K M A) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X])) (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, lxEquiv_algebraMap, bxEquiv_one,
      RingHom.id_apply]
  exact congrFun (congrArg DFunLike.coe this) y

/-- **Semilinearity**: `lxEquiv (τ, g)` acts on `M(X)` by `ratFuncMap τ`. -/
theorem lxEquiv_algebraMap_ratFunc (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) (φ : RatFunc M) :
    lxEquiv K M A τ g (algebraMap (RatFunc M) (LX K M A) φ) =
      algebraMap (RatFunc M) (LX K M A) (ratFuncMap (τ : M →+* M) φ) := by
  have : (lxEquiv K M A τ g : LX K M A →+* LX K M A).comp (algebraMap (RatFunc M) (LX K M A)) =
      (algebraMap (RatFunc M) (LX K M A)).comp (ratFuncMap (τ : M →+* M)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors M[X]) (RingHom.ext fun q ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [ratFuncMap_algebraMap, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply M[X] (BX K M A),
      IsScalarTower.algebraMap_apply M[X] (BX K M A) (LX K M A), lxEquiv_algebraMap,
      bxEquiv_algebraMap]
  exact congrFun (congrArg DFunLike.coe this) φ

section BaseChange

variable {M' : Type u} [Field M'] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M']

/-- The change of constants `LX K M A → LX K M' A` is semilinear over `ratFuncMap`. -/
theorem lxMap_algebraMap_ratFunc (φ : RatFunc M) :
    lxMap K M A M' (algebraMap (RatFunc M) (LX K M A) φ) =
      algebraMap (RatFunc M') (LX K M' A) (ratFuncMap (algebraMap M M') φ) := by
  have : (lxMap K M A M').comp (algebraMap (RatFunc M) (LX K M A)) =
      (algebraMap (RatFunc M') (LX K M' A)).comp (ratFuncMap (algebraMap M M')) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors M[X]) (RingHom.ext fun q ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [ratFuncMap_algebraMap, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply M[X] (BX K M A),
      IsScalarTower.algebraMap_apply M'[X] (BX K M' A) (LX K M' A), lxMap_algebraMap,
      bxMap_algebraMap]
  exact congrFun (congrArg DFunLike.coe this) φ

/-- `LB K A → LX K M A` is semilinear over `ratFuncMap`. -/
theorem lbMap_algebraMap_ratFunc (φ : RatFunc K) :
    lbMap K M A (algebraMap (RatFunc K) (LB K A) φ) =
      algebraMap (RatFunc M) (LX K M A) (ratFuncMap (algebraMap K M) φ) := by
  have : (lbMap K M A).comp (algebraMap (RatFunc K) (LB K A)) =
      (algebraMap (RatFunc M) (LX K M A)).comp (ratFuncMap (algebraMap K M)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun q ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [ratFuncMap_algebraMap, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K[X] A (LB K A),
      IsScalarTower.algebraMap_apply M[X] (BX K M A) (LX K M A), lbMap_algebraMap,
      ofA_algebraMap]
  exact congrFun (congrArg DFunLike.coe this) φ

/-- The action is semilinear on the constants `M ⊆ LX`. -/
theorem lxEquiv_algebraMap_const (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) (m : M) :
    lxEquiv K M A τ g (algebraMap M (LX K M A) m) = algebraMap M (LX K M A) (τ m) := by
  rw [IsScalarTower.algebraMap_apply M (RatFunc M) (LX K M A), lxEquiv_algebraMap_ratFunc,
    IsScalarTower.algebraMap_apply M (RatFunc M) (LX K M A)]
  congr 1
  exact ratFuncMap_algebraMap_C _ m

end BaseChange

section Group

variable (K M A) {H : Type*} [Group H] (α : H →* (M ≃ₐ[K] M)) (β : H →* (A ≃ₐ[K[X]] A))

/-- The action of `H` on `LX`. -/
noncomputable def lxAct : H →* (LX K M A ≃+* LX K M A) where
  toFun h := lxEquiv K M A (α h) (β h)
  map_one' := RingEquiv.ext fun y ↦ by rw [map_one, map_one]; exact lxEquiv_one y
  map_mul' h₁ h₂ := RingEquiv.ext fun y ↦ by rw [map_mul, map_mul, lxEquiv_mul]; rfl

variable [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A] [IsReduced (BX K M A)]

/-- The action of `H` on the product of the components. -/
noncomputable def piAct :
    H →* ((∀ 𝔪 : MaximalSpectrum (LX K M A), Comp K M A 𝔪) ≃+*
      (∀ 𝔪 : MaximalSpectrum (LX K M A), Comp K M A 𝔪)) where
  toFun h := (equivPi K M A).toRingEquiv.symm.trans
    ((lxAct K M A α β h).trans (equivPi K M A).toRingEquiv)
  map_one' := RingEquiv.ext fun y ↦ by
    change equivPi K M A (lxAct K M A α β 1 ((equivPi K M A).symm y)) = y
    rw [map_one]
    exact (equivPi K M A).apply_symm_apply y
  map_mul' h₁ h₂ := RingEquiv.ext fun y ↦ by
    change equivPi K M A (lxAct K M A α β (h₁ * h₂) ((equivPi K M A).symm y)) =
      equivPi K M A (lxAct K M A α β h₁ ((equivPi K M A).symm
        (equivPi K M A (lxAct K M A α β h₂ ((equivPi K M A).symm y)))))
    rw [AlgEquiv.symm_apply_apply, map_mul]
    rfl

variable {K M A}

lemma piAct_equivPi (h : H) (y : LX K M A) :
    piAct K M A α β h (equivPi K M A y) = equivPi K M A (lxAct K M A α β h y) := by
  change equivPi K M A (lxAct K M A α β h ((equivPi K M A).symm (equivPi K M A y))) = _
  rw [AlgEquiv.symm_apply_apply]

/-- **Semilinearity of the action on the components.** -/
theorem piAct_algebraMap (h : H) (φ : RatFunc M) :
    piAct K M A α β h (fun 𝔪 ↦ algebraMap (RatFunc M) (Comp K M A 𝔪) φ) =
      fun 𝔪 ↦ algebraMap (RatFunc M) (Comp K M A 𝔪)
        (ratFuncMap ((α h : M ≃ₐ[K] M) : M →+* M) φ) := by
  have key : ∀ ψ : RatFunc M, (fun 𝔪 ↦ algebraMap (RatFunc M) (Comp K M A 𝔪) ψ) =
      equivPi K M A (algebraMap (RatFunc M) (LX K M A) ψ) := fun ψ ↦ by
    ext 𝔪
    rw [equivPi_apply]
    rfl
  rw [key, key, piAct_equivPi]
  congr 1
  exact lxEquiv_algebraMap_ratFunc (α h) (β h) φ

end Group

section Permutation

/-- The maximal ideal `σ⁻¹ 𝔫`. -/
noncomputable def comapMax (σ : LX K M A ≃+* LX K M A) (𝔫 : MaximalSpectrum (LX K M A)) :
    MaximalSpectrum (LX K M A) :=
  ⟨𝔫.asIdeal.comap (σ : LX K M A →+* LX K M A),
    Ideal.comap_isMaximal_of_surjective _ σ.surjective⟩

/-- The isomorphism of components `LX ⧸ σ⁻¹ 𝔫 ≃ LX ⧸ 𝔫` induced by `σ`. -/
noncomputable def compEquiv (σ : LX K M A ≃+* LX K M A) (𝔫 : MaximalSpectrum (LX K M A)) :
    Comp K M A (comapMax σ 𝔫) ≃+* Comp K M A 𝔫 :=
  Ideal.quotientEquiv _ _ σ (Ideal.map_comap_of_surjective _ σ.surjective _).symm

lemma compEquiv_mk (σ : LX K M A ≃+* LX K M A) (𝔫 : MaximalSpectrum (LX K M A)) (y : LX K M A) :
    compEquiv σ 𝔫 (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk 𝔫.asIdeal (σ y) :=
  rfl

variable [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A] [IsReduced (BX K M A)]

lemma equivPi_apply_equiv (σ : LX K M A ≃+* LX K M A) (y : LX K M A)
    (𝔫 : MaximalSpectrum (LX K M A)) :
    equivPi K M A (σ y) 𝔫 = compEquiv σ 𝔫 (equivPi K M A y (comapMax σ 𝔫)) := by
  rw [equivPi_apply, equivPi_apply, compEquiv_mk]

variable {H : Type*} [Group H] (α : H →* (M ≃ₐ[K] M)) (β : H →* (A ≃ₐ[K[X]] A))

/-- **The action on the components is componentwise**: `piAct h` maps the component
`(lxAct h)⁻¹ 𝔫` to `𝔫` by `compEquiv`. -/
theorem piAct_apply (h : H) (z : ∀ 𝔪 : MaximalSpectrum (LX K M A), Comp K M A 𝔪)
    (𝔫 : MaximalSpectrum (LX K M A)) :
    piAct K M A α β h z 𝔫 =
      compEquiv (lxAct K M A α β h) 𝔫 (z (comapMax (lxAct K M A α β h) 𝔫)) := by
  obtain ⟨y, rfl⟩ := (equivPi K M A).surjective z
  rw [piAct_equivPi, equivPi_apply_equiv]

end Permutation

end W10Fields

end SemistableReduction
