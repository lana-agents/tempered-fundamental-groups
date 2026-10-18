/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel

/-!
# The patching datum `α₀` from an isomorphism modulo `J` (Blueprint §12.8, M2.3 (d'))

The level-`n` patching `FormalPatchLevel.isBaseChange_lift` needs `α₀ : P → N_f/J` whose
`R̂`-linear extension `betaMod α₀ : R̂ ⊗_R P → N_f/J` is surjective with kernel in
`J (R̂ ⊗_R P)`. Both conditions say that `betaMod α₀` induces an isomorphism
`(R̂ ⊗_R P)/J ≅ N_f/J`. Conversely, **any** `R̂`-algebra isomorphism
`Φ : (R̂ ⊗_R P)/J ≃ N_f/J` gives such an `α₀` (`FormalPatchLevel.alphaOfEquiv`,
`p ↦ Φ(1 ⊗ p)`): `betaMod (alphaOfEquiv Φ) = Φ ∘ mk` (`betaMod_alphaOfEquiv`), so
`surjective_betaMod_alphaOfEquiv` and `mem_of_betaMod_alphaOfEquiv_eq_zero` hold.

So the remaining input of the patching is an `R̂`-algebra isomorphism between the two reductions
modulo `J`, which is where the admissible covering of the special fibre enters.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalPatchLevel

noncomputable section

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R)
  {P : Type u} [CommRing P] [Algebra R P]
  {N : Type u} [CommRing N] [Algebra R N] [Algebra (Hat f) N] [IsScalarTower R (Hat f) N]

variable (P) in
/-- The ideal `J (R̂ ⊗_R P)`. -/
abbrev JT : Ideal (Hat f ⊗[R] P) := J.map (algebraMap R (Hat f ⊗[R] P))

/-- **The patching datum from an isomorphism modulo `J`**: `p ↦ Φ(1 ⊗ p)`. -/
noncomputable def alphaOfEquiv
    (Φ : ((Hat f ⊗[R] P) ⧸ JT f J P) ≃ₐ[Hat f] (Nf f N ⧸ JNf f J N)) :
    P →ₐ[R] Nf f N ⧸ JNf f J N :=
  ((Φ.toAlgHom.restrictScalars R).comp (Ideal.Quotient.mkₐ R (JT f J P))).comp
    Algebra.TensorProduct.includeRight

variable {f J}

lemma betaMod_alphaOfEquiv
    (Φ : ((Hat f ⊗[R] P) ⧸ JT f J P) ≃ₐ[Hat f] (Nf f N ⧸ JNf f J N)) (x : Hat f ⊗[R] P) :
    betaMod f J (alphaOfEquiv f J Φ) x = Φ (Ideal.Quotient.mk _ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s p =>
    rw [betaMod, LinearMap.liftBaseChange_tmul, AlgHom.toLinearMap_apply]
    simp only [alphaOfEquiv, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Ideal.Quotient.mkₐ_eq_mk, AlgHom.restrictScalars_apply]
    rw [← map_smul, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

lemma surjective_betaMod_alphaOfEquiv
    (Φ : ((Hat f ⊗[R] P) ⧸ JT f J P) ≃ₐ[Hat f] (Nf f N ⧸ JNf f J N)) :
    Function.Surjective (betaMod f J (alphaOfEquiv f J Φ)) := fun y ↦ by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Φ.symm y)
  exact ⟨x, by rw [betaMod_alphaOfEquiv, hx, AlgEquiv.apply_symm_apply]⟩

lemma mem_of_betaMod_alphaOfEquiv_eq_zero
    (Φ : ((Hat f ⊗[R] P) ⧸ JT f J P) ≃ₐ[Hat f] (Nf f N ⧸ JNf f J N)) (x : Hat f ⊗[R] P)
    (hx : betaMod f J (alphaOfEquiv f J Φ) x = 0) :
    x ∈ (J.map (algebraMap R (Hat f))) • (⊤ : Submodule (Hat f) (Hat f ⊗[R] P)) := by
  rw [betaMod_alphaOfEquiv, map_eq_zero_iff _ Φ.injective, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
  exact hx

end

end FormalPatchLevel

end SemistableReduction
