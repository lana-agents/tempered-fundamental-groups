/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerBaseChangeRes

/-!
# Transport of residue-trivial Kummer data along an isomorphism of the base

For an `O`-algebra isomorphism `eN : N ≃ₐ[O] N''` and an `N`-algebra `B` (an `N''`-algebra through
`eN⁻¹`), `IsKummerNormAtRes` / `Cusp.IsCuspNormAtRes` of `B` at `𝔪 ⊆ N` give the same at
`eN(𝔪)` with coordinates `eN u, eN v` (resp. `eN t`) (`IsKummerNormAtRes.of_baseEquiv`,
`Cusp.IsCuspNormAtRes.of_baseEquiv`). Used to pass from `O' ⊗_O NR` (where
`isKummerNormAtRes_baseChange` lands) to the node chart `NR'` over `O'` (`baseChangeNR`), and
from `O' ⊗_O Rc` to `Rc'` (`baseChangeRc`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace KummerBaseChange

noncomputable section

variable {O N N'' : Type u} [CommRing O] [CommRing N] [CommRing N''] [Algebra O N] [Algebra O N'']
  (eN : N ≃ₐ[O] N'') {B : Type u} [CommRing B] [Algebra N B]

/-- `B ≃ N'' ⊗_N B` as `N''`-algebras (`B` an `N''`-algebra through `eN⁻¹`). -/
def baseEquivAux :
    letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
    letI : Algebra N N'' := eN.toRingHom.toAlgebra
    B ≃ₐ[N''] N'' ⊗[N] B :=
  letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
  letI : Algebra N N'' := eN.toRingHom.toAlgebra
  let e' : N'' ≃ₐ[N] N := AlgEquiv.ofRingEquiv (f := eN.symm.toRingEquiv) fun x ↦
    eN.symm_apply_apply x
  let G : N'' ⊗[N] B ≃ₐ[N] B :=
    (Algebra.TensorProduct.congr e' AlgEquiv.refl).trans (Algebra.TensorProduct.lid N B)
  AlgEquiv.ofRingEquiv (f := G.symm.toRingEquiv) fun x ↦ by
    change G.symm (algebraMap N B (eN.symm x)) = x ⊗ₜ 1
    rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra]
    change eN (eN.symm x) ⊗ₜ[N] (1 : B) = x ⊗ₜ 1
    rw [AlgEquiv.apply_symm_apply]

/-- `N₁ ⊗_{N''} B ≃ N₁ ⊗_N B` (`N₁` an `N`-algebra, an `N''`-algebra through `eN⁻¹`). -/
def baseEquivTensor (N₁ : Type u) [CommRing N₁] [Algebra N N₁] :
    letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
    letI : Algebra N'' N₁ := ((algebraMap N N₁).comp eN.symm.toRingHom).toAlgebra
    N₁ ⊗[N''] B ≃ₐ[N₁] N₁ ⊗[N] B :=
  letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
  letI : Algebra N'' N₁ := ((algebraMap N N₁).comp eN.symm.toRingHom).toAlgebra
  letI : Algebra N N'' := eN.toRingHom.toAlgebra
  haveI : IsScalarTower N N'' N₁ := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = algebraMap N N₁ (eN.symm (eN x))
    rw [AlgEquiv.symm_apply_apply]
  (Algebra.TensorProduct.congr AlgEquiv.refl (baseEquivAux eN)).trans
    (Algebra.TensorProduct.cancelBaseChange N N'' N₁ N₁ B)

/-- **Transport of `IsKummerNormAtRes` along an isomorphism of the base.** -/
theorem isKummerNormAtRes_of_baseEquiv {ϖ : O} {n M' : ℕ} {u v : N} {𝔪 : Ideal N}
    (h : IsKummerNormAtRes ϖ n M' u v B 𝔪) :
    letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
    IsKummerNormAtRes ϖ n M' (eN u) (eN v) B (𝔪.comap eN.symm.toRingHom) := by
  letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
  obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, hs, hd⟩ := h
  letI A'' : Algebra N'' N₁ := ((algebraMap N N₁).comp eN.symm.toRingHom).toAlgebra
  have hA : ∀ x : N, algebraMap N'' N₁ (eN x) = algebraMap N N₁ x := fun x ↦ by
    change algebraMap N N₁ (eN.symm (eN x)) = _
    rw [AlgEquiv.symm_apply_apply]
  haveI : Algebra.Etale N'' N₁ := RingHom.etale_algebraMap.mp
    (RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective eN.symm.bijective) (RingHom.etale_algebraMap.mpr inferInstance))
  refine ⟨N₁, inferInstance, A'', inferInstance, 𝔫, inferInstance, ?_, fun z ↦ ?_, ?_⟩
  · rw [← h𝔫]
    rfl
  · obtain ⟨x, hx⟩ := hs z
    exact ⟨eN x, by rw [RingHom.comp_apply, hA]; exact hx⟩
  · change @KummerNodeSplit O _ ϖ n M' N₁ _
      ((algebraMap N'' N₁).comp (algebraMap O N'')).toAlgebra
      (algebraMap N'' N₁ (eN u)) (algebraMap N'' N₁ (eN v)) 𝔫 (N₁ ⊗[N''] B) _ _
    rw [hA, hA]
    letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
    exact kummerNodeSplit_of_algebra_eq _ _ (fun r ↦ by
      change algebraMap N N₁ (algebraMap O N r) = algebraMap N N₁ (eN.symm (algebraMap O N'' r))
      rw [AlgEquiv.commutes]) (KummerNodeSplit.of_algEquiv (baseEquivTensor eN N₁) hd)

/-- **Transport of `Cusp.IsCuspNormAtRes` along an isomorphism of the base.** -/
theorem isCuspNormAtRes_of_baseEquiv {e : ℕ} {t : N} {𝔪 : Ideal N}
    (h : Cusp.IsCuspNormAtRes O e t B 𝔪) :
    letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
    Cusp.IsCuspNormAtRes O e (eN t) B (𝔪.comap eN.symm.toRingHom) := by
  letI : Algebra N'' B := ((algebraMap N B).comp eN.symm.toRingHom).toAlgebra
  obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, hs, hd⟩ := h
  letI A'' : Algebra N'' N₁ := ((algebraMap N N₁).comp eN.symm.toRingHom).toAlgebra
  have hA : ∀ x : N, algebraMap N'' N₁ (eN x) = algebraMap N N₁ x := fun x ↦ by
    change algebraMap N N₁ (eN.symm (eN x)) = _
    rw [AlgEquiv.symm_apply_apply]
  haveI : Algebra.Etale N'' N₁ := RingHom.etale_algebraMap.mp
    (RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective eN.symm.bijective) (RingHom.etale_algebraMap.mpr inferInstance))
  refine ⟨N₁, inferInstance, A'', inferInstance, 𝔫, inferInstance, ?_, fun z ↦ ?_, ?_⟩
  · rw [← h𝔫]
    rfl
  · obtain ⟨x, hx⟩ := hs z
    exact ⟨eN x, by rw [RingHom.comp_apply, hA]; exact hx⟩
  · change @Cusp.CuspNormSplit O _ e N₁ _
      ((algebraMap N'' N₁).comp (algebraMap O N'')).toAlgebra
      (algebraMap N'' N₁ (eN t)) 𝔫 (N₁ ⊗[N''] B) _ _
    rw [hA]
    letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
    exact cuspNormSplit_of_algebra_eq _ _ (fun r ↦ by
      change algebraMap N N₁ (algebraMap O N r) = algebraMap N N₁ (eN.symm (algebraMap O N'' r))
      rw [AlgEquiv.commutes]) (Cusp.CuspNormSplit.of_algEquiv (baseEquivTensor eN N₁) hd)

end

end KummerBaseChange

end SemistableReduction
