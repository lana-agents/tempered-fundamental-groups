/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateTwoChart

/-!
# The charts of the Tate model commute with base change (MR12 S5.7)

For an `O`-algebra `O'` (e.g. a finite unramified extension of complete DVRs, for the base change
of S5.7 which trivialises the residue extensions):

* **`TateTwoChart.adjoinRootBaseChange`**: `O' ⊗_O O[X][Y]/(p) ≃ₐ[O'] O'[X][Y]/(p')`, `p'` the
  image of `p` (`AdjoinRoot.tensorAlgEquiv` and `polyEquivTensor'`), with `root` and `of`;
* **`TateTwoChart.baseChangeT0`**, **`TateTwoChart.baseChangeT1`**: `O' ⊗_O T0 ≃ₐ[O'] T0'`,
  `O' ⊗_O T1 ≃ₐ[O'] T1'`, the charts with the images of the parameters `π, b₄, t, κ` in `O'`
  (`map_G0_baseChange`, `map_G1_baseChange`), and **`TateTwoChart.baseChangeT01`** for the overlap
  `T01 = T1[1/h']` (`IsLocalization.Away.tensorProductEquivTMulRight`).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace TateTwoChart

noncomputable section

/-- **Adjoining a root over `R[X]` commutes with base change**:
`R' ⊗_R R[X][Y]/(p) ≃ R'[X][Y]/(p')`, `p'` the image of `p`. -/
def adjoinRootBaseChange {R : Type*} [CommRing R] (R' : Type*) [CommRing R'] [Algebra R R']
    (p : R[X][X]) :
    R' ⊗[R] AdjoinRoot p ≃ₐ[R'] AdjoinRoot (p.map (mapRingHom (algebraMap R R'))) :=
  (AdjoinRoot.tensorAlgEquiv p (p.map Algebra.TensorProduct.includeRight.toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv (polyEquivTensor' R R').symm _ _ ⟨1, by
      rw [Units.val_one, mul_one, Polynomial.map_map]
      congr 1
      refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_ <;>
        simp [Algebra.algebraMap_eq_smul_one]⟩)

@[simp] lemma adjoinRootBaseChange_root {R : Type*} [CommRing R] (R' : Type*) [CommRing R']
    [Algebra R R'] (p : R[X][X]) :
    adjoinRootBaseChange R' p (1 ⊗ₜ AdjoinRoot.root p) = AdjoinRoot.root _ := by
  rw [adjoinRootBaseChange, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

@[simp] lemma adjoinRootBaseChange_of {R : Type*} [CommRing R] (R' : Type*) [CommRing R']
    [Algebra R R'] (p : R[X][X]) (a : R[X]) :
    adjoinRootBaseChange R' p (1 ⊗ₜ AdjoinRoot.of p a) =
      AdjoinRoot.of _ (a.map (algebraMap R R')) := by
  rw [adjoinRootBaseChange, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  congr 1
  induction a using Polynomial.induction_on' with
  | add p q hp hq => simp [TensorProduct.tmul_add]
  | monomial n r => simp [Algebra.algebraMap_eq_smul_one]

variable {O : Type u} [CommRing O] (π b₄ t κ : O) (O' : Type u) [CommRing O'] [Algebra O O']

lemma map_G0_baseChange : (G0 π b₄ t κ).map (mapRingHom (algebraMap O O')) =
    G0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ) := by
  simp [G0, map_ofNat]

lemma map_G1_baseChange : (G1 π b₄ t κ).map (mapRingHom (algebraMap O O')) =
    G1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ) := by
  simp [G1, map_ofNat]

/-- **The chart `T0` commutes with base change** `O → O'`. -/
def baseChangeT0 : O' ⊗[O] T0 π b₄ t κ ≃ₐ[O']
    T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ) :=
  (adjoinRootBaseChange O' (G0 π b₄ t κ)).trans
    (AdjoinRoot.mapAlgEquiv AlgEquiv.refl _ _
      ⟨1, by rw [Units.val_one, mul_one, ← map_G0_baseChange]; exact Polynomial.map_id⟩)

/-- **The chart `T1` commutes with base change** `O → O'`. -/
def baseChangeT1 : O' ⊗[O] T1 π b₄ t κ ≃ₐ[O']
    T1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ) :=
  (adjoinRootBaseChange O' (G1 π b₄ t κ)).trans
    (AdjoinRoot.mapAlgEquiv AlgEquiv.refl _ _
      ⟨1, by rw [Units.val_one, mul_one, ← map_G1_baseChange]; exact Polynomial.map_id⟩)


@[simp] lemma baseChangeT0_root :
    baseChangeT0 π b₄ t κ O' (1 ⊗ₜ AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [baseChangeT0, AlgEquiv.trans_apply, adjoinRootBaseChange_root, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_root]

@[simp] lemma baseChangeT0_of (a : O[X]) :
    baseChangeT0 π b₄ t κ O' (1 ⊗ₜ AdjoinRoot.of _ a) =
      AdjoinRoot.of _ (a.map (algebraMap O O')) := by
  rw [baseChangeT0, AlgEquiv.trans_apply, adjoinRootBaseChange_of, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_of]
  rfl

@[simp] lemma baseChangeT1_root :
    baseChangeT1 π b₄ t κ O' (1 ⊗ₜ AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [baseChangeT1, AlgEquiv.trans_apply, adjoinRootBaseChange_root, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_root]

@[simp] lemma baseChangeT1_of (a : O[X]) :
    baseChangeT1 π b₄ t κ O' (1 ⊗ₜ AdjoinRoot.of _ a) =
      AdjoinRoot.of _ (a.map (algebraMap O O')) := by
  rw [baseChangeT1, AlgEquiv.trans_apply, adjoinRootBaseChange_of, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_of]
  rfl


/-- **The overlap chart `T01 = T1[1/h']` commutes with base change** `O → O'`. -/
def baseChangeT01 : O' ⊗[O] T01 π b₄ t κ ≃ₐ[O']
    T01 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t) (algebraMap O O' κ) :=
  (IsLocalization.Away.tensorProductEquivTMulRight O O' (h1 π b₄ t κ) (T01 π b₄ t κ)).trans
    (IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers ((1 : O') ⊗ₜ h1 π b₄ t κ))
      (T := Submonoid.powers (h1 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
        (algebraMap O O' κ))) (Localization.Away _) (T01 _ _ _ _) (baseChangeT1 π b₄ t κ O')
      (by rw [Submonoid.map_powers]; congr 1; simp [h1]))

end

end TateTwoChart

end SemistableReduction
