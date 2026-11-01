/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateTwoChartNode
import TemperedFundamentalGroups.SemistableReduction.SmoothBaseChange

/-!
# The node chart of the Tate model commutes with base change (MR12 S5.7)

For an `O`-algebra `O'` (e.g. a finite unramified extension, where the parameters of the node
chart just map to `O'`):

* **`TateTwoChartNode.nodeCongr`**: `O[u,v]/(uv − a) ≃ O[u,v]/(uv − b)` for `a = b`;
* **`TateTwoChartNode.baseChangeA`**: `O' ⊗_O O[u,v]/(uv − ϖᵐ) ≃ₐ[O'] O'[u,v]/(uv − ϖ'ᵐ)`
  (`Node.tensorEquiv`), sending `cN`, `DN` to `cN'`, `DN'`;
* **`TateTwoChartNode.baseChangeQ`**: the quadratic cover `A[S]/(S² + S − c)` commutes with base
  change (`AdjoinRoot.tensorAlgEquiv`);
* **`TateTwoChartNode.baseChangeNR`**: **the node chart `NR = Q[1/D]` commutes with base change**,
  `O' ⊗_O NR b₄ b₆ ϖ m ε ≃ₐ[O'] NR b₄' b₆' ϖ' m ε'`
  (`IsLocalization.Away.tensorProductEquivTMulRight`).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace TateTwoChartNode

open KummerEtale

noncomputable section

variable {O : Type u} [CommRing O]

/-- `O[u,v]/(uv − a) ≃ O[u,v]/(uv − b)` for `a = b`. -/
def nodeCongr {a b : O} (h : a = b) : Node O a ≃ₐ[O] Node O b :=
  Ideal.quotientEquivAlgOfEq O (by rw [h])

@[simp] lemma nodeCongr_u {a b : O} (h : a = b) : nodeCongr h (Node.u a) = Node.u b := rfl

@[simp] lemma nodeCongr_v {a b : O} (h : a = b) : nodeCongr h (Node.v a) = Node.v b := rfl

variable (b₄ b₆ ϖ : O) (m : ℕ) (ε : O) (O' : Type u) [CommRing O'] [Algebra O O']

/-- **The node ring commutes with base change**: `O' ⊗_O A ϖ m ≃ₐ[O'] A ϖ' m`. -/
def baseChangeA : O' ⊗[O] A ϖ m ≃ₐ[O'] A (algebraMap O O' ϖ) m :=
  (Node.tensorEquiv (O' := O') (ϖ ^ m)).trans (nodeCongr (map_pow _ ϖ m))

/-- `A ϖ m → A ϖ' m`. -/
abbrev mapA : A ϖ m →ₐ[O] A (algebraMap O O' ϖ) m :=
  ((nodeCongr (map_pow (algebraMap O O') ϖ m)).toAlgHom.restrictScalars O).comp
    (Node.baseAlg (O' := O') (ϖ ^ m))

lemma baseChangeA_tmul (z : A ϖ m) : baseChangeA ϖ m O' (1 ⊗ₜ z) = mapA ϖ m O' z := by
  rw [baseChangeA, AlgEquiv.trans_apply, Node.tensorEquiv_tmul]
  rfl

lemma mapA_u : mapA ϖ m O' (Node.u _) = Node.u _ := by
  simp [mapA, Node.baseAlg]

lemma mapA_v : mapA ϖ m O' (Node.v _) = Node.v _ := by
  simp [mapA, Node.baseAlg]

lemma mapA_algebraMap (o : O) :
    mapA ϖ m O' (algebraMap O _ o) = algebraMap O' _ (algebraMap O O' o) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (A (algebraMap O O' ϖ) m)]

lemma mapA_cN : mapA ϖ m O' (cN b₄ b₆ ϖ m ε) =
    cN (algebraMap O O' b₄) (algebraMap O O' b₆) (algebraMap O O' ϖ) m (algebraMap O O' ε) := by
  simp only [cN, map_add, map_mul, map_pow, map_one, mapA_algebraMap, mapA_u, mapA_v]

lemma mapA_DN : mapA ϖ m O' (DN b₄ ϖ m) = DN (algebraMap O O' b₄) (algebraMap O O' ϖ) m := by
  simp only [DN, map_add, map_mul, map_pow, map_one, mapA_algebraMap, mapA_u]

/-- **The quadratic cover of the node ring commutes with base change**. -/
def baseChangeQ : O' ⊗[O] QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε) ≃ₐ[O']
    QuadNode.Q (algebraMap O O' ϖ) m
      (cN (algebraMap O O' b₄) (algebraMap O O' b₆) (algebraMap O O' ϖ) m (algebraMap O O' ε)) :=
  (AdjoinRoot.tensorAlgEquiv (T := O') (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) _ rfl).trans
    (AdjoinRoot.mapAlgEquiv (baseChangeA ϖ m O') _ _ ⟨1, by
      rw [Units.val_one, mul_one, Polynomial.map_map]
      simp only [QuadraticEtale.poly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
      congr 2
      change baseChangeA ϖ m O' (1 ⊗ₜ cN b₄ b₆ ϖ m ε) = _
      rw [baseChangeA_tmul, mapA_cN]⟩)

lemma baseChangeQ_of (z : A ϖ m) :
    baseChangeQ b₄ b₆ ϖ m ε O' (1 ⊗ₜ AdjoinRoot.of _ z) = AdjoinRoot.of _ (mapA ϖ m O' z) := by
  rw [baseChangeQ, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  exact congrArg _ (baseChangeA_tmul ϖ m O' z)

/-- **The node chart of the Tate model commutes with base change** `O → O'`:
`O' ⊗_O NR b₄ b₆ ϖ m ε ≃ₐ[O'] NR b₄' b₆' ϖ' m ε'`. -/
def baseChangeNR : O' ⊗[O] NR b₄ b₆ ϖ m ε ≃ₐ[O']
    NR (algebraMap O O' b₄) (algebraMap O O' b₆) (algebraMap O O' ϖ) m (algebraMap O O' ε) :=
  (IsLocalization.Away.tensorProductEquivTMulRight O O'
      (AdjoinRoot.of (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) (DN b₄ ϖ m))
      (NR b₄ b₆ ϖ m ε)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers ((1 : O') ⊗ₜ AdjoinRoot.of _ (DN b₄ ϖ m)))
      (T := Submonoid.powers (AdjoinRoot.of _ (DN (algebraMap O O' b₄) (algebraMap O O' ϖ) m)))
      (Localization.Away _) (NR _ _ _ _ _) (baseChangeQ b₄ b₆ ϖ m ε O')
      (by rw [Submonoid.map_powers]; exact congrArg _ ((baseChangeQ_of b₄ b₆ ϖ m ε O' _).trans
        (congrArg _ (mapA_DN b₄ ϖ m O')))))

end

end TateTwoChartNode

end SemistableReduction
