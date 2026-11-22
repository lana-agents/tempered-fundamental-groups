/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerBaseChangeCusp
import TemperedFundamentalGroups.SemistableReduction.IntegralClosureBaseChange
import TemperedFundamentalGroups.SemistableReduction.FormalKummerChart
import TemperedFundamentalGroups.SemistableReduction.FormalCuspNode

/-!
# Étale-local Kummer data over `O' ⊗_O N` (MR12 S5.7 (c), part 2: the ring-level packaging)

For `O → O'`, an `O`-algebra `N` with an `N`-algebra `B`, put `N' = O' ⊗_O N`, `B' = O' ⊗_O B`
(`baseChangeAlgebra`). If `B` is tamely Kummer at `𝔪 ⊆ N` over an étale neighbourhood `N₁ ⊇ 𝔫`
(the data of `IsKummerNormAt` / `Cusp.IsCuspNormAt`), and the residue field of `𝔫` maps to the
residue field `k'` of `O'` (`ι : N₁ → k'` with kernel `𝔫`, compatible with `θ' : O' ↠ k'`), then
`B'` is tamely Kummer over `O'` **with trivial residue field extension** at a point `𝔪'` of `N'`
over `𝔪`:

* `cancelEquiv`, **`etale_baseChange`**: `(O' ⊗_O T) ⊗_T L ≃ O' ⊗_O L` over `O' ⊗_O T`, so étale
  maps `T → L` base change to étale `O' ⊗_O T → O' ⊗_O L` (no hypothesis on `O → O'`);
* `etale_node_baseChange`, `etale_aeval_baseChange`: the node chart `O'[u,v]/(uv − c') → O' ⊗ N₁`
  and the cusp chart `O'[X] → O' ⊗ N₁` stay étale;
* `tensorBaseChangeEquiv`: `N₁' ⊗_{N'} B' ≅ N₁' ⊗_{N₁} (N₁ ⊗_N B)` for `N₁' = O' ⊗_O N₁`;
* **`isKummerNormAtRes_baseChange`**, **`isCuspNormAtRes_baseChange`**: `IsKummerNormAtRes` /
  `Cusp.IsCuspNormAtRes` of `B'` over `O'` at `𝔪' = (resPrime θ' ι).comap` lying over `𝔪`
  (from `kummerNodeSplit_baseChange` / `cuspNormSplit_baseChange` with `ψ = includeRight`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace KummerBaseChange

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Etale

variable (O O' : Type u) [CommRing O] [CommRing O'] [Algebra O O']

/-- `(O' ⊗_O T) ⊗_T L ≃ O' ⊗_O L` as `O' ⊗_O T`-algebras (`O' ⊗_O L` through
`baseChangeAlgebra`). -/
def cancelEquiv (T L : Type u) [CommRing T] [CommRing L] [Algebra O T] [Algebra O L]
    [Algebra T L] [IsScalarTower O T L] :
    letI := baseChangeAlgebra O O' T L
    (O' ⊗[O] T) ⊗[T] L ≃ₐ[O' ⊗[O] T] O' ⊗[O] L :=
  letI := baseChangeAlgebra O O' T L
  AlgEquiv.ofRingEquiv
    (f := (Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) L).toRingEquiv)
    fun x ↦ by
      apply (Algebra.IsPushout.cancelBaseChangeAlg O O' T (O' ⊗[O] T) L).symm.injective
      refine Eq.trans ?_ (cancelBaseChangeAlg_symm_baseChangeMap O O' T L x).symm
      exact AlgEquiv.symm_apply_apply _ _

/-- **Étale maps base change along `O → O'`**: if `T → L` is étale, so is
`O' ⊗_O T → O' ⊗_O L`. -/
theorem etale_baseChange (T L : Type u) [CommRing T] [CommRing L] [Algebra O T] [Algebra O L]
    [Algebra T L] [IsScalarTower O T L] [Algebra.Etale T L] :
    letI := baseChangeAlgebra O O' T L
    Algebra.Etale (O' ⊗[O] T) (O' ⊗[O] L) :=
  letI := baseChangeAlgebra O O' T L
  Algebra.Etale.of_equiv (cancelEquiv O O' T L)

variable {O O'}

lemma tensorEquiv_symm_u (c : O) :
    (Node.tensorEquiv (O' := O') c).symm (Node.u (algebraMap O O' c)) = 1 ⊗ₜ Node.u c := by
  rw [AlgEquiv.symm_apply_eq, Node.tensorEquiv_tmul, baseAlg_u]

lemma tensorEquiv_symm_v (c : O) :
    (Node.tensorEquiv (O' := O') c).symm (Node.v (algebraMap O O' c)) = 1 ⊗ₜ Node.v c := by
  rw [AlgEquiv.symm_apply_eq, Node.tensorEquiv_tmul, baseAlg_v]

/-- **Étale node charts base change**: if `O[u, v]/(uv − c) → N₁`, `u ↦ u₁`, `v ↦ v₁` is étale,
so is `O'[u, v]/(uv − c') → O' ⊗_O N₁` for `c' = c` in `O'`. -/
theorem etale_node_baseChange {N₁ : Type u} [CommRing N₁] [Algebra O N₁] {c : O} {u₁ v₁ : N₁}
    (huv : u₁ * v₁ = algebraMap O N₁ c) (het : (Node.lift u₁ v₁ huv).toRingHom.Etale)
    (c' : O') (hc : algebraMap O O' c = c')
    (huv' : ((1 : O') ⊗ₜ[O] u₁) * ((1 : O') ⊗ₜ[O] v₁) = algebraMap O' (O' ⊗[O] N₁) c') :
    (Node.lift _ _ huv').toRingHom.Etale := by
  subst hc
  letI := (Node.lift u₁ v₁ huv).toRingHom.toAlgebra
  haveI : IsScalarTower O (Node O c) N₁ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((Node.lift u₁ v₁ huv).commutes r).symm
  haveI : Algebra.Etale (Node O c) N₁ := RingHom.etale_algebraMap.mp het
  have hbc := etale_baseChange O O' (Node O c) N₁
  letI := baseChangeAlgebra O O' (Node O c) N₁
  have h : (Node.lift _ _ huv') = (baseChangeMap O O' (Node O c) N₁).comp
      (Node.tensorEquiv (O' := O') c).symm.toAlgHom := by
    apply Node.algHom_ext
    · rw [Node.lift_u, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        tensorEquiv_symm_u, Algebra.TensorProduct.map_tmul]
      simp only [AlgHom.id_apply, IsScalarTower.coe_toAlgHom', RingHom.algebraMap_toAlgebra,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Node.lift_u]
    · rw [Node.lift_v, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        tensorEquiv_symm_v, Algebra.TensorProduct.map_tmul]
      simp only [AlgHom.id_apply, IsScalarTower.coe_toAlgHom', RingHom.algebraMap_toAlgebra,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Node.lift_v]
  rw [h]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (Node.tensorEquiv (O' := O') c).symm.bijective)
    (RingHom.etale_algebraMap.mpr hbc)

end Etale

/-- `KummerNodeSplit` depends on the `O`-algebra structure of `N₁` only through its structure
map. -/
lemma kummerNodeSplit_of_algebra_eq {O N₁ : Type u} [CommRing O] [CommRing N₁]
    (i₁ i₂ : Algebra O N₁) (h : ∀ r, @algebraMap O N₁ _ _ i₁ r = @algebraMap O N₁ _ _ i₂ r)
    {ϖ : O} {n M' : ℕ} {u₁ v₁ : N₁} {𝔫 : Ideal N₁} {X : Type u} [CommRing X] [Algebra N₁ X]
    (hX : @KummerNodeSplit O _ ϖ n M' N₁ _ i₁ u₁ v₁ 𝔫 X _ _) :
    @KummerNodeSplit O _ ϖ n M' N₁ _ i₂ u₁ v₁ 𝔫 X _ _ := by
  obtain rfl := Algebra.algebra_ext i₁ i₂ h
  exact hX

section NodeRes

variable {O O' : Type u} [CommRing O] [CommRing O'] [Algebra O O']
  {N : Type u} [CommRing N] [Algebra O N] {B : Type u} [CommRing B] [Algebra O B] [Algebra N B]
  [IsScalarTower O N B]

/-- **`N₁' ⊗_{N'} B' ≅ N₁' ⊗_{N₁} (N₁ ⊗_N B)`** for `N' = O' ⊗_O N`, `B' = O' ⊗_O B`,
`N₁' = O' ⊗_O N₁` (`N₁` an `N`-algebra, `O`-algebra through `N`). -/
def tensorBaseChangeEquiv (N₁ : Type u) [CommRing N₁] [Algebra N N₁] :
    letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
    haveI : IsScalarTower O N N₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI := baseChangeAlgebra O O' N B
    letI := baseChangeAlgebra O O' N N₁
    (O' ⊗[O] N₁) ⊗[O' ⊗[O] N] (O' ⊗[O] B) ≃ₐ[O' ⊗[O] N₁] (O' ⊗[O] N₁) ⊗[N₁] (N₁ ⊗[N] B) :=
  letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
  haveI : IsScalarTower O N N₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI := baseChangeAlgebra O O' N B
  letI := baseChangeAlgebra O O' N N₁
  letI : Algebra N (O' ⊗[O] N₁) :=
    ((algebraMap N₁ (O' ⊗[O] N₁)).comp (algebraMap N N₁)).toAlgebra
  haveI : IsScalarTower N N₁ (O' ⊗[O] N₁) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower N (O' ⊗[O] N) (O' ⊗[O] N₁) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    change _ = baseChangeMap O O' N N₁ ((1 : O') ⊗ₜ x)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  (Algebra.TensorProduct.congr AlgEquiv.refl (cancelEquiv O O' N B).symm).trans
    ((Algebra.TensorProduct.cancelBaseChange N (O' ⊗[O] N) (O' ⊗[O] N₁) (O' ⊗[O] N₁) B).trans
      (Algebra.TensorProduct.cancelBaseChange N N₁ (O' ⊗[O] N₁) (O' ⊗[O] N₁) B).symm)

/-- **Étale-local Kummer data base change to a point with trivial residue field extension**:
let `N₁ ⊇ 𝔫` be an étale neighbourhood of `𝔪` carrying Kummer data for `B` over `O`, and
`ι : N₁ → k'` a map with kernel `𝔫` compatible with a surjection `θ' : O' → k'`. Then over
`N' = O' ⊗_O N`, `B' = O' ⊗_O B` is tamely Kummer, with trivial residue field extension, at a point
`𝔪'` over `𝔪` (the neighbourhood `O' ⊗_O N₁`, the point `resPrime θ' ι`). -/
theorem isKummerNormAtRes_baseChange {ϖ : O} {n M' : ℕ} {u v : N} {𝔪 : Ideal N}
    {N₁ : Type u} [CommRing N₁] [Algebra N N₁] [Algebra.Etale N N₁] {𝔫 : Ideal N₁}
    [𝔫.IsPrime] (h𝔫 : 𝔫.comap (algebraMap N N₁) = 𝔪)
    (hd : KummerNormData ϖ n M' u v B N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N)))
    {k' : Type u} [Field k'] (θ' : O' →+* k') (hθ' : Function.Surjective θ') (ι : N₁ →+* k')
    (hι : RingHom.ker ι = 𝔫)
    (hc : ∀ a : O, ι (algebraMap N N₁ (algebraMap O N a)) = θ' (algebraMap O O' a)) :
    letI := baseChangeAlgebra O O' N B
    ∃ 𝔪' : Ideal (O' ⊗[O] N),
      𝔪'.comap (Algebra.TensorProduct.includeRight : N →ₐ[O] O' ⊗[O] N).toRingHom = 𝔪 ∧
      IsKummerNormAtRes (algebraMap O O' ϖ) n M' ((1 : O') ⊗ₜ[O] u) ((1 : O') ⊗ₜ[O] v)
        (O' ⊗[O] B) 𝔪' := by
  letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
  haveI : IsScalarTower O N N₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI := baseChangeAlgebra O O' N B
  letI := baseChangeAlgebra O O' N N₁
  haveI := etale_baseChange O O' N N₁
  set ψ : N₁ →+* O' ⊗[O] N₁ :=
    (Algebra.TensorProduct.includeRight : N₁ →ₐ[O] O' ⊗[O] N₁).toRingHom with hψdef
  have hψ : ∀ a : O, ψ (algebraMap O N₁ a) = algebraMap O' (O' ⊗[O] N₁) (algebraMap O O' a) :=
    fun a ↦ by
      rw [hψdef, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply, one_tmul_algebraMap,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hc' : ∀ a : O, ι (algebraMap O N₁ a) = θ' (algebraMap O O' a) := hc
  set 𝔫' := resPrime θ' ι hc' with h𝔫'def
  have h𝔫' : 𝔫 ≤ 𝔫'.comap ψ := by
    rw [h𝔫'def, hψdef, comap_resPrime, hι]
  have hbc : ∀ x : N, algebraMap (O' ⊗[O] N) (O' ⊗[O] N₁) ((1 : O') ⊗ₜ[O] x) =
      ψ (algebraMap N N₁ x) := fun x ↦ by
    change baseChangeMap O O' N N₁ ((1 : O') ⊗ₜ x) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨𝔫'.comap (algebraMap (O' ⊗[O] N) (O' ⊗[O] N₁)), ?_, O' ⊗[O] N₁, inferInstance,
    inferInstance, inferInstance, 𝔫', inferInstance, rfl, ?_, ?_⟩
  · ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, hbc, ← Ideal.mem_comap, h𝔫'def, hψdef,
      comap_resPrime, hι, ← Ideal.mem_comap, h𝔫]
  · intro z
    obtain ⟨a, ha⟩ := surjective_resPrime θ' ι hc' hθ' z
    refine ⟨algebraMap O' (O' ⊗[O] N) a, ?_⟩
    rw [← ha, RingHom.comp_apply, RingHom.comp_apply]
    congr 1
    change baseChangeMap O O' N N₁ (a ⊗ₜ 1) = a ⊗ₜ 1
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  · have het : ∀ huv : ψ (algebraMap N N₁ u) * ψ (algebraMap N N₁ v) =
        algebraMap O' (O' ⊗[O] N₁) (algebraMap O O' ϖ ^ n),
        (Node.lift _ _ huv).toRingHom.Etale := fun huv ↦ by
      obtain ⟨huv0, het0, -⟩ := hd
      exact etale_node_baseChange huv0 het0 _ (map_pow _ _ _) huv
    have h1 := kummerNodeSplit_baseChange hψ hd h𝔫' het
    have h2 := KummerNodeSplit.of_algEquiv (tensorBaseChangeEquiv (O' := O') (B := B) N₁) h1
    rw [← hbc u, ← hbc v] at h2
    exact kummerNodeSplit_of_algebra_eq _ _ (fun r ↦ by
      change r ⊗ₜ 1 = baseChangeMap O O' N N₁ (r ⊗ₜ 1)
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl) h2

end NodeRes

section CuspRes

open Polynomial

variable {O O' : Type u} [CommRing O] [CommRing O'] [Algebra O O']

/-- `CuspNormSplit` depends on the `O`-algebra structure of `N₁` only through its structure
map. -/
lemma cuspNormSplit_of_algebra_eq {N₁ : Type u} [CommRing N₁]
    (i₁ i₂ : Algebra O N₁) (h : ∀ r, @algebraMap O N₁ _ _ i₁ r = @algebraMap O N₁ _ _ i₂ r)
    {e : ℕ} {t₁ : N₁} {𝔫 : Ideal N₁} {Z : Type u} [CommRing Z] [Algebra N₁ Z]
    (hZ : @Cusp.CuspNormSplit O _ e N₁ _ i₁ t₁ 𝔫 Z _ _) :
    @Cusp.CuspNormSplit O _ e N₁ _ i₂ t₁ 𝔫 Z _ _ := by
  obtain rfl := Algebra.algebra_ext i₁ i₂ h
  exact hZ

/-- **Étale cusp charts base change**: if `O[X] → N₁`, `X ↦ t₁` is étale, so is
`O'[X] → O' ⊗_O N₁`, `X ↦ 1 ⊗ t₁`. -/
theorem etale_aeval_baseChange {N₁ : Type u} [CommRing N₁] [Algebra O N₁] [Algebra O[X] N₁]
    [IsScalarTower O O[X] N₁] [Algebra.Etale O[X] N₁] :
    (aeval ((1 : O') ⊗ₜ[O] algebraMap O[X] N₁ X) : O'[X] →ₐ[O'] O' ⊗[O] N₁).toRingHom.Etale := by
  have hbc := etale_baseChange O O' O[X] N₁
  letI := baseChangeAlgebra O O' O[X] N₁
  have h : (aeval ((1 : O') ⊗ₜ[O] algebraMap O[X] N₁ X) : O'[X] →ₐ[O'] O' ⊗[O] N₁).toRingHom =
      (baseChangeMap O O' O[X] N₁).toRingHom.comp (polyEquivTensor O O').toRingHom := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, polyEquivTensor_apply, eval₂_C]
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, polyEquivTensor_apply, eval₂_X]
      rw [Algebra.TensorProduct.map_tmul]
      rfl
  rw [h]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (polyEquivTensor O O').bijective)
    (RingHom.etale_algebraMap.mpr hbc)

variable {N : Type u} [CommRing N] [Algebra O N] {B : Type u} [CommRing B] [Algebra O B]
  [Algebra N B] [IsScalarTower O N B]

/-- **Étale-local cusp Kummer data base change to a point with trivial residue field
extension** (the cusp analogue of `isKummerNormAtRes_baseChange`). -/
theorem isCuspNormAtRes_baseChange {e : ℕ} {t : N} {𝔪 : Ideal N}
    {N₁ : Type u} [CommRing N₁] [Algebra N N₁] [Algebra.Etale N N₁] {𝔫 : Ideal N₁}
    [𝔫.IsPrime] (h𝔫 : 𝔫.comap (algebraMap N N₁) = 𝔪)
    (hd : Cusp.CuspNormData O e t B N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N)))
    {k' : Type u} [Field k'] (θ' : O' →+* k') (hθ' : Function.Surjective θ') (ι : N₁ →+* k')
    (hι : RingHom.ker ι = 𝔫)
    (hc : ∀ a : O, ι (algebraMap N N₁ (algebraMap O N a)) = θ' (algebraMap O O' a)) :
    letI := baseChangeAlgebra O O' N B
    ∃ 𝔪' : Ideal (O' ⊗[O] N),
      𝔪'.comap (Algebra.TensorProduct.includeRight : N →ₐ[O] O' ⊗[O] N).toRingHom = 𝔪 ∧
      Cusp.IsCuspNormAtRes O' e ((1 : O') ⊗ₜ[O] t) (O' ⊗[O] B) 𝔪' := by
  letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
  haveI : IsScalarTower O N N₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI := baseChangeAlgebra O O' N B
  letI := baseChangeAlgebra O O' N N₁
  haveI := etale_baseChange O O' N N₁
  set ψ : N₁ →+* O' ⊗[O] N₁ :=
    (Algebra.TensorProduct.includeRight : N₁ →ₐ[O] O' ⊗[O] N₁).toRingHom with hψdef
  have hψ : ∀ a : O, ψ (algebraMap O N₁ a) = algebraMap O' (O' ⊗[O] N₁) (algebraMap O O' a) :=
    fun a ↦ by
      rw [hψdef, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply, one_tmul_algebraMap,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hc' : ∀ a : O, ι (algebraMap O N₁ a) = θ' (algebraMap O O' a) := hc
  set 𝔫' := resPrime θ' ι hc' with h𝔫'def
  have h𝔫' : 𝔫 ≤ 𝔫'.comap ψ := by
    rw [h𝔫'def, hψdef, comap_resPrime, hι]
  have hbc : ∀ x : N, algebraMap (O' ⊗[O] N) (O' ⊗[O] N₁) ((1 : O') ⊗ₜ[O] x) =
      ψ (algebraMap N N₁ x) := fun x ↦ by
    change baseChangeMap O O' N N₁ ((1 : O') ⊗ₜ x) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨𝔫'.comap (algebraMap (O' ⊗[O] N) (O' ⊗[O] N₁)), ?_, O' ⊗[O] N₁, inferInstance,
    inferInstance, inferInstance, 𝔫', inferInstance, rfl, ?_, ?_⟩
  · ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, hbc, ← Ideal.mem_comap, h𝔫'def, hψdef,
      comap_resPrime, hι, ← Ideal.mem_comap, h𝔫]
  · intro z
    obtain ⟨a, ha⟩ := surjective_resPrime θ' ι hc' hθ' z
    refine ⟨algebraMap O' (O' ⊗[O] N) a, ?_⟩
    rw [← ha, RingHom.comp_apply, RingHom.comp_apply]
    congr 1
    change baseChangeMap O O' N N₁ (a ⊗ₜ 1) = a ⊗ₜ 1
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  · have het : (aeval (ψ (algebraMap N N₁ t)) : O'[X] →ₐ[O'] O' ⊗[O] N₁).toRingHom.Etale := by
      obtain ⟨palg, hT, hX, hE, -⟩ := hd
      letI := palg
      rw [← hX]
      exact etale_aeval_baseChange
    have h1 := cuspNormSplit_baseChange hψ hd h𝔫' het
    have h2 := Cusp.CuspNormSplit.of_algEquiv (tensorBaseChangeEquiv (O' := O') (B := B) N₁) h1
    rw [← hbc t] at h2
    exact cuspNormSplit_of_algebra_eq _ _ (fun r ↦ by
      change r ⊗ₜ 1 = baseChangeMap O O' N N₁ (r ⊗ₜ 1)
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl) h2

end CuspRes

end

end KummerBaseChange

end SemistableReduction
