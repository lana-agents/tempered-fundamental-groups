/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.UnramifiedLift

/-!
# An unramified extension whose residue field contains given finite separable extensions

S5.7 (finite-`k` route, step (c)/(2)): the residue fields of the finitely many chosen étale
neighbourhoods of the Kummer data are finite separable extensions of `k`; we need one finite
unramified `O → O'` whose residue field `k'` receives all of them.

* **`UnramifiedLift.exists_embeddings`**: finitely many finite separable extensions `κᵢ / k` embed
  into one finite separable extension `E / k` (the compositum of their images in an algebraic
  closure);
* **`UnramifiedLift.exists_monic_lift`**: for a finite separable `k' / k` and a surjection
  `θ : O ↠ k` with kernel `𝔪_O`, there is a monic `f ∈ O[X]` with irreducible separable reduction
  (the hypotheses of `UnramifiedLift`) and a surjection `θ' : O[X]/(f) ↠ k'` over `θ`
  (`f` lifts the minimal polynomial of a primitive element);
* **`UnramifiedLift.eq_map_of_comap_eq`**: if `O → N/𝔪` is surjective and `𝔪_O O'` is the only
  prime of `O'` above it, the only prime of `O' ⊗_O N` over `𝔪` is `𝔪 (O' ⊗_O N)` (identifies
  the point `𝔪'` of `isKummerNormAtRes_baseChange` with the base-changed node / cusp point).
-/

universe u v

open Polynomial IsLocalRing

namespace SemistableReduction

namespace UnramifiedLift

/-- **Finitely many finite separable extensions embed into one.** -/
theorem exists_embeddings {k : Type u} [Field k] {ι : Type*} [Finite ι] (κ : ι → Type v)
    [∀ i, Field (κ i)] [∀ i, Algebra k (κ i)] [∀ i, FiniteDimensional k (κ i)]
    [∀ i, Algebra.IsSeparable k (κ i)] :
    ∃ E : IntermediateField k (AlgebraicClosure k), FiniteDimensional k E ∧
      Algebra.IsSeparable k E ∧ ∀ i, Nonempty (κ i →ₐ[k] E) := by
  let e : ∀ i, κ i →ₐ[k] AlgebraicClosure k := fun i ↦ IsAlgClosed.lift
  haveI : ∀ i, FiniteDimensional k (e i).fieldRange := fun i ↦
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (e i)).toLinearEquiv
  haveI : ∀ i, Algebra.IsSeparable k (e i).fieldRange := fun i ↦
    Algebra.IsSeparable.of_algHom k (κ i) (AlgEquiv.ofInjectiveField (e i)).symm.toAlgHom
  refine ⟨⨆ i, (e i).fieldRange, inferInstance, inferInstance, fun i ↦ ⟨?_⟩⟩
  exact (IntermediateField.inclusion (le_iSup (fun i ↦ (e i).fieldRange) i)).comp
    (AlgEquiv.ofInjectiveField (e i)).toAlgHom

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u}
  [Field k] (θ : O →+* k) (hθ : Function.Surjective θ) (hker : RingHom.ker θ = maximalIdeal O)

include hθ hker in
/-- **A monic lift of the minimal polynomial of a primitive element**: for a finite separable
`k' / k`, there is a monic `f ∈ O[X]` whose reduction is irreducible and separable, and a
surjection `θ' : O[X]/(f) → k'` extending `θ`. -/
theorem exists_monic_lift (k' : Type*) [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [Algebra.IsSeparable k k'] :
    ∃ f : O[X], f.Monic ∧ Irreducible (f.map (Ideal.Quotient.mk (maximalIdeal O))) ∧
      (f.map (Ideal.Quotient.mk (maximalIdeal O))).Separable ∧
      ∃ θ' : AdjoinRoot f →+* k', Function.Surjective θ' ∧
        ∀ a : O, θ' (algebraMap O (AdjoinRoot f) a) = algebraMap k k' (θ a) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k k'
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  set g := minpoly k α with hg
  have hlift : g ∈ lifts θ := by
    rw [lifts_iff_coeff_lifts]
    exact fun n ↦ hθ _
  obtain ⟨f, hfg, -, hf⟩ := lifts_and_degree_eq_and_monic hlift (minpoly.monic hint)
  -- the residue field of `O` is `k`
  let φ : (O ⧸ maximalIdeal O) ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hθ)
  have hφ : φ.toRingHom.comp (Ideal.Quotient.mk (maximalIdeal O)) = θ := by
    ext a
    rfl
  have hmap : (f.map (Ideal.Quotient.mk (maximalIdeal O))).map φ.toRingHom = g := by
    rw [Polynomial.map_map, hφ, hfg]
  have hmap' : f.map (Ideal.Quotient.mk (maximalIdeal O)) = g.map φ.symm.toRingHom := by
    rw [← hmap, Polynomial.map_map]
    have : φ.symm.toRingHom.comp φ.toRingHom = RingHom.id _ := by
      ext x
      simp
    rw [this, Polynomial.map_id]
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · rw [hmap', ← Polynomial.coe_mapRingHom]
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv φ.symm).toMulEquiv).mpr
      (minpoly.irreducible hint)
  · rw [hmap']
    exact Polynomial.Separable.map
      (Algebra.IsSeparable.isSeparable k α : (minpoly k α).Separable)
  · have hroot : eval₂ ((algebraMap k k').comp θ) α f = 0 := by
      rw [← eval₂_map, hfg, ← aeval_def, minpoly.aeval]
    refine ⟨AdjoinRoot.lift ((algebraMap k k').comp θ) α hroot, ?_, fun a ↦ ?_⟩
    · intro x
      have hx : x ∈ Algebra.adjoin k {α} := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα]
        trivial
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := Polynomial.map_surjective θ hθ p
      refine ⟨AdjoinRoot.mk f q, ?_⟩
      rw [AdjoinRoot.lift_mk, ← eval₂_map, ← aeval_def]
      rfl
    · rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, RingHom.comp_apply]

section Point

open TensorProduct

/-- **The point of `O' ⊗_O N` over a residue-rational point**: if `O → N/𝔪` is surjective,
`𝔪_O ⊆ 𝔪` and `𝔪_O O'` is the only prime of `O'` containing `𝔪_O O'` (e.g. `O'` local and
unramified over `O`), then the only prime of `O' ⊗_O N` over `𝔪` is `𝔪 (O' ⊗_O N)`. -/
theorem eq_map_of_comap_eq {O O' N : Type*} [CommRing O] [CommRing O'] [Algebra O O']
    [CommRing N] [Algebra O N] (𝔪O : Ideal O) (𝔪 : Ideal N)
    (h𝔪O : 𝔪O ≤ 𝔪.comap (algebraMap O N))
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O N)))
    (hO' : ∀ Q : Ideal O', Q.IsPrime → 𝔪O.map (algebraMap O O') ≤ Q →
      Q = 𝔪O.map (algebraMap O O'))
    (P : Ideal (O' ⊗[O] N)) [P.IsPrime]
    (hP : P.comap (Algebra.TensorProduct.includeRight : N →ₐ[O] O' ⊗[O] N).toRingHom = 𝔪) :
    P = 𝔪.map (Algebra.TensorProduct.includeRight : N →ₐ[O] O' ⊗[O] N).toRingHom := by
  have hswap : ∀ a : O, (algebraMap O O' a) ⊗ₜ[O] (1 : N) = (1 : O') ⊗ₜ[O] algebraMap O N a :=
    fun a ↦ by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
  set I := 𝔪.map (Algebra.TensorProduct.includeRight : N →ₐ[O] O' ⊗[O] N).toRingHom
  have hIP : I ≤ P := Ideal.map_le_iff_le_comap.2 hP.ge
  have hmem : ∀ n ∈ 𝔪, ((1 : O') ⊗ₜ[O] n) ∈ I := fun n hn ↦ Ideal.mem_map_of_mem _ hn
  -- every element is `o' ⊗ 1` modulo `I`
  have hred : ∀ x : O' ⊗[O] N, ∃ o' : O', x - o' ⊗ₜ[O] (1 : N) ∈ I := by
    intro x
    induction x with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by
        rw [show x + y - (a + b) ⊗ₜ[O] (1 : N) = (x - a ⊗ₜ 1) + (y - b ⊗ₜ 1) by
          rw [TensorProduct.add_tmul]; abel]
        exact I.add_mem ha hb⟩
    | tmul o' n =>
      obtain ⟨o, ho⟩ := hres (Ideal.Quotient.mk 𝔪 n)
      have hn : n - algebraMap O N o ∈ 𝔪 := by
        rw [← Ideal.Quotient.eq]
        exact ho.symm
      refine ⟨o' * algebraMap O O' o, ?_⟩
      have : o' ⊗ₜ[O] n - (o' * algebraMap O O' o) ⊗ₜ[O] (1 : N) =
          (o' ⊗ₜ[O] (1 : N)) * ((1 : O') ⊗ₜ[O] (n - algebraMap O N o)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub]
        congr 1
        rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
          Algebra.algebraMap_eq_smul_one (A := N)]
      rw [this]
      exact I.mul_mem_left _ (hmem _ hn)
  -- the trace of `P` on `O'` is `𝔪_O O'`
  have hQ : P.comap (algebraMap O' (O' ⊗[O] N)) = 𝔪O.map (algebraMap O O') := by
    refine hO' _ (Ideal.comap_isPrime _ _) (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
    rw [Ideal.mem_comap, Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, hswap]
    exact hIP (hmem _ (h𝔪O ha))
  have hOI : ∀ o' ∈ 𝔪O.map (algebraMap O O'), o' ⊗ₜ[O] (1 : N) ∈ I := by
    intro o' ho'
    have h : (𝔪O.map (algebraMap O O')).map (algebraMap O' (O' ⊗[O] N)) ≤ I := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, hswap]
      exact hmem _ (h𝔪O ha)
    exact h (Ideal.mem_map_of_mem _ ho')
  refine le_antisymm (fun x hx ↦ ?_) hIP
  obtain ⟨o', ho'⟩ := hred x
  have h1 : o' ⊗ₜ[O] (1 : N) ∈ P := by
    have := P.sub_mem hx (hIP ho')
    rwa [sub_sub_cancel] at this
  have h2 : o' ∈ 𝔪O.map (algebraMap O O') := by
    rw [← hQ, Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact h1
  have := I.add_mem ho' (hOI o' h2)
  rwa [sub_add_cancel] at this

end Point

end UnramifiedLift

end SemistableReduction
