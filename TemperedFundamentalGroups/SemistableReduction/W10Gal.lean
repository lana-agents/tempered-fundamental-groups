/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Coords
import TemperedFundamentalGroups.SemistableReduction.W10Apply
import TemperedFundamentalGroups.SemistableReduction.W10Dom
import TemperedFundamentalGroups.SemistableReduction.ResidueCentres
import TemperedFundamentalGroups.SemistableReduction.GenusCount

/-!
# Galois transport of charts, the field `E`, and compatibility of charts along `E ⊆ C`

Blueprint §9.7a (W10 assembly). `C = K̄` with the spectral norm (`DVRNorm`), `B` finite over
`K[X]`, coordinates `f 𝔫` on the components `CompB K B 𝔫` of `B` over `K`.

* **(1)** `chartsC`: the charts `O_C[fC / fC j]` on the components of `C ⊗_K B`
  (`fC = fE` for `E = C`); `galMax`, `galEquiv`: the action of `τ ∈ Gal(C/K)` on the
  components; `htr_gal`: the input `htr` of `W10Discs.exists_V0` (with `hinv_gal`,
  `hiso_gal`); `finite_RT_chartsC`, `hfin_chartsC`: finiteness of the residue-transcendental
  centres (O9).
* **(2)** for `E ⊆ C` finite over `K`: `valuationSubring_E` (the restricted norm has valuation ring
  `O_E`), `isDiscreteValuationRing_E`, `perfectField_residueField_OE`, `huniq_E` (`O_C` is the only
  extension of `O_E`; `UniqueExtension.valuationSubring_eq`).
* **(3)** `contrB_contrMax`, `compMap_mk_lbMap`, `hχ_compMap`, `hY_compMap`: the charts
  `O_E[fE / fE j]` and `O_C[fC / fC j]` correspond under `χ = compMap` (input `hY` of
  `W10Dom.exists_mem_RT_comap_eq`).
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace W10Gal

open TemperedFundamentalGroups W10Fields W10Assembly ZariskiModel

attribute [local instance] polyAlgebra

section Transport

variable {K : Type u} [Field K] (B : Type u) [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B]
  {M : Type u} [Field M] [Algebra K M]

/-- The action of `τ` on the maximal ideals of `LX`: `𝔪 ↦ τ⁻¹(𝔪)`. -/
noncomputable def galMax (τ : M ≃ₐ[K] M) (𝔪 : MaximalSpectrum (LX K M B)) :
    MaximalSpectrum (LX K M B) :=
  ⟨𝔪.asIdeal.comap (lxEquiv K M B τ 1), IsArtinianRing.isMaximal_of_isPrime _⟩

/-- `τ : Comp (τ⁻¹ 𝔪) ≃ Comp 𝔪`. -/
noncomputable def galEquiv (τ : M ≃ₐ[K] M) (𝔪 : MaximalSpectrum (LX K M B)) :
    Comp K M B (galMax B τ 𝔪) ≃+* Comp K M B 𝔪 :=
  Ideal.quotientEquiv _ _ (lxEquiv K M B τ 1)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm

lemma galEquiv_mk (τ : M ≃ₐ[K] M) (𝔪 : MaximalSpectrum (LX K M B)) (y : LX K M B) :
    galEquiv B τ 𝔪 (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (lxEquiv K M B τ 1 y) := rfl

/-- **(a)** `τ` acts semilinearly. -/
theorem galEquiv_algebraMap (τ : M ≃ₐ[K] M) (𝔪 : MaximalSpectrum (LX K M B)) (φ : RatFunc M) :
    galEquiv B τ 𝔪 (algebraMap (RatFunc M) _ φ) =
      algebraMap (RatFunc M) _ (ratFuncMap (τ : M →+* M) φ) := by
  change galEquiv B τ 𝔪 (Ideal.Quotient.mk _ (algebraMap (RatFunc M) (LX K M B) φ)) =
    Ideal.Quotient.mk _ (algebraMap (RatFunc M) (LX K M B) (ratFuncMap (τ : M →+* M) φ))
  rw [galEquiv_mk, lxEquiv_algebraMap_ratFunc]

lemma galEquiv_algebraMap_M (τ : M ≃ₐ[K] M) (𝔪 : MaximalSpectrum (LX K M B)) (c : M) :
    galEquiv B τ 𝔪 (algebraMap M _ c) = algebraMap M _ (τ c) := by
  rw [IsScalarTower.algebraMap_apply M (RatFunc M) (Comp K M B (galMax B τ 𝔪)),
    galEquiv_algebraMap, ratFuncMap_algebraMap_C, ← IsScalarTower.algebraMap_apply]
  rfl

omit [Module.Finite K[X] B] in
/-- `K`-rationality: the action fixes the image of `LB`. -/
lemma lxEquiv_lbMap (τ : M ≃ₐ[K] M) (y : LB K B) :
    lxEquiv K M B τ 1 (lbMap K M B y) = lbMap K M B y := by
  have : ((lxEquiv K M B τ 1 : LX K M B →+* LX K M B)).comp (lbMap K M B) = lbMap K M B := by
    refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B (nonZeroDivisors K[X]))
      (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, lbMap_algebraMap, lxEquiv_algebraMap,
      bxEquiv_ofA]
    rfl
  exact congrArg (fun g : LB K B →+* LX K M B ↦ g y) this

lemma contrB_galMax (τ : M ≃ₐ[K] M) (𝔪 : MaximalSpectrum (LX K M B)) :
    contrB K M B (galMax B τ 𝔪) = contrB K M B 𝔪 := by
  ext y
  change lxEquiv K M B τ 1 (lbMap K M B y) ∈ 𝔪.asIdeal ↔ lbMap K M B y ∈ 𝔪.asIdeal
  rw [lxEquiv_lbMap]

lemma galEquiv_mk_lbMap (τ : M ≃ₐ[K] M) (𝔪 : MaximalSpectrum (LX K M B)) (y : LB K B) :
    galEquiv B τ 𝔪 (Ideal.Quotient.mk _ (lbMap K M B y)) =
      Ideal.Quotient.mk _ (lbMap K M B y) := by
  rw [galEquiv_mk, lxEquiv_lbMap]

end Transport

section ProjChart

variable {F₁ F₂ : Type*} [Field F₁] [Field F₂] {ι : Type*}

lemma map_projChart (χ : F₁ →+* F₂) (R : Subring F₁) (g : ι → F₁) (j : ι) :
    (projChart R g j).map χ = projChart (R.map χ) (fun k ↦ χ (g k)) j := by
  rw [projChart, projChart, RingHom.map_closure, Set.image_union, ← Set.range_comp]
  congr 2
  ext k; simp

end ProjChart

section Charts

variable {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  (B : Type u) [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B]
  {n : MaximalSpectrum (LB K B) → ℕ} (f : ∀ 𝔫, Fin (n 𝔫 + 1) → CompB K B 𝔫)

/-- `O_C`, the valuation ring of the spectral norm on `K̄`. -/
noncomputable def OC : ValuationSubring (AlgebraicClosure K) :=
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  (NormedField.valuation (K := AlgebraicClosure K)).valuationSubring

lemma mem_OC_iff (c : AlgebraicClosure K) :
    letI := DVRNorm.normedFieldAlgCl O
    c ∈ OC O ↔ ‖c‖ ≤ 1 := by
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  change NormedField.valuation c ≤ 1 ↔ _
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
  rfl

lemma mem_OC_iff_algEquiv (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (c : AlgebraicClosure K) : τ c ∈ OC O ↔ c ∈ OC O := by
  rw [mem_OC_iff, mem_OC_iff, DVRNorm.norm_algEquiv_apply]

/-- The charts `O_M[fM / fM j]` on a component of `M ⊗_K B`. -/
def chartsM {M : Type u} [Field M] [Algebra K M] (OM : ValuationSubring M)
    (𝔪 : MaximalSpectrum (LX K M B)) : Set (Subring (Comp K M B 𝔪)) :=
  Set.range fun j ↦ projChart (baseRing _ OM) (fE (f := f) 𝔪) j

/-- The charts `O_C[fC / fC j]` on a component of `C ⊗_K B`. -/
abbrev chartsC (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) :
    Set (Subring (Comp K (AlgebraicClosure K) B 𝔪')) :=
  chartsM B f (OC O) 𝔪'

/-- Lifts of the coordinates to `LB`. -/
noncomputable def liftF (𝔫 : MaximalSpectrum (LB K B)) (k : Fin (n 𝔫 + 1)) : LB K B :=
  (Ideal.Quotient.mk_surjective (f 𝔫 k)).choose

omit [Module.Finite K[X] B] in
lemma mk_liftF (𝔫 : MaximalSpectrum (LB K B)) (k : Fin (n 𝔫 + 1)) :
    Ideal.Quotient.mk _ (liftF B f 𝔫 k) = f 𝔫 k :=
  (Ideal.Quotient.mk_surjective (f 𝔫 k)).choose_spec

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] in
lemma chartsM_eq {M : Type u} [Field M] [Algebra K M] (OM : ValuationSubring M)
    (𝔪 : MaximalSpectrum (LX K M B)) (𝔫 : MaximalSpectrum (LB K B)) (h : contrB K M B 𝔪 = 𝔫) :
    chartsM B f OM 𝔪 = Set.range fun j : Fin (n 𝔫 + 1) ↦ projChart (baseRing _ OM)
      (fun k ↦ Ideal.Quotient.mk 𝔪.asIdeal (lbMap K M B (liftF B f 𝔫 k))) j := by
  subst h
  have : fE (f := f) 𝔪 = fun k ↦ Ideal.Quotient.mk 𝔪.asIdeal
      (lbMap K M B (liftF B f (contrB K M B 𝔪) k)) := by
    funext k
    change compBMap _ _ _ 𝔪 (f _ k) = _
    rw [← mk_liftF B f _ k, compBMap_mk]
  rw [chartsM, this]

lemma map_baseRing_galEquiv_symm (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) :
    (baseRing _ (OC O)).map ((galEquiv B τ 𝔪').symm : Comp K _ B 𝔪' →+* _) =
      baseRing (Comp K _ B (galMax B τ 𝔪')) (OC O) := by
  have h (c : AlgebraicClosure K) : (galEquiv B τ 𝔪').symm (algebraMap _ _ c) =
      algebraMap _ (Comp K _ B (galMax B τ 𝔪')) (τ.symm c) := by
    rw [RingEquiv.symm_apply_eq, galEquiv_algebraMap_M, AlgEquiv.apply_symm_apply]
  ext x
  simp only [baseRing, Subring.mem_map, ValuationSubring.mem_toSubring]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨τ.symm c, ?_, (h c).symm⟩
    rwa [← mem_OC_iff_algEquiv O τ, AlgEquiv.apply_symm_apply]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨_, ⟨τ c, (mem_OC_iff_algEquiv O τ c).2 hc, rfl⟩, ?_⟩
    change (galEquiv B τ 𝔪').symm _ = _
    rw [h, AlgEquiv.symm_apply_apply]

/-- **(b)** The action of `τ` transports the charts. -/
theorem comap_mem_chartsC (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) :
    ∀ Bc ∈ chartsC O B f 𝔪', Bc.comap (galEquiv B τ 𝔪' : Comp K _ B (galMax B τ 𝔪') →+* _) ∈
      chartsC O B f (galMax B τ 𝔪') := by
  intro Bc hB
  rw [chartsC, chartsM_eq B f _ 𝔪' _ rfl] at hB
  obtain ⟨j, rfl⟩ := hB
  rw [chartsC, chartsM_eq B f _ (galMax B τ 𝔪') _ (contrB_galMax B τ 𝔪')]
  refine ⟨j, ?_⟩
  dsimp only
  rw [Subring.comap_equiv_eq_map_symm, map_projChart, map_baseRing_galEquiv_symm]
  refine congrArg (fun g ↦ projChart _ g j) (funext fun k ↦ ?_)
  exact ((RingEquiv.symm_apply_eq _).2 (galEquiv_mk_lbMap B τ 𝔪' _).symm).symm

/-- **(1) The input `htr` of `exists_V0`** for `Gal = Gal(C/K)`. -/
theorem htr_gal :
    letI := DVRNorm.normedFieldAlgCl O
    ∀ τ ∈ Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ τ.toRingEquiv),
      ∃ (π : MaximalSpectrum (LX K (AlgebraicClosure K) B) →
          MaximalSpectrum (LX K (AlgebraicClosure K) B))
        (σ : ∀ k, Comp K _ B (π k) ≃+* Comp K _ B k),
        (∀ k φ, σ k (algebraMap (RatFunc (AlgebraicClosure K)) _ φ) =
          algebraMap (RatFunc (AlgebraicClosure K)) _
            (ratFuncMap (τ : AlgebraicClosure K →+* AlgebraicClosure K) φ)) ∧
        ∀ k, ∀ Bc ∈ chartsC O B f k, Bc.comap (σ k : Comp K _ B (π k) →+* _) ∈
          chartsC O B f (π k) := by
  rintro _ ⟨τ, rfl⟩
  exact ⟨galMax B τ, galEquiv B τ, fun k φ ↦ galEquiv_algebraMap B τ k φ,
    fun k ↦ comap_mem_chartsC O B f τ k⟩

theorem hinv_gal :
    ∀ τ ∈ Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ τ.toRingEquiv),
      τ.symm ∈ Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ τ.toRingEquiv) := by
  rintro _ ⟨τ, rfl⟩
  exact ⟨τ.symm, rfl⟩

theorem hiso_gal :
    letI := DVRNorm.normedFieldAlgCl O
    ∀ τ ∈ Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ τ.toRingEquiv),
      ∀ z, ‖τ z‖ = ‖z‖ := by
  rintro _ ⟨τ, rfl⟩ z
  exact DVRNorm.norm_algEquiv_apply O τ z

/-- **O9 for the charts `chartsC`**: finitely many residue-transcendental centres. -/
theorem finite_RT_chartsC (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) :
    (W10Discs.RT (OC O) (chartsC O B f 𝔪')).Finite := by
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  haveI : IsCurveFunctionField (AlgebraicClosure K) (Comp K (AlgebraicClosure K) B 𝔪') :=
    GaussFibre.isCurveFunctionField_F
  refine (finite_residueTranscendental_centres (O := OC O)
    (projModel_isFiniteType (R := baseRing _ (OC O)) (f := fE (f := f) 𝔪'))).subset ?_
  rintro W ⟨hW, Bc, hBc, hBW, z, hz, hRT⟩
  obtain ⟨j, rfl⟩ := hBc
  exact ⟨hW, _, mem_projModel_charts.2 ⟨j, rfl⟩, hBW, z, hz, hRT⟩

/-- `finite_RT_chartsC` in the form of `exists_V0`'s `hfin`. -/
theorem hfin_chartsC :
    letI := DVRNorm.normedFieldAlgCl O; haveI := DVRNorm.isUltrametricDist_algCl O
    ∀ 𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B),
      (W10Discs.RT (NormedField.valuation (K := AlgebraicClosure K)).valuationSubring
        (chartsC O B f 𝔪')).Finite :=
  fun 𝔪' ↦ finite_RT_chartsC O B f 𝔪'

end Charts

/-! ### (3) Compatibility of the charts along `E ⊆ C` -/

section Compat

variable {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  (B : Type u) [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B]
  {n : MaximalSpectrum (LB K B) → ℕ} (f : ∀ 𝔫, Fin (n 𝔫 + 1) → CompB K B 𝔫)
  (E : IntermediateField K (AlgebraicClosure K))

omit [Module.Finite K[X] B] in
lemma lxMap_lbMap (y : LB K B) :
    lxMap K E B (AlgebraicClosure K) (lbMap K E B y) = lbMap K (AlgebraicClosure K) B y := by
  have : (lxMap K E B (AlgebraicClosure K)).comp (lbMap K E B) =
      lbMap K (AlgebraicClosure K) B := by
    refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B (nonZeroDivisors K[X]))
      (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, lbMap_algebraMap, lxMap_algebraMap, bxMap_ofA]
  exact congrArg (fun g : LB K B →+* _ ↦ g y) this

lemma contrB_contrMax (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) :
    contrB K E B (contrMax K E B (AlgebraicClosure K) 𝔪') = contrB K (AlgebraicClosure K) B 𝔪' := by
  ext y
  change lxMap K E B _ (lbMap K E B y) ∈ 𝔪'.asIdeal ↔ _
  rw [lxMap_lbMap]
  rfl

lemma compMap_mk_lbMap (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) (y : LB K B) :
    compMap K E B (AlgebraicClosure K) 𝔪' (Ideal.Quotient.mk _ (lbMap K E B y)) =
      Ideal.Quotient.mk _ (lbMap K (AlgebraicClosure K) B y) := by
  rw [compMap_mk, lxMap_lbMap]

/-- **`hχ`** for `χ = compMap` (`W10Dom.exists_mem_RT_comap_eq`). -/
lemma hχ_compMap (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) (x : RatFunc E) :
    compMap K E B (AlgebraicClosure K) 𝔪' (algebraMap (RatFunc E) _ x) =
      algebraMap (RatFunc (AlgebraicClosure K)) _
        (ratFuncMap (algebraMap E (AlgebraicClosure K)) x) :=
  compMap_algebraMap K B 𝔪' x

lemma compMap_algebraMap_E (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) (e : E) :
    compMap K E B (AlgebraicClosure K) 𝔪' (algebraMap E _ e) =
      algebraMap (AlgebraicClosure K) _ (e : AlgebraicClosure K) := by
  rw [IsScalarTower.algebraMap_apply E (RatFunc E), hχ_compMap, ratFuncMap_algebraMap_C,
    ← IsScalarTower.algebraMap_apply]
  rfl

/-- **(3) `hY` for `χ = compMap`**: the chart `O_E[fE / fE j]` maps into `O_C[fC / fC j]`, which
is generated by `O_C` and the image. -/
theorem hY_compMap (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) :
    ∀ Bch ∈ chartsM B f (W10Apply.OE O E) (contrMax K E B (AlgebraicClosure K) 𝔪'),
      ∃ B' ∈ chartsC O B f 𝔪', (∀ z ∈ Bch, compMap K E B (AlgebraicClosure K) 𝔪' z ∈ B') ∧
        B' ≤ Subring.closure ((baseRing (Comp K (AlgebraicClosure K) B 𝔪') (OC O) :
          Set (Comp K (AlgebraicClosure K) B 𝔪')) ∪
            compMap K E B (AlgebraicClosure K) 𝔪' '' Bch) := by
  intro Bch hB
  set χ := compMap K E B (AlgebraicClosure K) 𝔪'
  rw [chartsM_eq B f _ _ _ (contrB_contrMax B E 𝔪')] at hB
  obtain ⟨j, rfl⟩ := hB
  dsimp only
  have hmem : projChart (baseRing (Comp K (AlgebraicClosure K) B 𝔪') (OC O))
      (fun k ↦ Ideal.Quotient.mk 𝔪'.asIdeal
        (lbMap K (AlgebraicClosure K) B (liftF B f (contrB K (AlgebraicClosure K) B 𝔪') k))) j ∈
        chartsC O B f 𝔪' := by
    rw [chartsC, chartsM_eq B f (OC O) 𝔪' _ rfl]
    exact ⟨j, rfl⟩
  refine ⟨_, hmem, ?_, ?_⟩
  · have hbase : (baseRing (Comp K E B (contrMax K E B (AlgebraicClosure K) 𝔪'))
        (W10Apply.OE O E)).map χ ≤ baseRing (Comp K (AlgebraicClosure K) B 𝔪') (OC O) := by
      rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
      refine ⟨(e : AlgebraicClosure K), ?_, (compMap_algebraMap_E B E 𝔪' e).symm⟩
      change (e : AlgebraicClosure K) ∈ OC O
      rw [mem_OC_iff]
      exact (W10Apply.mem_OE_iff_norm O E e).1 he
    intro z hz
    have hz' : χ z ∈ (projChart (baseRing _ (W10Apply.OE O E))
        (fun k ↦ Ideal.Quotient.mk (contrMax K E B (AlgebraicClosure K) 𝔪').asIdeal
          (lbMap K E B (liftF B f (contrB K (AlgebraicClosure K) B 𝔪') k))) j).map χ :=
      ⟨z, hz, rfl⟩
    rw [map_projChart] at hz'
    refine (projChart_le (hbase.trans (base_le_projChart j)) fun k ↦ ?_) hz'
    simp only [χ, compMap_mk_lbMap]
    exact div_mem_projChart j k
  · refine projChart_le (fun x hx ↦ Subring.subset_closure (Or.inl hx)) fun k ↦ ?_
    refine Subring.subset_closure (Or.inr ⟨_, div_mem_projChart j k, ?_⟩)
    rw [map_div₀, compMap_mk_lbMap, compMap_mk_lbMap]

end Compat

/-! ### (2) The field `E` -/

section FieldE

variable {K : Type u} [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] (E : IntermediateField K (AlgebraicClosure K))

omit [CharZero K] in
/-- The valuation ring of the restricted norm on `E` is `O_E`. -/
theorem valuationSubring_E :
    letI := W10Apply.normedFieldE O E; haveI := W10Apply.isUltrametricDist_E O E
    (NormedField.valuation (K := E)).valuationSubring = W10Apply.OE O E := by
  letI := W10Apply.normedFieldE O E
  haveI := W10Apply.isUltrametricDist_E O E
  ext x
  change NormedField.valuation x ≤ 1 ↔ _
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, W10Apply.mem_OE_iff_norm]
  rfl

variable [FiniteDimensional K E]

theorem isDiscreteValuationRing_E :
    letI := W10Apply.normedFieldE O E; haveI := W10Apply.isUltrametricDist_E O E
    IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring := by
  letI := W10Apply.normedFieldE O E
  haveI := W10Apply.isUltrametricDist_E O E
  rw [valuationSubring_E]
  infer_instance

omit [CharZero K] in
/-- The residue field of `O_E` is perfect if that of `O` is (finite extension). -/
theorem perfectField_residueField_OE [PerfectField (ResidueField O)] :
    PerfectField (ResidueField (W10Apply.OE O E)) := by
  haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI := residueAlgebra (W10Apply.comap_OE O E)
  haveI := isAlgebraic_residueField (W10Apply.comap_OE O E)
  exact Algebra.IsAlgebraic.perfectField (ResidueField O)

omit [CharZero K] [FiniteDimensional K E] in
lemma comap_OC_eq : (OC O).comap (algebraMap E (AlgebraicClosure K)) = W10Apply.OE O E := by
  ext x
  rw [ValuationSubring.mem_comap, mem_OC_iff, W10Apply.mem_OE_iff_norm]
  rfl

omit [CharZero K] in
/-- **`huniq`** (D3b form): `O_C` is the only valuation ring of `C` over `O_E` (`E` complete). -/
theorem huniq_E :
    letI := DVRNorm.normedFieldAlgCl O; haveI := DVRNorm.isUltrametricDist_algCl O
    ∀ V : ValuationSubring (AlgebraicClosure K),
      V.comap (algebraMap E (AlgebraicClosure K)) =
        ((NormedField.valuation (K := AlgebraicClosure K)).valuationSubring).comap
          (algebraMap E (AlgebraicClosure K)) →
        V = (NormedField.valuation (K := AlgebraicClosure K)).valuationSubring := by
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  intro V hV
  letI := W10Apply.normedFieldE O E
  haveI := W10Apply.isUltrametricDist_E O E
  haveI := W10Apply.completeSpace_E O E
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) E
  have hOC : ((NormedField.valuation (K := AlgebraicClosure K)).valuationSubring).comap
      (algebraMap E (AlgebraicClosure K)) = W10Apply.OE O E := comap_OC_eq O E
  have hcomap (w : Valuation (AlgebraicClosure K) NNReal) :
      (w.comap (algebraMap E (AlgebraicClosure K))).valuationSubring =
        w.valuationSubring.comap (algebraMap E (AlgebraicClosure K)) := by
    ext x; rfl
  haveI h1 : (NormedField.valuation (K := E)).HasExtension V.valuation := by
    refine ⟨(Valuation.isEquiv_iff_valuationSubring _ _).2 ?_⟩
    rw [valuationSubring_E]
    have : (V.valuation.comap (algebraMap E (AlgebraicClosure K))).valuationSubring =
        V.comap (algebraMap E (AlgebraicClosure K)) := by
      ext x
      change V.valuation _ ≤ 1 ↔ _
      rw [ValuationSubring.valuation_le_one_iff]
      rfl
    rw [this, hV, hOC]
  haveI h2 : (NormedField.valuation (K := E)).HasExtension
      (NormedField.valuation (K := AlgebraicClosure K)) := by
    refine ⟨(Valuation.isEquiv_iff_valuationSubring _ _).2 ?_⟩
    rw [valuationSubring_E, hcomap, hOC]
  have := UniqueExtension.valuationSubring_eq (K := E) V.valuation
    (NormedField.valuation (K := AlgebraicClosure K))
  rwa [ValuationSubring.valuationSubring_valuation] at this

end FieldE

end W10Gal

end SemistableReduction
