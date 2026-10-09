/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingWalk
import TemperedFundamentalGroups.SemistableReduction.UniqueExtDVR
import TemperedFundamentalGroups.SemistableReduction.CrossingX1

/-!
# Glue for `Statement.CrossingX1` (Blueprint §10.3.8)

* `eq_of_le_of_lt_one`: a valuation subring of `K` containing the DVR `O` with its uniformizer in
  the maximal ideal is `O`;
* `mem_of_base`: a valuation subring of `L₁` containing the image of `O` with `ϖ₀` in its maximal
  ideal contains the images of `O₁` and `O₂` (unique extension over the complete `O`);
* `baseHom_target`: the base map of the target through `j'` is the algebra map on `O` (from the
  compatibility of `ψ` over `O` and the W-model structure of the source).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingGlue

open CentreGerms ValuativeCentre ModelCode CrossingSource

/-- **Valuation subrings above a DVR.** -/
theorem eq_of_le_of_lt_one {K : Type*} [Field K] {O : ValuationSubring K}
    [IsDiscreteValuationRing O] {ϖ₀ : O} (hϖ₀ : Irreducible ϖ₀) {V : ValuationSubring K}
    (hOV : O ≤ V) (hϖV : V.valuation (ϖ₀ : K) < 1) : V = O := by
  refine le_antisymm (fun x hx ↦ ?_) hOV
  by_contra hxO
  have hxi : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  have hx0 : x ≠ 0 := fun h ↦ hxO (h ▸ O.zero_mem)
  have hnu : ¬ IsUnit (⟨x⁻¹, hxi⟩ : O) := fun hu ↦ by
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    apply hxO
    have : x = (w : K) := by
      have h1 : x⁻¹ * (w : K) = 1 := congrArg Subtype.val hw
      exact (inv_mul_eq_one₀ hx0).1 h1
    rw [this]; exact w.2
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.1 (hϖ₀.maximalIdeal_eq ▸ (show (⟨x⁻¹, hxi⟩ : O) ∈
    maximalIdeal O from hnu))
  have e : x⁻¹ = (o : K) * ϖ₀ := congrArg Subtype.val ho.symm
  have hv : V.valuation x⁻¹ < 1 := by
    rw [e, map_mul]
    exact (mul_le_of_le_one_left' ((V.valuation_le_one_iff _).2 (hOV o.2))).trans_lt hϖV
  have hxV : V.valuation x ≤ 1 := (V.valuation_le_one_iff _).2 hx
  have : V.valuation (x * x⁻¹) < 1 := (mul_le_of_le_one_left' hxV).trans_lt hv
  rw [mul_inv_cancel₀ hx0, map_one] at this
  exact lt_irrefl _ this

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] {K' : Type u} [Field K'] [Algebra K K']
  [FiniteDimensional K K'] {O' : ValuationSubring K'} (h' : O'.comap (algebraMap K K') = O)
  {F : Type u} [Field F] [Algebra K F]

include h' in
/-- **Unique extension, inside a bigger field.** A valuation subring of `F` containing the image
of `O` with `ϖ₀` in its maximal ideal contains the image of `O'` under any `K`-embedding. -/
theorem mem_of_base {ϖ₀ : O} (hϖ₀ : Irreducible ϖ₀) (φ : K' →+* F)
    (hφ : φ.comp (algebraMap K K') = algebraMap K F) {R : ValuationSubring F}
    (hR : ∀ o : O, algebraMap K F o ∈ R) (hRϖ : R.valuation (algebraMap K F ϖ₀) < 1)
    (o' : O') : φ o' ∈ R := by
  have hRK : R.comap (algebraMap K F) = O := by
    refine eq_of_le_of_lt_one hϖ₀ (fun o ho ↦ hR ⟨o, ho⟩) ?_
    rw [CentreGerms.valuation_comap_lt_one_iff']
    exact hRϖ
  have hRK' : (R.comap φ).comap (algebraMap K K') = O := by
    rw [ValuationSubring.comap_comap, hφ, hRK]
  have := CrossingAux.eq_of_comap_eq_dvr O hRK' h'
  have hmem : (o' : K') ∈ R.comap φ := by rw [this]; exact o'.2
  exact hmem

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [FiniteDimensional K K'] in
/-- **The base of the target, seen from `j'`, is the algebra map on `O`.** -/
theorem baseHom_target {K₁ L₁ L₂ : Type u} [Field K₁] [Field L₁] [Field L₂] [Algebra K K₁]
    [Algebra K' L₂] [Algebra L₂ L₁] [Algebra K₁ L₁] [Algebra K L₁] [Algebra K L₂]
    [IsScalarTower K K₁ L₁] [IsScalarTower K K' L₂] [IsScalarTower K L₂ L₁]
    {O₁ : ValuationSubring K₁} (h₁ : O₁.comap (algebraMap K K₁) = O) [Algebra O₁ L₁]
    [IsScalarTower O₁ K₁ L₁] {x : L₁} {c : TemperedFundamentalGroups.ModelCode O₁}
    {c' : TemperedFundamentalGroups.ModelCode O'} {ψ : c.scheme ⟶ c'.scheme}
    {j : Spec (CommRingCat.of L₁) ⟶ c.scheme} {j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme}
    (hW : IsWModel O₁ L₁ x c j)
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j')
    (hψO : ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K').restrict O O'
      (fun y hy ↦ by rw [← h'] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy)))) (o : O) :
    baseHom c' j' ((algebraMap K K').restrict O O' (fun y hy ↦ by rw [← h'] at hy; exact hy) o) =
      algebraMap K L₂ o := by
  have e := whisker_eq j hψO
  rw [← Category.assoc j ψ, hj, Category.assoc, ← Category.assoc j' c'.toSpec, toSpec_comp,
    ← Category.assoc j c.toSpec, toSpec_comp, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp] at e
  have e2 := congrArg (fun φ ↦ φ.hom o) (Spec.map_injective e)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e2
  rw [baseHom_eq_of_isWModel hW] at e2
  apply (algebraMap L₂ L₁).injective
  rw [e2, ← IsScalarTower.algebraMap_apply K L₂ L₁, IsScalarTower.algebraMap_apply O₁ K₁ L₁]
  change algebraMap K₁ L₁ (algebraMap K K₁ o) = _
  rw [← IsScalarTower.algebraMap_apply]

end TemperedFundamentalGroups.SemistableReduction.CrossingGlue
